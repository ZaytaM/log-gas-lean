#!/usr/bin/env python3 -I
"""Comparator for lean4export NDJSON (format 3.1.x) challenge vs. solution exports.

For each --target THEOREM:PROP it checks that
  1. THEOREM is a `thm` in the solution export whose type is the constant PROP (up to levels),
  2. the definition of PROP in the solution export is structurally identical to its definition in
     the challenge export (alpha-equivalent terms, independent of back-reference numbering),
  3. every constant reachable from PROP's type and value through definition bodies (stopping at
     Mathlib/core, i.e. names outside the project namespaces) is identical in both exports,
  4. the axioms reachable from THEOREM's proof in the solution export are within --permitted-axioms.
Exit 0 iff all checks pass; a JSON report is written with --report.

Format notes (lean4export format_ndjson.md / Export.lean, version 3.1.0): names `{"str":{"pre":i,"str":s},"in":k}`
/ `{"num":{"pre":i,"i":n},"in":k}` with index 0 = anonymous; levels `succ|max|imax|param` with `"il"`,
index 0 = zero; exprs `bvar|sort|const|app|lam|forallE|letE|proj|natVal|strVal|mdata` with `"ie"`;
declarations `axiom|def|opaque|thm|quot|inductive`. Indices are per kind, dense, never forward.
"""
import argparse, json, sys
from functools import lru_cache

PROJECT_PREFIXES = ("LogGasPaper.", "LogGasChallenge.", "LogGas.")


class Export:
    def __init__(self, path):
        self.names = {0: ()}          # index -> tuple of components
        self.levels = {0: ("zero",)}
        self.exprs = {}
        self.decls = {}               # qualified name string -> ("thm"|"def"|..., record)
        self.meta = None
        with open(path, encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                o = json.loads(line)
                if "meta" in o:
                    self.meta = o["meta"]; continue
                if "in" in o:
                    k = o["in"]
                    if "str" in o: self.names[k] = self.names[o["str"]["pre"]] + (o["str"]["str"],)
                    else: self.names[k] = self.names[o["num"]["pre"]] + (int(o["num"]["i"]),)
                elif "il" in o:
                    k = o["il"]
                    for tag in ("succ", "max", "imax", "param"):
                        if tag in o: self.levels[k] = (tag, o[tag]); break
                elif "ie" in o:
                    self.exprs[o["ie"]] = o
                else:
                    (kind, rec), = o.items()
                    if kind == "inductive":
                        for sub in ("types", "ctors", "recs"):
                            for r in rec[sub]:
                                self.decls[self.qname(r["name"])] = (sub[:-1], r)
                    else:
                        self.decls[self.qname(rec["name"])] = (kind, rec)
        version = (self.meta or {}).get("format", {}).get("version", "?")
        if not version.startswith("3.1"):
            raise SystemExit(f"{path}: unsupported export format version {version}")

    def qname(self, idx):
        return ".".join(str(c) for c in self.names[idx])

    # --- canonical (index-free) forms -------------------------------------------------------
    def level(self, k):
        l = self.levels[k]
        if l[0] == "zero": return ("zero",)
        if l[0] == "param": return ("param", self.qname(l[1]))
        if l[0] == "succ": return ("succ", self.level(l[1]))
        return (l[0], self.level(l[1][0]), self.level(l[1][1]))

    def expr(self, k, memo):
        if k in memo: return memo[k]
        e = self.exprs[k]
        if "bvar" in e: r = ("bvar", e["bvar"])
        elif "sort" in e: r = ("sort", self.level(e["sort"]))
        elif "const" in e: r = ("const", self.qname(e["const"]["name"]), tuple(self.level(u) for u in e["const"]["us"]))
        elif "app" in e: r = ("app", self.expr(e["app"]["fn"], memo), self.expr(e["app"]["arg"], memo))
        elif "lam" in e or "forallE" in e:
            tag = "lam" if "lam" in e else "forallE"; b = e[tag]   # binder names are ignored (alpha-equivalence)
            r = (tag, b["binderInfo"], self.expr(b["type"], memo), self.expr(b["body"], memo))
        elif "letE" in e:
            b = e["letE"]; r = ("letE", self.expr(b["type"], memo), self.expr(b["value"], memo), self.expr(b["body"], memo))
        elif "proj" in e:
            b = e["proj"]; r = ("proj", self.qname(b["typeName"]), b["idx"], self.expr(b["struct"], memo))
        elif "natVal" in e: r = ("nat", str(e["natVal"]))
        elif "strVal" in e: r = ("str", e["strVal"])
        elif "mdata" in e: r = self.expr(e["mdata"]["expr"], memo)   # metadata is ignored
        else: raise SystemExit(f"unknown expr record {e}")
        memo[k] = r
        return r

    def consts_in(self, k, memo, acc):
        """Constant names referenced by expression k."""
        e = self.exprs[k]
        if k in memo: return
        memo.add(k)
        if "const" in e: acc.add(self.qname(e["const"]["name"]))
        for key in ("app", "lam", "forallE", "letE", "proj", "mdata"):
            if key in e:
                for sub in ("fn", "arg", "type", "body", "value", "struct", "expr"):
                    if sub in e[key] and isinstance(e[key][sub], int) and sub != "idx":
                        self.consts_in(e[key][sub], memo, acc)

    def decl_canon(self, name):
        kind, rec = self.decls[name]
        memo = {}
        parts = [kind, tuple(self.qname(n) for n in rec.get("levelParams", [])), self.expr(rec["type"], memo)]
        if kind in ("def", "opaque"):
            parts.append(self.expr(rec["value"], memo))
        if kind == "def":
            parts.append(json.dumps(rec.get("hints"), sort_keys=True)); parts.append(rec.get("safety"))
        if kind == "type":
            parts += [rec["numParams"], rec["numIndices"], tuple(self.qname(c) for c in rec["ctors"]), rec["isRec"]]
        if kind == "ctor":
            parts += [rec["cidx"], rec["numParams"], rec["numFields"]]
        if kind == "rec":
            parts += [rec["numParams"], rec["numIndices"], rec["numMotives"], rec["numMinors"], rec["k"],
                      tuple((self.qname(r["ctor"]), r["nfields"], self.expr(r["rhs"], memo)) for r in rec["rules"])]
        return tuple(parts)

    def deps(self, name, through_values=True):
        kind, rec = self.decls[name]
        acc, memo = set(), set()
        self.consts_in(rec["type"], memo, acc)
        if through_values and "value" in rec: self.consts_in(rec["value"], memo, acc)
        if kind == "rec":
            for r in rec["rules"]: self.consts_in(r["rhs"], memo, acc)
        return acc

    def closure(self, roots, project_only=True):
        """Transitive closure through types and definition bodies, stopping at non-project names."""
        seen, todo = set(), list(roots)
        while todo:
            n = todo.pop()
            if n in seen or n not in self.decls: continue
            seen.add(n)
            if project_only and not n.startswith(PROJECT_PREFIXES) and n not in roots: continue
            todo.extend(self.deps(n))
        return seen

    def axioms_of(self, root):
        seen, todo, ax = set(), [root], set()
        while todo:
            n = todo.pop()
            if n in seen or n not in self.decls: continue
            seen.add(n)
            if self.decls[n][0] == "axiom": ax.add(n)
            todo.extend(self.deps(n))
        return ax


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("challenge"); ap.add_argument("solution")
    ap.add_argument("--target", action="append", required=True, help="THEOREM:PROP (solution theorem name : challenge proposition constant)")
    ap.add_argument("--permitted-axioms", nargs="*", default=["propext", "Classical.choice", "Quot.sound"])
    ap.add_argument("--report")
    a = ap.parse_args()
    C, S = Export(a.challenge), Export(a.solution)
    report = {"challenge_meta": C.meta, "solution_meta": S.meta, "targets": {}, "ok": True}
    for t in a.target:
        thm, prop = t.split(":")
        r = {"checks": {}}
        kind = S.decls.get(thm, (None,))[0]
        r["checks"]["theorem_present_as_thm"] = kind == "thm"
        if kind == "thm":
            ty = S.expr(S.decls[thm][1]["type"], {})
            r["checks"]["theorem_type_is_prop_constant"] = ty[0] == "const" and ty[1] == prop
            bad = sorted(S.axioms_of(thm) - set(a.permitted_axioms))
            r["axioms"] = sorted(S.axioms_of(thm)); r["checks"]["axioms_permitted"] = not bad
            if bad: r["unpermitted_axioms"] = bad
        r["checks"]["prop_in_challenge"] = prop in C.decls
        r["checks"]["prop_in_solution"] = prop in S.decls
        if prop in C.decls and prop in S.decls:
            closure = sorted(C.closure({prop}))
            r["closure_size"] = len(closure)
            missing = [n for n in closure if n not in S.decls]
            differing = [n for n in closure if n in S.decls and C.decl_canon(n) != S.decl_canon(n)]
            r["checks"]["closure_present_in_solution"] = not missing
            r["checks"]["closure_identical"] = not differing
            if missing: r["missing_in_solution"] = missing
            if differing: r["differing"] = differing
        r["ok"] = all(r["checks"].values()) and len(r["checks"]) >= 6
        report["targets"][t] = r
        report["ok"] &= r["ok"]
        print(f"{t}: {'PASS' if r['ok'] else 'FAIL'} {json.dumps(r['checks'])}")
    if a.report:
        with open(a.report, "w") as f: json.dump(report, f, indent=2)
    print("COMPARATOR", "ACCEPTED" if report["ok"] else "REJECTED")
    sys.exit(0 if report["ok"] else 1)


if __name__ == "__main__":
    main()
