import Lean

/-! Independent environment inspection; never imported by a mathematical target. -/
open Lean Elab Command
namespace LogGasAudit
/- Ignore binder display names and elaborator metadata only. Constants, levels,
types, terms and de Bruijn variables are retained; no mathematical unfolding or
proof erasure is used to force a comparison pass. -/
private partial def canonical : Expr → Expr
  | .app f a => .app (canonical f) (canonical a)
  | .lam _ t b bi => .lam .anonymous (canonical t) (canonical b) bi
  | .forallE _ t b bi => .forallE .anonymous (canonical t) (canonical b) bi
  | .letE _ t v b nonDep => .letE .anonymous (canonical t) (canonical v) (canonical b) nonDep
  | .mdata _ e => canonical e
  | .proj n i e => .proj n i (canonical e)
  | e => e

def audit (target : Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut count := 0
  let mut declarations : Array Json := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let provider := env.header.moduleNames[idx]!
    unless provider == target || ((target == `Solution || target == `PaperSolution) && (`LogGas).isPrefixOf provider) do
      continue
    count := count + 1
    if ci.isUnsafe then throwError "Unsafe declaration: {n}"
    if let .axiomInfo _ := ci then throwError "Custom axiom: {n}"
    let axioms ← collectAxioms n
    for ax in axioms do
      unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
        throwError "Forbidden axiom {ax} in {n}"
    if (`LogGasChallenge).isPrefixOf n || (`LogGasPaper).isPrefixOf n then
      -- Compare specification definitions. Additional proved inhabitants belong
      -- only to the solution and are checked separately against the target.
      unless ci matches .defnInfo _ do continue
      declarations := declarations.push <| Json.mkObj [
        ("name", toJson n.toString), ("type", toJson (toString (canonical ci.type))),
        ("body", match ci with
          | .defnInfo d => toJson (toString (canonical d.value))
          | _ => Json.null)]
  let modules := env.header.moduleNames.map Name.toString
  if target == `Challenge || target == `PaperChallenge then
    for n in env.header.moduleNames do
      if (`LogGas).isPrefixOf n || n == `Solution || n == `PaperSolution then
        throwError "Project proof imported into Challenge: {n}"
  if target == `Solution || target == `PaperSolution then
    if env.header.moduleNames.contains `Challenge || env.header.moduleNames.contains `PaperChallenge then
      throwError "Challenge imported into Solution"
  logInfo m!"VERIFICATION_JSON {Json.compress <| Json.mkObj [
    ("target", toJson target.toString), ("count", toJson count),
    ("modules", toJson modules), ("definitions", toJson declarations)]}"
end LogGasAudit
