-- Run: lake env lean Audit/statement_types.lean > Audit/statement_types.txt
-- Prints, with `pp.all`, the type of every declaration of the frozen namespaces `LogGasPaper`
-- and `LogGasChallenge` (and the value of every definition there), then the types of the
-- milestone declarations and of the `LogGas.Spec` / `LogGas.Torus` definitions they are stated
-- with. Theorem proofs are never printed, so the output must stay byte-identical while proofs
-- change (frozen-statement check, see Audit/FREEZE.md and Audit/check_statement_types.py).
import PaperSolution
import Solution

open Lean Elab Command Meta

/-- Milestone declarations whose *types* are frozen (Audit/statement_map.md, Block 2). -/
def milestoneNames : List Name := [
  `LogGasPaper.main, `LogGasPaper.kernel_exists,
  `LogGasChallenge.principal, `LogGasChallenge.bulk,
  `LogGas.Spec.principal, `LogGas.Spec.bulk,
  `LogGas.Paper.paper_main, `LogGas.Paper.kernel_exists, `LogGas.Paper.paperTheorem,
  `LogGas.Paper.logKernelExists,
  `LogGas.Main.theorem11, `LogGas.Main.holder_split, `LogGas.Main.bulk_hypothesis,
  `LogGas.Main.parameter_choice,
  `LogGas.Bulk.lemma41, `LogGas.Bulk.histogram_box, `LogGas.Bulk.empEnergy_split,
  `LogGas.Bulk.empEnergy_le, `LogGas.Bulk.dual_log_hls, `LogGas.Bulk.ell_hist,
  `LogGas.Bulk.coarse_exp_bound, `LogGas.Bulk.rJ_bound, `LogGas.Bulk.W_le_coarse,
  `LogGas.Singular.lemma51, `LogGas.BadEvent.bad_gibbs_bound,
  `LogGas.Decoupling.exp_bound, `LogGas.Grouped.grouped_exp_bound,
  `LogGas.Torus.grid, `LogGas.Physical.singular_instance, `LogGas.Physical.log_exp_integrable,
  -- definitions the milestone statements are expressed with
  `LogGas.Torus.T, `LogGas.Torus.unif, `LogGas.Torus.radius, `LogGas.Fourier.IsLogKernel,
  `LogGas.Spec.energy, `LogGas.Spec.partition, `LogGas.Spec.cutoff, `LogGas.Spec.boundedH1,
  `LogGas.Spec.paperLogHLS, `LogGas.Spec.principalStatement, `LogGas.Spec.bulkStatement,
  `LogGas.Spec.quadratic, `LogGas.Spec.positive, `LogGas.Spec.entropy, `LogGas.Spec.density]

elab "#print_statement_types" : command => do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (nm, _) in env.constants.toList do
    if ((`LogGasPaper).isPrefixOf nm || (`LogGasChallenge).isPrefixOf nm) && !nm.isInternalDetail then
      names := names.push nm
  for nm in milestoneNames do
    if env.contains nm then names := names.push nm
    else logWarning m!"milestone declaration missing: {nm}"
  names := (names.qsort (fun a b => a.toString < b.toString)).toList.eraseDups.toArray
  let mut out : Array String := #[]
  for nm in names do
    let some ci := env.find? nm | continue
    let ty ← liftTermElabM <| withOptions (fun o => (o.setBool `pp.all true).setBool `pp.proofs false) <| ppExpr ci.type
    let mut s := s!"{nm} : {ty}"
    -- Values are printed only for the frozen namespaces (definitions there are the claim);
    -- library definitions are compared by type and by `Audit/Replay` export comparison.
    if (`LogGasPaper).isPrefixOf nm || (`LogGasChallenge).isPrefixOf nm then
      if let .defnInfo d := ci then
        let v ← liftTermElabM <| withOptions (fun o => (o.setBool `pp.all true).setBool `pp.proofs false) <| ppExpr d.value
        s := s ++ s!"\n  := {v}"
    out := out.push s
  IO.println (String.intercalate "\n" out.toList)

#print_statement_types
