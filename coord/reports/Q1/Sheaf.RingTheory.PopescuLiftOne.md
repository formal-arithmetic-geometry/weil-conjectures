## What changed

Proved `Algebra.popescuEighthPowerLifting_one` in
`Sheaf.RingTheory.PopescuLiftOne` without changing its signature or visibility.
The proof follows the one-element case of Stacks 07F8 and uses the existing
`Algebra.popescu_desingularize_lifting_apply` (07F0). Four proved private helpers
handle principal annihilators, smoothness after inverting the parameter, the
singular ideal under quotient base change, and the universe of the intermediate
algebra. The final ideal inclusions and noncontainment are proved using ideal
map/comap operations. No new public statements or definitions were introduced.

Added proof-only imports `Sheaf.RingTheory.PopescuIdealCompEquiv`,
`Sheaf.RingTheory.SingularIdealMapEquiv`,
`Mathlib.RingTheory.TensorProduct.Quotient`, and
`Mathlib.RingTheory.Localization.BaseChange`. Updated the existing node's proof,
proof dependencies, and proof origin to match the Lean argument.

Read the source's `lemma-lift-solution` and its r = 1 proof in the locally available
Stacks checkout (the project's own literature copy is absent on this machine).
The unit `sk-thm-p1` has no realized step at this node; the unit route is unchanged.

## Proved and sorry left

Closed one hole: `Algebra.popescuEighthPowerLifting_one`
(`lem-weil-pbc-popescu-lift-one`). All four private helpers are proved.
There are no `sorry`s left in the delivered module and no holes added elsewhere:
this is a proof from existing declarations, not a decomposition into new holes.

The proof still depends on the existing holed theorem
`Algebra.popescu_desingularize_lifting_apply`
(`lem-weil-pbc-popescu-desingularize-lifting-apply`), which is unchanged and remains
work for its holder. Thus closing this module does not claim that the full theorem
is free of transitive `sorry` dependencies.

Validation: the prescribed single-file compiler accepts the module without errors
or warnings. All lines meet the 100-character limit. Both added Sheaf proof imports
pass `tools/import_direction.py may`. The required delivery dry run is the final gate.

## No longer needed

No existing imports were removed, and every added import is used by a proof.
The planned node `lem-weil-pbc-polynomial-ring-smooth` is no longer needed by this
module's proof: Mathlib's `Smooth.of_isLocalization_Away` directly establishes
smoothness of the base localization. It was a Mathlib leaf, not an imported Sheaf
module, so no Sheaf or WeilConjectures module is claimed pruned.
All other original proof dependencies are retained. The finite-presentation
notion, induction notion, and the two existing algebra-equivalence lemmas are
explicitly recorded as dependencies of the implemented steps.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable signature was found. The recorded dependencies
sufficed. The original plan used polynomial-ring smoothness to prove smoothness
of the base localization; Mathlib already gives the needed localization theorem
directly. The noncontainment step is implemented by contradiction and ideal maps,
which avoids choosing a lift outside the reduced prime while proving the same
claim.

The shorter-route searches were performed with the prescribed leanfinder,
loogle, and grep wrappers, and with local searches in both library roots and
Mathlib. Lean Finder returned formal-smooth lifting lemmas, which require stronger
hypotheses and do not solve this Popescu resolution statement. Loogle's
annihilator/span search gave an unrelated minimum-polynomial lemma. Mathlib grep
found only category-theoretic Gabriel–Popescu results. Local source searches found
the existing singular-ideal equivalence lemmas and the finite polynomial
presentation and base-change APIs used above.

## Second reading by Q1

1. **Interface and accidental changes.** Compared the delivered Lean module and DAG node with the repository versions. The theorem signature and visibility are unchanged; the node changes only the proof route, proof dependencies, and proof origin. Verdict: pass.

2. **Proof and trust basis.** Compiled `Sheaf.RingTheory.PopescuLiftOne` with the prescribed `lcompile.py`; it compiles without errors or warnings. The module has no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`, and the proof uses only existing declarations plus private proved helpers. Verdict: pass.

3. **Statements and dependencies.** No new public statements or definitions were added. The private helpers are strictly intermediate parts of the Stacks 07F8 argument: annihilator reduction, localization smoothness, quotient base change of singular ideals, and universe resizing. Their uses match the recorded node proof dependencies. Verdict: pass.

4. **Shortest route and pruning.** Checked the imports and proof against the available Sheaf and Mathlib declarations. The direct Mathlib localization smoothness result makes the planned polynomial-ring-smoothness leaf unnecessary; all remaining added imports are used. The reduced-resolution route and the `sk-thm-p1` unit route are preserved. Verdict: pass.

5. **DAG and report agreement.** The node proof, `proof_deps`, and `proof_origin` describe the delivered proof, including the quotient-base-change and finite-presentation-equivalence steps. No new nodes or split-off holes were introduced. Verdict: pass.

Changed during second reading: appended this review section only; no Lean or DAG repairs were needed.
