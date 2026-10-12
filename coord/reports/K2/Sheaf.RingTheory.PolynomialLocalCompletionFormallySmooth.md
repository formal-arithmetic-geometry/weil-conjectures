## What changed

Proved `Algebra.polynomial_local_completion_formallySmoothAdic` in
`Sheaf.RingTheory.PolynomialLocalCompletionFormallySmooth`, preserving its signature and
public imports. Added the proof-only import `Mathlib.RingTheory.Smooth.Basic`. Mathlib supplies discrete formal smoothness of the
polynomial localization; its square-zero lifting gives adic formal smoothness directly.
Finite generation of q maps to finite generation of qT. The existing completion theorem
then applies, and `Ideal.map_map` with `IsScalarTower.algebraMap_eq` identifies the final ideal.
Updated the item's DAG proof and dependency list accordingly. No definition or interface changed.

## Proved and sorry left

Closed the one original hole, `Algebra.polynomial_local_completion_formallySmoothAdic`
(node `lem-weil-pbc-polynomial-local-completion-formally-smooth`). No sorry remains in the
item and none was added. This is a proof, not a decomposition. Local compilation succeeds
without warnings; a temporary `#print axioms` check reports only `propext`, `Classical.choice`,
and `Quot.sound`, and the probe has been removed.

## No longer needed

Pruned proof dependency `lem-weil-pbc-localization-noetherian`: the argument uses
`Ideal.FG.map` on q rather than Noetherianity of the localization. Its Mathlib declaration
`IsLocalization.isNoetherianRing` and module `Mathlib.RingTheory.Localization.Submodule`
are not needed by this proof directly. The second reader removed the redundant added import
`Mathlib.RingTheory.Polynomial.Basic` (already available transitively).
No original import was removed, and no Sheaf module
is newly pruned by this delivery. The remaining discrete polynomial/localization lifting,
finite-type polynomial Noetherianity, adic definition and completion nodes are retained.
The item's node is not one of the unit's own realized statements or steps; the unit route stays.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement or source was found. The DAG's localization Noetherian step is
unnecessary because finite generation is preserved by ideal extension. LeanFinder and
Loogle found Mathlib's `Algebra.FormallySmooth.instLocalization`; local source searches
confirmed the polynomial instance, square-zero lifting, `Ideal.FG.map`, and `Ideal.map_map`.
The existing completion theorem is already proved, so no new intermediate theory was needed.


## Second reading by K2

1. Compared the sole delivered Lean module and node with their repository versions.
   Verdict: the existing theorem signature is byte-for-byte unchanged; there are no
   definition changes, new declarations, change records or adaptations. All public
   imports retain their original visibility; the added Smooth.Basic import is proof-only.
2. Compiled the module with lcompile.py and compiled a scratch copy with `#print axioms
   Algebra.polynomial_local_completion_formallySmoothAdic`. Verdict: no errors or warnings,
   no sorry or forbidden declarations; only propext, Classical.choice and Quot.sound.
   Read FormallySmoothAdic and the proved completion theorem, and checked the Mathlib
   polynomial/localization instances, square-zero lift and ideal-map identities.
3. No statement was split off and no hole was added. Verdict: there is no restatement,
   hollow definition or arbitrary witness selected from an unproved existence theorem.
   The lifting existential is supplied by a proved Mathlib theorem. The statement covers
   zero prime ideals over fields as well as nonmaximal primes; no extra maximality or
   nonzero-ideal assumption enters the proof.
4. Checked the top-down reduction and searched existing polynomial formal smoothness and
   adic-completion declarations in Mathlib and both library roots. Verdict: the existing
   completion theorem is the direct route; no intermediate lemma is needed. Removing the
   added Polynomial.Basic import still compiles with the same three axioms, confirming
   redundancy. The report lists the sole old dependency no longer used, localization
   Noetherianity. Read dag/units/sk-thm-p1.json: this helper is absent from its realized
   statement and steps, and neither the unit route nor its realizations are changed.
5. Compared the node proof, proof_deps and proof_origin with the actual Lean proof and
   dependency declarations. Verdict: the five steps match the polynomial/localization
   instances, unrestricted lift, finite generation by ideal extension, and completion;
   proof_deps is exactly the union of the steps' uses. Statement and statement-dependency
   fields are unchanged; no new nodes require checking.

Changed only the redundant added Polynomial.Basic import, the stale proof-docstring step
that still invoked localization Noetherianity, and this report. The proof term is unchanged.
Closed one original hole and added zero: proved 1 of 1, zero split off.
