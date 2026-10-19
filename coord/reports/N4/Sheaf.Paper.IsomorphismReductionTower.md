## What changed

Proved two of the three original holes in
`lean/Sheaf/Paper/IsomorphismReductionTower.lean`, with all existing statements,
definitions, visibility and public imports unchanged.

`WeilConjectures.isoReductionCompletedMap_existsUnique` is proved by constructing
constant-coefficient naturality from the uniquely normalized constant maps. A private
extensionality lemma lifts ring-sheaf maps to commutative-ring sheaf maps and uses the
sheafification universal property. Conjugating by the inverse constant comparison
reduces naturality to constant sections. `NatTrans.ofOpSequence` then assembles the
comparison of the coefficient towers; the limit-preservation isomorphism followed by
`HasLimit.isoOfNatIso` gives the required isomorphism. Its projection equations follow
from the two standard projection lemmas, and joint monicity proves uniqueness.
This proves the existing node's step 1 without adding a dependency or changing its route.

`WeilConjectures.isoReductionMapQuasiIso` is proved by
`HomologicalComplex.quasiIso_map_of_preservesHomology`, using exactness already
provided by `isoSectionwiseModuleInverseImage_exact`. This realizes step 7 directly
through Mathlib instead of the redundant wrapper module.

Added only the proof import `Mathlib.CategoryTheory.Limits.Preserves.Limits`.
The private helpers are all proved. Final single-file compilation after import pruning
succeeded without warnings in 11.4 seconds. The resumed worker rechecked the
retained proofs against the current shared sources and compiled the module without
warnings in 7.7 seconds. The delivery tool supplies its independent
axiom probe and preflight checks.

## Proved and sorry left

Closed 2 of the 3 original holes:

- `WeilConjectures.isoReductionCompletedMap_existsUnique`.
- `WeilConjectures.isoReductionMapQuasiIso`.

Added holes: none. Split-offs: none. This is a partial proof delivery, not a decomposition.

The only remaining hole in the item is
`WeilConjectures.isomorphismReductionTower`, corresponding to
`lem-weil-isomorphism-derived-pullback-reduction-tower`. Its signature, proof docstring
and original `by sorry` body are unchanged. It still needs the sectionwise, independent-
universe scalar-extension comparison and the proof that its localization commutes with
the canonical resolution comparisons. In particular the general tensor comparison
recorded in `inverseImage_tensor_hom_iso` fixes the coefficient universe to `t+1`,
whereas this theorem requires `max u (t+1)` and the sectionwise model. No universe
restriction has been introduced to hide this remaining interface work.

## No longer needed

Removed the following direct proof imports; none is used by the two completed proofs
or by the existing definitions and statements, as checked by compiling their removal:

- `Sheaf.Paper.PurInverseImageTensorHom`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.QuasiIsoSaturatedTriangulated`.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`.
- `Sheaf.Paper.KFlatRingedToposPullback`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso`.
- `Sheaf.Paper.EtaleDerivedScalarTensor`.
- `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`.
- `Sheaf.CategoryTheory.RingedSiteModules`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
- `Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted`.

These are twelve direct-import removals only; eight remain reachable transitively
from this item. A read-only source import-closure comparison from `TargetsCheck.lean`
found that all twelve still occur through other target dependencies: no module leaves
the targets import closure in this delivery. No dependency node is declared globally
unnecessary: the unchanged, unfinished main theorem retains its recorded plan and may
need these tools
when its proof is completed. In particular no unit statement or unit proof step has
been bypassed. The existing node needs no route change: the implemented arguments
are exactly its steps 1 and 7, and steps 2--6 and 8--10 remain planned, unproved work.
No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement or mathematical route error was found. The direct application of
the tensor comparison named in step 2 requires additional interface work: the published
comparison uses the adjunction-defined inverse image and coefficient universe `t+1`,
while the item uses the sectionwise model and independent coefficient universe
`max u (t+1)`. The two completed proofs use the already generalized sectionwise
interface instead. Existing `sorry` dependencies were used as intended.

Several compile requests received no server answer and were retried; subsequent
compiles succeeded. The previous delivery attempt failed while preparing its temporary
worktree; the resumed worker retained its two completed proofs and re-ran the prescribed delivery
checks. No launcher script or shared repository file was modified.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
