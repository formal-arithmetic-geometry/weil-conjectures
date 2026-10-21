## What changed

Proved `CategoryTheory.ConstantCompletion.quotientPresentation_exists` for both
coefficient rings, including the full normalized unit law. All existing public signatures,
public definition bodies and target statements remain unchanged.

The reduction tower is derived using the existing K-flat resolutions and resolving-class
theorem. Evaluation reduces quasi-isomorphism preservation to scalar extension on K-flat
complexes and exact restriction. The unit comes from the ordinary constant-tower/limit
adjunction unit, descended by the universal left-derived lift, and a second lift of
the strict reduction unit. The limit projections identify its ordinary normalization with the specified ordinary unit.

Added six private proved helpers: `resolving_derived_cochain`,
`change_preserves_kFlat_quasiIso`, `derived_tower_unit`, `module_kFlat_resolution`,
`reductionTower_preserves_kFlat_quasiIso`, and `derived_tower_presentation`.
The private `towerOrdinaryUnit` chooses the morphism specified by the fully proved
unique projection formula. Proof irrelevance identifies its specialization with the
existing `ordinaryUnit`; this adds no arbitrary choice or postponed proof.
Moved the existing private Kan-extension helpers before their new uses,
with their proofs unchanged. Added two private proof imports and updated the existing
node's proof, proof dependencies and proof origin.

A local irreducibility attribute keeps `completed` behind its named maps. Two existing
projection proofs explicitly unfold it, and `completedMap` temporarily restores its
original transparency. Local irreducibility also keeps the four chosen universal records behind their field
APIs: `derivedExtension`, `strictLimit`, `quotientPresentation`, and `derivedPull`.
Inside the final theorem only, `HasDerivedCategory.standard` is locally irreducible
and type equality respects transparency. No consumer attributes change. Diagnostic files are outside the
delivery source tree; no profiling instrumentation or diagnostic omissions remain.

The final specialization supplies `M := Mod O` explicitly to avoid re-inferring the
coefficient category through the concrete reduction-tower functor.

Validation: the complete submitted module compiled through `lcompile.py` in
50.0 seconds. The final delivery runs its compiler, axiom and packet checks.

Change record: `coord/changes/Q1-constant-completion-derived-tower.md`.

## Proved and sorry left

Closed 1 of the original 15 holes:

- `CategoryTheory.ConstantCompletion.quotientPresentation_exists`.

Added 0 holes and split off 0 statements. The following 14 existing named holes are
unchanged. All names are in `CategoryTheory.ConstantCompletion` and attached to
`lem-weil-pbc-constant-completion-equivalence`:

- `flat_and_quotients`.
- `finiteDerivedComparison`.
- `koszul_quotient_reflector`.
- `completion_restriction`.
- `derivedReductionTowerComparison`.
- `inverseImageData_exists`.
- `ordinaryPullComparison_existsUnique`.
- `derivedPullComparison_existsUnique`.
- `ordinaryFinitePull_existsUnique`.
- `finitePull_existsUnique`.
- `completedFinitePull_existsUnique`.
- `pullbackTowerComparison_existsUnique`.
- `pullback_composition`.
- `pullback_identity`.

The proof uses existing library theorems. Their transitive axiom closures and the other
fourteen completion and pullback results are not claimed to be sorry-free. This is a
partial delivery under the brief's rule for a module with several holes.

## No longer needed

Removed three redundant private proof imports:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.

Retained imports supply their required APIs. No module is withdrawn. The proved quotient
presentation needs only a single-complex K-flat resolution, using the existing
independent-coefficient resolution and its proved equivalence with K-flatness; it does
not need diagram replacements. `lem-weil-pbc-diagram-kflat-replacements` remains in the
node because other unfinished steps still cite it. No dependency needed by any of the
fourteen remaining holes has been pruned. Each added proof import supplies a used API.

The unit needs only the ordinary adjunction unit, constructed degreewise on complexes;
no complex adjunction or derived-adjunction API is needed. In particular, the proof does
not import `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction` or
`Mathlib.CategoryTheory.Functor.Derived.Adjunction`.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or target repair. The quotient-presentation part of step 3 is now
proved; the finite derived comparisons remain pending. Its unit can be obtained directly
from the constant-tower/limit adjunction and Kan-extension universality, without choosing
separate representatives at every tower coordinate.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
