# AlgebraicGeometry.Scheme.adicResidue_isIso_of_residue proof context

## Reason

The conservative command-interface check sees the additional namespace opening and
scoped instance-search adjustments used by the proof and its private helpers.
Record their exact scope for review. No existing signature, visibility, definition,
attribute registration, public import or target meaning changes. No consumer is adapted.
All new helpers are proved private theorems and occur only in theorem proofs.

## Old

The original context and declaration were:

```lean
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme

theorem adicResidue_isIso_of_residue
    (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) (U : coefficientProEtaleSiteModel.{u, v} X)
    (T M : AdicResidueLocalDerived.{u, v} X J U)
    (_hT : CategoryTheory.ConstantCompletion.IsComplete
      (adicResidueLocalProjection.{u, v} X J U 0) T)
    (_hM : CategoryTheory.ConstantCompletion.IsComplete
      (adicResidueLocalProjection.{u, v} X J U 0) M)
    (f : T ⟶ M) (_hf : IsIso ((adicResidueLocalReduction.{u, v} X J U 0).map f)) : IsIso f := by
  sorry
```

## New

The declaration signature above is unchanged. Its proof uses three proved private
helpers and the existing normalized complete-reduction cone plus the new successor
coefficient lemma. The additional namespace opening is:

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
```

Each of the three private helpers and the assigned theorem is individually preceded by:

```lean
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
```

The `in` scopes the removal to that declaration. It is not a global change to instance
search or an exported attribute. The existing complete-cone and Hom-section modules
use the same instance-search adjustment. The generic helpers explicitly install the
standard derived-category instances, and internal-Hom exactness supplies its own shifts.
The successor module also scopes the adjustment to its sole theorem.

## Users

Read-only `tools/downstream.py Sheaf.Paper.AdicCompleteResidueConservative --uses
AlgebraicGeometry.Scheme.adicResidue_isIso_of_residue` found the following two modules
using the name. Its transitive importer inventory contains 2612 modules; no public
imports or global elaboration environment changes, so none requires adaptation.
The direct external consumer's call at line 328 uses exactly the same arguments.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicCompleteResidueConservative | Y2 | Replace theorem proof; add private proved helpers and declaration-scoped proof context. |
| Sheaf.Paper.AdicResidueLissePerfectLift | unclaimed | Same theorem signature and call; no adaptation. |

## Status

landed 20261025T203737-L-2850606 2026-10-25 (merge of deliver/Y2/Sheaf.Paper.AdicCompleteResidueConservative)
