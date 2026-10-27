# AlgebraicGeometry.Etale.projectiveLineDiagonalAlpha

## Reason

The component file's original supported-map composite typechecks very slowly
when the category structure proofs captured by the diagonal alpha are inferred
again rather than shared with its named ordinary derived objects. A small section
around this declaration reuses the existing library HasSheafify,
IsGrothendieckAbelian, homology, zero-object and small-localized-Hom proofs.
No written signature, attribute, formula or public import changes. Only this
last declaration of the module is elaborated in the new local instance context.
The module is unclaimed. Targets using this representation are reopened for
review of the unchanged maps. This makes no assumption or new choice.

## Old

```lean
def projectiveLineDiagonalAlpha (A : Type (u + 1)) [CommRing A]
    (S : Scheme.{u}) (a : Bool) :
    ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).obj
        ((ordinaryFinitePushforward A (pullback.diagonal (ProjectiveLine S ↘ S))).obj
          (ordinaryFiniteUnit A (ProjectiveLine S))) :=
  supportedDerivedUnit A (projectiveLineDiagonalProjection S a) ≫
    (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map
      (supportedDerivedUnit A (pullback.diagonal (ProjectiveLine S ↘ S)))
```

## New

```lean
section
-- Reuse the canonical structures already captured by the ordinary module class map.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

set_option linter.auxLemma false in
attribute [local instance 100000] ordinaryFiniteClass._proof_1 ordinaryFiniteClass._proof_2
  ordinaryFiniteClass._proof_3

/-- The canonical source identification A_P → Rp_* RDelta_* A_P. The two units
compose to the identity-map unit because p Delta = id, so this is the canonical
derived-composition identification, in the direction required by the integral.
Source: blueprint lem-amb-p1-diagonal-integrals, alpha_a and proof steps 3 and 5
(blueprint: lem-amb-p1-diagonal-integrals). -/
def projectiveLineDiagonalAlpha (A : Type (u + 1)) [CommRing A]
    (S : Scheme.{u}) (a : Bool) :
    ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).obj
        ((ordinaryFinitePushforward A (pullback.diagonal (ProjectiveLine S ↘ S))).obj
          (ordinaryFiniteUnit A (ProjectiveLine S))) :=
  supportedDerivedUnit A (projectiveLineDiagonalProjection S a) ≫
    (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map
      (supportedDerivedUnit A (pullback.diagonal (ProjectiveLine S ↘ S)))
end
```

## Users

The declaration-use scan of tools/downstream.py --uses projectiveLineDiagonalAlpha
lists precisely these ten modules. Each sees the original composite of the
constant unit with direct image of the diagonal constant unit. All instance
proofs are existing proofs of the same propositions, and their computational
category structures remain the canonical ones. The repaired production pass compiled this module and the complete component proof. The full consumer validation is documented in report.md.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals` | unclaimed | Same written unit composite and canonical category structures; same mathematical statement. |
| `Sheaf.AlgebraicGeometry.FiniteP1DiagonalAlpha` | unclaimed | Same written unit composite and canonical category structures; same mathematical statement. |
| `Sheaf.AlgebraicGeometry.FiniteP1DiagonalKummerComponentFormula` | F1 | Same written unit composite and canonical category structures; same mathematical statement. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalChernComponents` | unclaimed | Same written unit composite and canonical category structures; same mathematical statement. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalData` | unclaimed | Same written unit composite and canonical category structures; same mathematical statement. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals` | unclaimed | Same written unit composite and canonical category structures; same mathematical statement. |
| `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalTraceCalculation` | unclaimed | Same written unit composite and canonical category structures; same mathematical statement. |
| `Sheaf.AlgebraicGeometry.SfP1IntegralSectionComparison` | U3 | Same written unit composite and canonical category structures; same mathematical statement. |
| `Sheaf.AlgebraicGeometry.SfP1IntegralTransport` | unclaimed | Same written unit composite and canonical category structures; same mathematical statement. |
| `Sheaf.Paper.TowerP1KernelScalarData` | unclaimed | Same written unit composite and canonical category structures; same mathematical statement. |

## Status

landed 20261026T222636-L-676965 2026-10-26 (merge of deliver/F1/Sheaf.AlgebraicGeometry.FiniteP1DiagonalKummerComponentFormula)
