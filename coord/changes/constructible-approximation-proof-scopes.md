# AlgebraicGeometry.IsCurve.assertions_of_constructible_approximation

## Reason

The proof uses limit/colimit names and the existing etale inverse-image notation. The
preflight conservatively classifies changes to namespace openings as an interface change.
This record documents their actual effect: they resolve names while elaborating this module;
no existing declaration signature or definition changes. All added imports in this existing
module are proof-only. No target statement or definition it uses changes.

## Old

```lean
open CategoryTheory
namespace AlgebraicGeometry
```

The exact original theorem signature is:

```lean
theorem IsCurve.assertions_of_constructible_approximation
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    (H : ∀ (G : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      [Scheme.IsConstructibleSheaf G], IsCurve.Assertions Λ f G)
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Scheme.IsTorsionSheaf F] :
    IsCurve.Assertions Λ f F
```

## New

```lean
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

open Etale
```

The theorem retains exactly the Old signature. Its proof now uses only proved private
helpers and the new proved presentation theorem. No notation, instance or attribute is
introduced. No public definition refers to a private helper. These namespace openings do
not change how an importing module resolves its names.

## Users

The read-only `tools/downstream.py` query with
`--uses AlgebraicGeometry.IsCurve.assertions_of_constructible_approximation` reports the
following two textual users. No module needs adaptation. The 126 modules in the transitive
import closure see the same public statement and original public imports; the new imports
are proof-only.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleApproximationAssertions | U2 | Own proof updated; original signature unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | not determined from this snapshot; not edited | Its constructible-reduction application has identical arguments and conclusion. |

## Status

landed 20261012T060757-L-2916829 2026-10-12 (merge of deliver/U2/Sheaf.AlgebraicGeometry.Curve.ConstructibleApproximationAssertions)
