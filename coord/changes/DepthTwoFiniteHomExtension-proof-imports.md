# AlgebraicGeometry.Scheme.exists_hom_of_finite_depth_two

## Reason

The delivery tool classifies the added `open Opposite TopologicalSpace` command as changing what other modules see and requires this record. The command is inside `section PrivateHelpers`, which ends before the existing theorem. All added imports are proof-only; all added helpers are private. The actual public interface, theorem signature, and definitions used by targets are unchanged. No target review is reopened and no adaptation is required.

## Old

```lean
theorem exists_hom_of_finite_depth_two
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    {F E : Scheme.{u}} (r : F ⟶ L) (p : E ⟶ L) [IsFinite r] [IsAffineHom p]
    (hF : ∀ z : F, r z ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := F.presheaf.stalk z) (F.presheaf.stalk z))
    (a : (r ⁻¹ᵁ U).toScheme ⟶ (p ⁻¹ᵁ U).toScheme)
    (ha : a ≫ p ∣_ U = r ∣_ U) :
    ∃ f : F ⟶ E, f ≫ p = r ∧ (r ⁻¹ᵁ U).ι ≫ f = a ≫ (p ⁻¹ᵁ U).ι
```

The surrounding namespace began with:

```lean
open CategoryTheory
namespace AlgebraicGeometry.Scheme
```

## New

```lean
theorem exists_hom_of_finite_depth_two
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    {F E : Scheme.{u}} (r : F ⟶ L) (p : E ⟶ L) [IsFinite r] [IsAffineHom p]
    (hF : ∀ z : F, r z ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := F.presheaf.stalk z) (F.presheaf.stalk z))
    (a : (r ⁻¹ᵁ U).toScheme ⟶ (p ⁻¹ᵁ U).toScheme)
    (ha : a ≫ p ∣_ U = r ∣_ U) :
    ∃ f : F ⟶ E, f ≫ p = r ∧ (r ⁻¹ᵁ U).ι ≫ f = a ≫ (p ⁻¹ᵁ U).ι
```

The helpers are scoped as follows:

```lean
open CategoryTheory
namespace AlgebraicGeometry.Scheme

section PrivateHelpers

open Opposite TopologicalSpace
```

`end PrivateHelpers` precedes the unchanged existing theorem docstring. Proof-only imports provide Hartogs restriction, affine local algebra maps, and quasi-coherence of the unit module.

## Users

`tools/downstream.py ... --uses exists_hom_of_finite_depth_two` lists these declaration users (122 transitive importing modules inherit the identical interface). No downstream file is delivered or adapted; the declaration's elaborated type and its signature bytes are unchanged.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Morphisms.DepthTwoFiniteHomExtension | H2 | proof closed; signature unchanged |
| Sheaf.AlgebraicGeometry.Morphisms.DepthTwoFiniteExtensionUniqueness | unclaimed in local claims snapshot | no interface effect; no adaptation |

## Status

landed 20261013T121510-L-3529258 2026-10-13 (merge of deliver/H2/Sheaf.AlgebraicGeometry.Morphisms.DepthTwoFiniteHomExtension)
