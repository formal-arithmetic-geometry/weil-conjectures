/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
public import WeilConjectures.AlgebraicGeometry.NormalBundle
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace

/-!
# Vector-bundle purity

For a vector bundle `π : E ⟶ B` of constant rank `r` and `K ∈ D^b_{ctf}(B, Λ)`,
`Rπ^! K ≅ Lπ^* K (r)[2r]` (blueprint `cor-pur-vector-bundle-purity`, part of `sk-prop-an`).

## Implementation notes

Vector bundles are presented as normal bundles: the normal bundle
`N_{B/X} = Spec_B (Sym (I/I²))` (`AlgebraicGeometry.Scheme.Hom.normalBundle`) of a regular
closed immersion `i : B ⟶ X` of pure codimension `r` is a vector bundle of rank `r`, its conormal
sheaf `I/I²` being locally free of rank `r`. Conversely every vector bundle `E = Spec_B (Sym ℰ)`
is the normal bundle of its zero section `B ⟶ E`, which is a regular immersion of codimension
`r`. So the statements below cover exactly the vector bundles of rank `r`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_normalBundle`:
  `Rπ^! K ≅ Lπ^* K (r)[2r]`.
- `AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_normalBundle`: its case `K = Λ_B`,
  `ω_π ≅ Λ_E(r)[2r]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]

/-- Blueprint `cor-pur-vector-bundle-purity`: Vector-bundle purity

Let `π : E ⟶ B` be a vector bundle of constant rank `r` over a separated scheme of finite type
over a field, on which the exponent of `Λ` is invertible. For every `K ∈ D^b_{ctf}(B, Λ)` there
is an isomorphism

`Rπ^! K ≅ Lπ^* K (r)[2r]`.

The vector bundle is presented as the normal bundle `π : N_{B/X} ⟶ B` of a regular closed
immersion `i : B ⟶ X` of pure codimension `r`; every vector bundle of rank `r` is of this form
(see the implementation notes). In the blueprint the isomorphism is the adjoint of integration
against the trace of the bundle; that map is not constructed, so only the existence of the
isomorphism is recorded. -/
theorem nonempty_iso_rightDerivedUpperShriek_normalBundle [HasTateTwist.IsNormalized Λ]
    {k : Type u} [Field k] (r : ℕ) {B X : Scheme.{u}} (i : B ⟶ X) [IsRegularImmersion r i]
    (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB]
    [HasCompactification i.normalBundleProj] [HasInvertibleExponent Λ B]
    (K : _root_.DerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ B K) :
    Nonempty ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) i.normalBundleProj).obj K ≅
      (twistShift Λ i.normalBundle r).obj
        ((L((i.normalBundleProj)^*[ModuleCat.{u + 1} Λ])).obj K)) :=
  sorry

/-- Blueprint `cor-pur-vector-bundle-purity`: Vector-bundle purity

**The dualizing complex of a vector bundle.** For a vector bundle `π : E ⟶ B` of constant rank
`r`, presented as the normal bundle of a regular closed immersion `i : B ⟶ X` of pure
codimension `r`,

`ω_π = Rπ^! Λ_B ≅ Λ_E(r)[2r]`.

This is the case `K = Λ_B` of
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_normalBundle`, with
`Lπ^* Λ_B ≅ Λ_E`; `Λ_B` lies in `D^b_{ctf}` as the twisting object `Λ_B(0)`. -/
theorem nonempty_iso_dualizingComplex_normalBundle [HasTateTwist.IsNormalized Λ]
    {k : Type u} [Field k] (r : ℕ) {B X : Scheme.{u}} (i : B ⟶ X) [IsRegularImmersion r i]
    (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB]
    [HasCompactification i.normalBundleProj] [HasInvertibleExponent Λ B] :
    Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) i.normalBundleProj ≅
      (twistShift Λ i.normalBundle r).obj (constantComplex Λ i.normalBundle)) := by
  obtain ⟨e⟩ := nonempty_iso_rightDerivedUpperShriek_normalBundle Λ r i aB (tateObject Λ B 0)
    (boundedConstructibleFiniteTor_tateObject Λ B 0)
  exact ⟨(rightDerivedUpperShriek _ _).mapIso (HasTateTwist.twistObjectZeroIso B).symm ≪≫ e ≪≫
    (twistShift Λ _ r).mapIso ((L((i.normalBundleProj)^*[ModuleCat.{u + 1} Λ])).mapIso
      (HasTateTwist.twistObjectZeroIso B) ≪≫ leftDerivedUpperStarUnitIso _ _)⟩

end Etale

end AlgebraicGeometry
