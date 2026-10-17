/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-!
# The canonical maps of the exceptional inverse image along the identity

For the identity `𝟙 X`, the derived direct image with compact support is the identity,
`R(𝟙)_! ≅ R(𝟙)_* ≅ 𝟭`, so the adjunction `R(𝟙)_! ⊣ R(𝟙)^!` is an adjoint equivalence: its unit
and counit are isomorphisms. Consequently the canonical tensor maps
`θ_{𝟙,K} : ω_𝟙 ⊗ᴸ K ⟶ R(𝟙)^! K`, adjoint transposes of isomorphisms, are isomorphisms, and
`ω_𝟙 = R(𝟙)^! Λ_X ≅ Λ_X`.

This is the identity case of smooth duality for étale morphisms
(`WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Etale`); it is kept apart from the
global duality statements (`AlgebraicGeometry.Etale.rightDerivedUpperShriekIdIso`), which are
built on smooth purity.

## Main statements

- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekAdjunction_unit_id`,
  `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekAdjunction_counit_id`
- `AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_id`
- `AlgebraicGeometry.Etale.nonempty_dualizingComplex_id_iso`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u}) [HasCompactification (𝟙 X)]

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- definitions of the derived tensor product.
attribute [local instance high] SymmetricCategory.toBraidedCategory

omit [Finite Λ] in
/-- `R(𝟙)_! ≅ 𝟭`: the identity is proper, so `R(𝟙)_! ≅ R(𝟙)_*`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`), and
`(𝟙)_* ≅ 𝟭`. -/
lemma nonempty_rightDerivedLowerShriek_id_iso :
    Nonempty (R(𝟙 X)_![ModuleCat.{u + 1} Λ] ≅ 𝟭 _) :=
  ⟨rightDerivedLowerShriekIsoRightDerivedLowerStar _ (𝟙 X) ≪≫
    Functor.rightDerivedFunctorNatIso (Etale.lowerStarId _ X) ≪≫
    (𝟭 _).rightDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _⟩

/-- The unit of `R(𝟙)_! ⊣ R(𝟙)^!` is an isomorphism, `R(𝟙)_!` being fully faithful. -/
lemma isIso_rightDerivedUpperShriekAdjunction_unit_id :
    IsIso (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X)).unit := by
  obtain ⟨e⟩ := nonempty_rightDerivedLowerShriek_id_iso Λ X
  have : (R(𝟙 X)_![ModuleCat.{u + 1} Λ]).Full := Functor.Full.of_iso e.symm
  have : (R(𝟙 X)_![ModuleCat.{u + 1} Λ]).Faithful := Functor.Faithful.of_iso e.symm
  exact (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X)).unit_isIso_of_L_fully_faithful

/-- The counit of `R(𝟙)_! ⊣ R(𝟙)^!` is an isomorphism: `R(𝟙)^!` is right adjoint to
`R(𝟙)_! ≅ 𝟭`, hence isomorphic to `𝟭` and fully faithful. -/
lemma isIso_rightDerivedUpperShriekAdjunction_counit_id :
    IsIso (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X)).counit := by
  obtain ⟨e⟩ := nonempty_rightDerivedLowerShriek_id_iso Λ X
  let e' : R(𝟙 X)^![ModuleCat.{u + 1} Λ] ≅ 𝟭 _ :=
    (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X)).rightAdjointUniq
      (Adjunction.id.ofNatIsoLeft e.symm)
  have : (R(𝟙 X)^![ModuleCat.{u + 1} Λ]).Full := Functor.Full.of_iso e'.symm
  have : (R(𝟙 X)^![ModuleCat.{u + 1} Λ]).Faithful := Functor.Faithful.of_iso e'.symm
  exact (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X)).counit_isIso_of_R_fully_faithful

/-- For the identity `𝟙 X`, the canonical tensor map `θ_{𝟙,K}` is an isomorphism: it is the
adjoint transpose of an isomorphism along the adjoint equivalence `R(𝟙)_! ⊣ R(𝟙)^!`. -/
theorem isIso_dualizingComplexTensorMap_id
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (dualizingComplexTensorMap Λ (𝟙 X) K) := by
  have := isIso_rightDerivedUpperShriekAdjunction_unit_id Λ X
  have := isIso_rightDerivedUpperShriekAdjunction_counit_id Λ X
  change IsIso (dualizingComplexTensorMapOfIsIso (𝟙 X) K)
  rw [isIso_dualizingComplexTensorMapOfIsIso_iff, rightDerivedUpperShriekTensorMap,
    Adjunction.projectionTensorMap, Adjunction.homEquiv_unit]
  infer_instance

/-- For the identity `𝟙 X`, the dualizing complex is trivial, `ω_𝟙 = R(𝟙)^! Λ_X ≅ Λ_X`. -/
theorem nonempty_dualizingComplex_id_iso :
    Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) (𝟙 X) ≅ 𝟙_ _) := by
  obtain ⟨e⟩ := nonempty_rightDerivedLowerShriek_id_iso Λ X
  exact ⟨((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X)).rightAdjointUniq
    (Adjunction.id.ofNatIsoLeft e.symm)).app _⟩

end Etale

end AlgebraicGeometry
