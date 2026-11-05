/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineStrictlyLocalSections
public import WeilConjectures.SixFunctors.BaseChange.DerivedForget
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent

/-!
# Acyclicity of the affine line over strictly henselian local rings: assembly

Let `φ : A ⟶ B` be a local homomorphism of strictly henselian local rings and `M` a locally
constant sheaf of `Λ`-modules on `Spec A`. The pullback map
`Hᵠ(𝔸¹_A, p_A^* M) ⟶ Hᵠ(𝔸¹_B, p_A^* M|)` along `𝔸¹_B ⟶ 𝔸¹_A` is bijective in degree `0`
(`AlgebraicGeometry.Etale.bijective_cohomologyMap_zero_affineLine_of_strictlyHenselian`). In
positive degrees it is bijective as soon as `Hᵠ(𝔸¹_R, p_R^* L) = 0` for every strictly
henselian local ring `R` on which the exponent of `Λ` is invertible and every locally constant
sheaf `L` of `Λ`-modules on `Spec R`: both sides then vanish, the target being identified with
`Hᵠ(𝔸¹_B, p_B^* (g^* M))`, `g : Spec B ⟶ Spec A`.

The vanishing in positive degrees is taken as a hypothesis here, split into degree `1` and
degrees `≥ 2`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The pullback along `𝔸¹_B ⟶ 𝔸¹_A` of the underlying abelian sheaf of `p_A^* M` is the
underlying abelian sheaf of `p_B^* (g^* M)`, `g : Spec B ⟶ Spec A`. -/
noncomputable def affineLineMapUpperStarForget₂Iso {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (M : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (AffineSpace.map (ULift.{u} (Fin 1)) (Spec.map (CommRingCat.ofHom φ)))^*[
        AddCommGrpCat.{u + 1}].obj
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((𝔸(ULift.{u} (Fin 1); Spec (.of A)) ↘ Spec (.of A))^*[ModuleCat.{u + 1} Λ].obj M)) ≅
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((𝔸(ULift.{u} (Fin 1); Spec (.of B)) ↘ Spec (.of B))^*[ModuleCat.{u + 1} Λ].obj
          ((Spec.map (CommRingCat.ofHom φ))^*[ModuleCat.{u + 1} Λ].obj M)) :=
  asIso ((upperStarForget₂ Λ
      (AffineSpace.map (ULift.{u} (Fin 1)) (Spec.map (CommRingCat.ofHom φ)))).natTrans.app _) ≪≫
    (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).mapIso
      (((upperStarComp _ (AffineSpace.map (ULift.{u} (Fin 1)) (Spec.map (CommRingCat.ofHom φ)))
        (𝔸(ULift.{u} (Fin 1); Spec (.of A)) ↘ Spec (.of A))).app M).symm ≪≫
      (upperStarComp _ (𝔸(ULift.{u} (Fin 1); Spec (.of B)) ↘ Spec (.of B))
        (Spec.map (CommRingCat.ofHom φ)) _ (AffineSpace.map_over _)).app M)

/-- **Acyclicity of the affine line over strictly henselian local rings, from the vanishing in
positive degrees.** Suppose that `Hᵠ(𝔸¹_R, p_R^* L) = 0` for `q > 0`, every strictly henselian
local ring `R` on which the exponent of `Λ` is invertible and every locally constant sheaf `L`
of `Λ`-modules on `Spec R`. Then for a local homomorphism `φ : A ⟶ B` of strictly henselian
local rings and `M` locally constant on `Spec A`, the pullback map
`Hᵠ(𝔸¹_A, p_A^* M) ⟶ Hᵠ(𝔸¹_B, p_A^* M|)` is bijective for every `q`. -/
theorem bijective_cohomologyMap_affineLine_of_strictlyHenselian_of_subsingleton
    (hvan : ∀ (R : Type u) [CommRing R] [HenselianLocalRing R]
      [IsSepClosed (IsLocalRing.ResidueField R)] [HasInvertibleExponent Λ (Spec (.of R))]
      (L : Sheaf (Spec (.of R)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
      [IsLocallyConstantSheaf L] (q : ℕ), 0 < q →
      Subsingleton (Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ)
        AddCommGrpCat.{u + 1})).obj
          ((𝔸(ULift.{u} (Fin 1); Spec (.of R)) ↘ Spec (.of R))^*[ModuleCat.{u + 1} Λ].obj L)) q))
    {A B : Type u} [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)] [CommRing B] [HenselianLocalRing B]
    [IsSepClosed (IsLocalRing.ResidueField B)] (φ : A →+* B)
    [HasInvertibleExponent Λ (Spec (.of A))]
    (M : Sheaf (Spec (.of A)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsLocallyConstantSheaf M] (q : ℕ) :
    Function.Bijective (cohomologyMap
      (AffineSpace.map (ULift.{u} (Fin 1)) (Spec.map (CommRingCat.ofHom φ)))
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((𝔸(ULift.{u} (Fin 1); Spec (.of A)) ↘ Spec (.of A))^*[ModuleCat.{u + 1} Λ].obj M)) q) := by
  obtain rfl | hq := Nat.eq_zero_or_pos q
  · exact bijective_cohomologyMap_zero_affineLine_of_strictlyHenselian Λ φ M
  have : HasInvertibleExponent Λ (Spec (.of B)) := .of_hom (Spec.map (CommRingCat.ofHom φ))
  have := IsLocallyConstantSheaf.upperStar (Spec.map (CommRingCat.ofHom φ)) M
  have hA := hvan A M q hq
  have hB := hvan B ((Spec.map (CommRingCat.ofHom φ))^*[ModuleCat.{u + 1} Λ].obj M) q hq
  have hB' := ((bijective_sheafHMap_hom (affineLineMapUpperStarForget₂Iso Λ φ M).symm q).2)
  have := hB'.subsingleton
  exact ⟨fun a b _ ↦ Subsingleton.elim a b, fun c ↦ ⟨0, Subsingleton.elim _ _⟩⟩

end Etale

end AlgebraicGeometry
