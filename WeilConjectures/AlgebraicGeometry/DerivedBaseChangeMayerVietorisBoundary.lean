/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeMayerVietorisMaps
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeMayerVietorisBoundaryData

/-! # Connecting square for relative Mayer--Vietoris base change

## References

* Stacks Project, Tags 08BV, 08HY and 0DJ9
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace AlgebraicGeometry

/-- Distinguished cover triangles and the connecting square for the constructed
canonical comparison maps. The open adjunctions are fixed explicit constructions.
This asserts no first or second square and constructs no triangle morphism
(Stacks, Tags 08BV, 08HZ and 0DJ9). -/
theorem derivedBaseChange_mayerVietoris_connectingSquare
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}} [IsAffine S] [IsAffine S']
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    [QuasiCompact f] [QuasiSeparated f]
    (hsq : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (ψ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    ∃ (δ : (schemeDerivedDirectImage (U ⊓ V).ι).obj
          ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.obj K) ⟶ K⟦(1 : ℤ)⟧)
      (δ' : (schemeDerivedDirectImage (g' ⁻¹ᵁ (U ⊓ V)).ι).obj
          ((schemeOpenRestriction X' (g' ⁻¹ᵁ (U ⊓ V))).mapDerivedCategory.obj K') ⟶
          K'⟦(1 : ℤ)⟧)
      (csF : (schemeDerivedDirectImage f ⋙ derivedPullback g).CommShift ℤ)
      (csG : (schemeDerivedDirectImage f').CommShift ℤ),
    let adjU := mvOpenRestrictionAdjunction X U
    let adjV := mvOpenRestrictionAdjunction X V
    let adjUV := mvOpenRestrictionAdjunction X (U ⊓ V)
    let adjU' := mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ U)
    let adjV' := mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ V)
    let adjUV' := mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ (U ⊓ V))
    let F := schemeDerivedDirectImage f ⋙ derivedPullback g
    let G := schemeDerivedDirectImage f'
    let T := mvBaseChangeTriangle X U V (U ⊓ V) (homOfLE inf_le_left)
        (homOfLE inf_le_right) adjU adjV adjUV K δ
    let T' := mvBaseChangeTriangle X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) (g' ⁻¹ᵁ (U ⊓ V))
        ((Opens.map g'.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U)))
        ((Opens.map g'.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V)))
        adjU' adjV' adjUV' K' δ'
    T ∈ distTriang (schemeDerivedCategory X) ∧
    T' ∈ distTriang (schemeDerivedCategory X') ∧
    (@Functor.mapTriangle _ _ _ _ _ _ F csF).obj T ∈
      distTriang (schemeDerivedCategory S') ∧
    (@Functor.mapTriangle _ _ _ _ _ _ G csG).obj T' ∈
      distTriang (schemeDerivedCategory S') ∧
    F.map δ ≫ (letI := csF; F.commShiftIso (1 : ℤ)).hom.app K ≫
        (schemeDerivedBaseChangeMap f f' g g' hsq.w K ≫ G.map ψ)⟦(1 : ℤ)⟧' =
      mvBaseChangeOpenMap f f' g g' hsq.w K K' ψ (U ⊓ V) ≫
        G.map δ' ≫ (letI := csG; G.commShiftIso (1 : ℤ)).hom.app K'
 := by
  let δ := mvCanonicalBoundary X U V (U ⊓ V) rfl hcover K
  let δ' := mvCanonicalBoundary X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) (g' ⁻¹ᵁ (U ⊓ V))
    (Scheme.Hom.preimage_inf g').symm
    (by rw [← Scheme.Hom.preimage_sup, hcover, Scheme.Hom.preimage_top]) K'
  obtain ⟨hT, hT', hF, hG⟩ :=
    mvBoundary_canonical_data f f' g g' K K' U V hcover
  refine ⟨δ, δ', mvCanonicalSourceShift f g, mvCanonicalTargetShift f',
    hT, hT', hF, hG, ?_⟩
  exact mvBoundary_equation f f' g g' hsq K K' U V hcover ψ

end AlgebraicGeometry
