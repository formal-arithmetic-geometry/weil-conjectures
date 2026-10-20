/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeMayerVietorisMaps
import Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisSquares
import Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietorisBoundary
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive

/-! # Base change and the relative Mayer--Vietoris triangle

Source: Stacks Project, Tag 0DJ9, induction step, and Tag 08BV
(blueprint: lem-pc-rf-mv-triangle-naturality).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

noncomputable section

namespace AlgebraicGeometry

set_option maxHeartbeats 200000 in
-- The expanded triangle statement needs a larger elaboration budget.
/-- Base change and a map on the pullback give a morphism of the two relative
Mayer--Vietoris distinguished triangles, including their connecting morphisms.
The middle component is characterized by its two projections, so no choice of a
biproduct comparison is needed. The open pullback comparisons are explicit
adjunction/composition constructions, not witnesses of bare existence.
The open components are expressed before the
canonical direct-image composition identifications: base change first for `f`,
then for the open immersion, followed by the restricted map. Pasting of canonical
base-change maps identifies these with the maps for `f|W` in the source.

Source: Stacks Project, Tag 0DJ9, induction step; Cohomology, Tag 08BV
(blueprint: lem-pc-rf-mv-triangle-naturality).
Proof:
1. For the six explicitly constructed open adjunctions, the unit and restriction
   squares are supplied by lem-pc-rf-mv-base-change-first-two-squares.
2. Lemma lem-pc-rf-mv-base-change-connecting-square supplies distinguished
   cover triangles, their distinguished images, and the connecting square.
3. Use the whole-space, diagonal biproduct, and overlap maps as the three
   components of TriangleMorphism. The three equations from steps 1 and 2
   are exactly its commutativity fields. Distribute composition over the sum
   defining the middle component. The identities inl/fst = id, inr/fst = 0,
   inl/snd = 0 and inr/snd = id give its two prescribed projections. -/
theorem derivedBaseChange_mayerVietoris_naturality
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}} [IsAffine S] [IsAffine S']
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    [QuasiCompact f] [QuasiSeparated f]
    (hsq : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (hK : schemeDerivedQCohProperty X K) (hK' : schemeDerivedQCohProperty X' K')
    (ψ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    (hUV : IsCompact ((U ⊓ V : X.Opens) : Set X)) (hcover : U ⊔ V = ⊤) :
    ∃ (adjU : (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
      (adjV : (schemeOpenRestriction X V).mapDerivedCategory ⊣ schemeDerivedDirectImage V.ι)
      (adjUV : (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory ⊣ schemeDerivedDirectImage (U ⊓
        V).ι)
      (δ : (schemeDerivedDirectImage (U ⊓ V).ι).obj
        ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.obj K) ⟶ K⟦(1 : ℤ)⟧)
      (adjU' : (schemeOpenRestriction X' (g' ⁻¹ᵁ U)).mapDerivedCategory ⊣ schemeDerivedDirectImage
        (g' ⁻¹ᵁ U).ι)
      (adjV' : (schemeOpenRestriction X' (g' ⁻¹ᵁ V)).mapDerivedCategory ⊣ schemeDerivedDirectImage
        (g' ⁻¹ᵁ V).ι)
      (adjUV' : (schemeOpenRestriction X' (g' ⁻¹ᵁ (U ⊓ V))).mapDerivedCategory ⊣
        schemeDerivedDirectImage (g' ⁻¹ᵁ (U ⊓ V)).ι)
      (δ' : (schemeDerivedDirectImage (g' ⁻¹ᵁ (U ⊓ V)).ι).obj
        ((schemeOpenRestriction X' (g' ⁻¹ᵁ (U ⊓ V))).mapDerivedCategory.obj K') ⟶ K'⟦(1 : ℤ)⟧),
    ∃ (csF : (schemeDerivedDirectImage f ⋙ derivedPullback g).CommShift ℤ)
      (csG : (schemeDerivedDirectImage f').CommShift ℤ),
      mvBaseChangeTriangle X U V (U ⊓ V) (homOfLE inf_le_left)
        (homOfLE inf_le_right) adjU adjV adjUV K δ ∈ distTriang (schemeDerivedCategory X) ∧
      mvBaseChangeTriangle X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) (g' ⁻¹ᵁ (U ⊓ V))
        ((Opens.map g'.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U)))
        ((Opens.map g'.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V)))
        adjU' adjV' adjUV' K' δ' ∈ distTriang (schemeDerivedCategory X') ∧
      (@Functor.mapTriangle _ _ _ _ _ _ (schemeDerivedDirectImage f ⋙ derivedPullback g) csF).obj (
        mvBaseChangeTriangle X U V (U ⊓ V) (homOfLE inf_le_left)
        (homOfLE inf_le_right) adjU adjV adjUV K δ) ∈ distTriang (schemeDerivedCategory S') ∧
      (@Functor.mapTriangle _ _ _ _ _ _ (schemeDerivedDirectImage f') csG).obj (
        mvBaseChangeTriangle X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) (g' ⁻¹ᵁ (U ⊓ V))
        ((Opens.map g'.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U)))
        ((Opens.map g'.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V)))
        adjU' adjV' adjUV' K' δ') ∈ distTriang (schemeDerivedCategory S') ∧
      ∃ φ :
        (@Functor.mapTriangle _ _ _ _ _ _ (schemeDerivedDirectImage f ⋙ derivedPullback g) csF).obj
          (mvBaseChangeTriangle X U V (U ⊓ V) (homOfLE inf_le_left)
        (homOfLE inf_le_right) adjU adjV adjUV K δ) ⟶
        (@Functor.mapTriangle _ _ _ _ _ _ (schemeDerivedDirectImage f') csG).obj (
          mvBaseChangeTriangle X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) (g' ⁻¹ᵁ (U ⊓ V))
        ((Opens.map g'.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U)))
        ((Opens.map g'.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V)))
        adjU' adjV' adjUV' K' δ'),
        φ.hom₁ = schemeDerivedBaseChangeMap f f' g g' hsq.w K ≫
          (schemeDerivedDirectImage f').map ψ ∧
        ∃ aU : (schemeDerivedDirectImage f ⋙ derivedPullback g).obj
            ((schemeDerivedDirectImage U.ι).obj ((schemeOpenRestriction X U).mapDerivedCategory.obj
              K)) ⟶
          (schemeDerivedDirectImage f').obj
            ((schemeDerivedDirectImage (g' ⁻¹ᵁ U).ι).obj ((schemeOpenRestriction X' (g' ⁻¹ᵁ
              U)).mapDerivedCategory.obj K')),
          aU =
            schemeDerivedBaseChangeMap f f' g g' hsq.w
                ((schemeDerivedDirectImage U.ι).obj ((schemeOpenRestriction X
                  U).mapDerivedCategory.obj K)) ≫
              (schemeDerivedDirectImage f').map (
                schemeDerivedBaseChangeMap U.ι (g' ⁻¹ᵁ U).ι g'
                    (g'.resLE U (g' ⁻¹ᵁ U) le_rfl)
                    (Scheme.Hom.resLE_comp_ι g' le_rfl)
                    ((schemeOpenRestriction X U).mapDerivedCategory.obj K) ≫
                  (schemeDerivedDirectImage (g' ⁻¹ᵁ U).ι).map (
                    (mvPullbackOpenRestrictionIso g' U).inv.app K ≫
                    (schemeOpenRestriction X' (g' ⁻¹ᵁ U)).mapDerivedCategory.map ψ)) ∧
        ∃ aV : (schemeDerivedDirectImage f ⋙ derivedPullback g).obj
            ((schemeDerivedDirectImage V.ι).obj ((schemeOpenRestriction X V).mapDerivedCategory.obj
              K)) ⟶
          (schemeDerivedDirectImage f').obj
            ((schemeDerivedDirectImage (g' ⁻¹ᵁ V).ι).obj ((schemeOpenRestriction X' (g' ⁻¹ᵁ
              V)).mapDerivedCategory.obj K')),
          aV =
            schemeDerivedBaseChangeMap f f' g g' hsq.w
                ((schemeDerivedDirectImage V.ι).obj ((schemeOpenRestriction X
                  V).mapDerivedCategory.obj K)) ≫
              (schemeDerivedDirectImage f').map (
                schemeDerivedBaseChangeMap V.ι (g' ⁻¹ᵁ V).ι g'
                    (g'.resLE V (g' ⁻¹ᵁ V) le_rfl)
                    (Scheme.Hom.resLE_comp_ι g' le_rfl)
                    ((schemeOpenRestriction X V).mapDerivedCategory.obj K) ≫
                  (schemeDerivedDirectImage (g' ⁻¹ᵁ V).ι).map (
                    (mvPullbackOpenRestrictionIso g' V).inv.app K ≫
                    (schemeOpenRestriction X' (g' ⁻¹ᵁ V)).mapDerivedCategory.map ψ)) ∧
        ∃ aUV : (schemeDerivedDirectImage f ⋙ derivedPullback g).obj
            ((schemeDerivedDirectImage (U ⊓ V).ι).obj ((schemeOpenRestriction X (U ⊓
              V)).mapDerivedCategory.obj K)) ⟶
          (schemeDerivedDirectImage f').obj
            ((schemeDerivedDirectImage (g' ⁻¹ᵁ (U ⊓ V)).ι).obj ((schemeOpenRestriction X' (g' ⁻¹ᵁ (U
              ⊓ V))).mapDerivedCategory.obj K')),
          aUV =
            schemeDerivedBaseChangeMap f f' g g' hsq.w
                ((schemeDerivedDirectImage (U ⊓ V).ι).obj ((schemeOpenRestriction X (U ⊓
                  V)).mapDerivedCategory.obj K)) ≫
              (schemeDerivedDirectImage f').map (
                schemeDerivedBaseChangeMap (U ⊓ V).ι (g' ⁻¹ᵁ (U ⊓ V)).ι g'
                    (g'.resLE (U ⊓ V) (g' ⁻¹ᵁ (U ⊓ V)) le_rfl)
                    (Scheme.Hom.resLE_comp_ι g' le_rfl)
                    ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.obj K) ≫
                  (schemeDerivedDirectImage (g' ⁻¹ᵁ (U ⊓ V)).ι).map (
                    (mvPullbackOpenRestrictionIso g' (U ⊓ V)).inv.app K ≫
                    (schemeOpenRestriction X' (g' ⁻¹ᵁ (U ⊓ V))).mapDerivedCategory.map ψ)) ∧
          φ.hom₂ ≫ (schemeDerivedDirectImage f').map biprod.fst =
            (schemeDerivedDirectImage f ⋙ derivedPullback g).map biprod.fst ≫ aU ∧
          φ.hom₂ ≫ (schemeDerivedDirectImage f').map biprod.snd =
            (schemeDerivedDirectImage f ⋙ derivedPullback g).map biprod.snd ≫ aV ∧
          φ.hom₃ = aUV := by
  classical
  let : Preadditive (schemeDerivedCategory X) := inferInstance
  let : Preadditive (schemeDerivedCategory X') := inferInstance
  let : Preadditive (schemeDerivedCategory S') := inferInstance
  let : HasFiniteBiproducts (schemeDerivedCategory X) := inferInstance
  let : HasFiniteBiproducts (schemeDerivedCategory X') := inferInstance
  let adjU := mvOpenRestrictionAdjunction.{u, w} X U
  let adjV := mvOpenRestrictionAdjunction.{u, w} X V
  let adjUV := mvOpenRestrictionAdjunction.{u, w} X (U ⊓ V)
  let adjU' := mvOpenRestrictionAdjunction.{u, w} X' (g' ⁻¹ᵁ U)
  let adjV' := mvOpenRestrictionAdjunction.{u, w} X' (g' ⁻¹ᵁ V)
  let adjUV' := mvOpenRestrictionAdjunction.{u, w} X' (g' ⁻¹ᵁ (U ⊓ V))
  have hsquares := derivedBaseChange_mayerVietoris_firstTwoSquares.{u, w}
    (X := X) (S := S) (X' := X') (S' := S') f f' g g' hsq U V hU hV hUV hcover
  have hb :=
    derivedBaseChange_mayerVietoris_connectingSquare.{u, w}
      (X := X) (S := S) (X' := X') (S' := S') f f' g g' hsq K K' hK hK' ψ
      U V hU hV hUV hcover
  rcases hb with ⟨δ, δ', csF, csG, hT, hT', hFT, hGT', hδ⟩
  let F := schemeDerivedDirectImage f ⋙ derivedPullback g
  let G := schemeDerivedDirectImage f'
  let : F.CommShift ℤ := csF
  let : G.CommShift ℤ := csG
  let T := mvBaseChangeTriangle.{u, w} X U V (U ⊓ V) (homOfLE inf_le_left)
    (homOfLE inf_le_right) adjU adjV adjUV K δ
  let T' := mvBaseChangeTriangle.{u, w} X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) (g' ⁻¹ᵁ (U ⊓ V))
    ((Opens.map g'.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U)))
    ((Opens.map g'.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V)))
    adjU' adjV' adjUV' K' δ'
  let a₀ := schemeDerivedBaseChangeMap.{u, w} f f' g g' hsq.w K ≫ G.map ψ
  let a₂ := mvBaseChangeMiddle.{u, w} f f' g g' hsq.w K K' ψ U V
  let aU := mvBaseChangeOpenMap.{u, w} f f' g g' hsq.w K K' ψ U
  let aV := mvBaseChangeOpenMap.{u, w} f f' g g' hsq.w K K' ψ V
  let aUV := mvBaseChangeOpenMap.{u, w} f f' g g' hsq.w K K' ψ (U ⊓ V)
  have h12 := hsquares K K' hK hK' ψ
  let φ : F.mapTriangle.obj T ⟶ G.mapTriangle.obj T' :=
    { hom₁ := a₀
      hom₂ := a₂
      hom₃ := aUV
      comm₁ := h12.1
      comm₂ := h12.2
      comm₃ := by
        dsimp only [Functor.mapTriangle, T, T', mvBaseChangeTriangle, Triangle.mk, a₀, aUV, F, G]
        simpa only [Functor.id_obj, Category.assoc] using hδ }
  refine ⟨adjU, adjV, adjUV, δ, adjU', adjV', adjUV', δ', csF, csG,
    hT, hT', hFT, hGT', φ, rfl, aU, rfl, aV, rfl, aUV, rfl, ?_, ?_, rfl⟩
  · change a₂ ≫ G.map biprod.fst = F.map biprod.fst ≫ aU
    dsimp only [a₂, mvBaseChangeMiddle, aU]
    dsimp only [G]
    simp only [Preadditive.add_comp, Category.assoc, ← Functor.map_comp,
      biprod.inl_fst, biprod.inr_fst, (schemeDerivedDirectImage f').map_id,
      (schemeDerivedDirectImage f').map_zero,
      Category.comp_id, comp_zero, add_zero]
    rfl
  · change a₂ ≫ G.map biprod.snd = F.map biprod.snd ≫ aV
    dsimp only [a₂, mvBaseChangeMiddle, aV, G]
    simp only [Preadditive.add_comp, Category.assoc, ← Functor.map_comp,
      biprod.inl_snd, biprod.inr_snd, (schemeDerivedDirectImage f').map_id,
      (schemeDerivedDirectImage f').map_zero,
      Category.comp_id, comp_zero, zero_add]
    rfl

end AlgebraicGeometry
