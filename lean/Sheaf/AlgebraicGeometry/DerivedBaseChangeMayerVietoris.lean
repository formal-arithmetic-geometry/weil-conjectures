/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedMayerVietorisTriangle
public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde

/-! # Base change and the relative Mayer--Vietoris triangle

Source: Stacks Project, Tag 0DJ9, induction step, and Tag 08BV
(blueprint: lem-pc-rf-mv-triangle-naturality).
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

/-- Base change and a map on the pullback give a morphism of the two relative
Mayer--Vietoris distinguished triangles, including their connecting morphisms.
The middle component is characterized by its two projections, so no choice of a
biproduct comparison is needed. The open components are expressed before the
canonical direct-image composition identifications: base change first for `f`,
then for the open immersion, followed by the restricted map. Pasting of canonical
base-change maps identifies these with the maps for `f|W` in the source.

Source: Stacks Project, Tag 0DJ9, induction step; Cohomology, Tag 08BV
(blueprint: lem-pc-rf-mv-triangle-naturality).
Proof:
1. Since the bases are affine, `g` and its base change `g'` are affine and hence
   qcqs (lem-weil-pbc-morphism-affine-schemes-affine,
   lem-weil-pbc-affine-morphism-permanence). The qcqs morphisms `f` and `f'` over
   affine bases have qcqs sources (lem-weil-pbc-qcqs-over-affine). The inverse-image
   cover has quasi-compact members and intersection. Apply
   lem-pc-derived-mayer-vietoris-triangle twice. The exact functors `Lg* Rf*`
   and `Rf'*` take these to distinguished triangles. Use
   lem-pc-derived-direct-image-composition to identify the relative terms.
2. Transpose the given map to `K → Rg'* K'` using
   lem-pc-pre-derived-adjoint-functors-general. Its target has quasi-coherent
   cohomology by lem-pc-derived-direct-image-preserves-qcoh. Restriction commutes
   with these adjunctions. By def-pc-derived-base-change-map, the adjoints of the
   four comparison maps are the direct images of these restricted maps followed
   by the composition comparisons. Apply both parts of
   lem-pc-derived-mayer-vietoris-functorial: naturality in the object, and
   compatibility with `Rg'*`. Apply `Rf*` and transpose back. Naturality of the
   adjunction bijection gives the first two commuting squares; its compatibility
   with shift gives the connecting square. -/
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
      Triangle.mk (biprod.lift (adjU.unit.app K) (adjV.unit.app K))
        (biprod.desc
          (schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_left)
            adjU adjUV K)
          (-(schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_right)
            adjV adjUV K))) δ ∈ distTriang (schemeDerivedCategory X) ∧
      Triangle.mk (biprod.lift (adjU'.unit.app K') (adjV'.unit.app K'))
        (biprod.desc
          (schemeDerivedOpenDirectImageRestriction X'
            ((Opens.map g'.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U)))
            adjU' adjUV' K')
          (-(schemeDerivedOpenDirectImageRestriction X'
            ((Opens.map g'.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V)))
            adjV' adjUV' K'))) δ' ∈ distTriang (schemeDerivedCategory X') ∧
      (@Functor.mapTriangle _ _ _ _ _ _ (schemeDerivedDirectImage f ⋙ derivedPullback g) csF).obj (
        Triangle.mk (biprod.lift (adjU.unit.app K) (adjV.unit.app K))
          (biprod.desc
            (schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_left)
              adjU adjUV K)
            (-(schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_right)
              adjV adjUV K))) δ) ∈ distTriang (schemeDerivedCategory S') ∧
      (@Functor.mapTriangle _ _ _ _ _ _ (schemeDerivedDirectImage f') csG).obj (
        Triangle.mk (biprod.lift (adjU'.unit.app K') (adjV'.unit.app K'))
          (biprod.desc
            (schemeDerivedOpenDirectImageRestriction X'
            ((Opens.map g'.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U)))
              adjU' adjUV' K')
            (-(schemeDerivedOpenDirectImageRestriction X'
            ((Opens.map g'.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V)))
              adjV' adjUV' K'))) δ') ∈ distTriang (schemeDerivedCategory S') ∧
      ∃ φ :
        (@Functor.mapTriangle _ _ _ _ _ _ (schemeDerivedDirectImage f ⋙ derivedPullback g) csF).obj
          (
          Triangle.mk (biprod.lift (adjU.unit.app K) (adjV.unit.app K))
            (biprod.desc
              (schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_left)
                adjU adjUV K)
              (-(schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_right)
                adjV adjUV K))) δ) ⟶
        (@Functor.mapTriangle _ _ _ _ _ _ (schemeDerivedDirectImage f') csG).obj (
          Triangle.mk (biprod.lift (adjU'.unit.app K') (adjV'.unit.app K'))
            (biprod.desc
              (schemeDerivedOpenDirectImageRestriction X'
            ((Opens.map g'.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U)))
                adjU' adjUV' K')
              (-(schemeDerivedOpenDirectImageRestriction X'
            ((Opens.map g'.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V)))
                adjV' adjUV' K'))) δ'),
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
                    (Classical.choice (derivedPullback_openRestriction_iso g'
                      (g' ⁻¹ᵁ U) U le_rfl)).inv.app K ≫
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
                    (Classical.choice (derivedPullback_openRestriction_iso g'
                      (g' ⁻¹ᵁ V) V le_rfl)).inv.app K ≫
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
                    (Classical.choice (derivedPullback_openRestriction_iso g'
                      (g' ⁻¹ᵁ (U ⊓ V)) (U ⊓ V) le_rfl)).inv.app K ≫
                    (schemeOpenRestriction X' (g' ⁻¹ᵁ (U ⊓ V))).mapDerivedCategory.map ψ)) ∧
          φ.hom₂ ≫ (schemeDerivedDirectImage f').map biprod.fst =
            (schemeDerivedDirectImage f ⋙ derivedPullback g).map biprod.fst ≫ aU ∧
          φ.hom₂ ≫ (schemeDerivedDirectImage f').map biprod.snd =
            (schemeDerivedDirectImage f ⋙ derivedPullback g).map biprod.snd ≫ aV ∧
          φ.hom₃ = aUV := by
  sorry

end AlgebraicGeometry
