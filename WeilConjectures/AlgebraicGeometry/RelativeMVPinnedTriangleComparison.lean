/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeMayerVietorisBoundary
import WeilConjectures.AlgebraicGeometry.RelativeMVPinnedVertexComparisons
import WeilConjectures.AlgebraicGeometry.RelativeMVRestrictionSquares

/-! # Compatible relative Mayer--Vietoris boundaries

## References

* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08HZ](https://stacks.math.columbia.edu/tag/08HZ)
* [Stacks Project, Tag 08BV](https://stacks.math.columbia.edu/tag/08BV)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Pretriangulated
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

private theorem triangle_transport_distinguished
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : Triangle C) (hT : T ∈ distTriang C) {B D : C}
    (e₂ : T.obj₂ ≅ B) (e₃ : T.obj₃ ≅ D)
    (f : T.obj₁ ⟶ B) (g : B ⟶ D)
    (hf : T.mor₁ ≫ e₂.hom = f) (hg : T.mor₂ ≫ e₃.hom = e₂.hom ≫ g) :
    Triangle.mk f g (e₃.inv ≫ T.mor₃) ∈ distTriang C := by
  apply isomorphic_distinguished _ hT
  refine (Triangle.isoMk T (Triangle.mk f g (e₃.inv ≫ T.mor₃))
    (Iso.refl _) e₂ e₃ ?_ hg ?_).symm
  · change T.mor₁ ≫ e₂.hom = 𝟙 _ ≫ f
    simpa only [Category.id_comp] using hf
  · change T.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map (𝟙 T.obj₁) =
      e₃.hom ≫ e₃.inv ≫ T.mor₃
    rw [(shiftFunctor C (1 : ℤ)).map_id, Category.comp_id, Iso.hom_inv_id_assoc]

/-- The pinned relative restriction maps are the first two arrows of a functorial
pair of distinguished triangles. Their morphism has the prescribed global, open,
and overlap components. This is a derived-category statement, with no assertion
about strict representatives of any of its components. -/
theorem relativeMV_pinned_triangle_comparison
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    [IsAffine S] [IsAffine S'] [QuasiCompact f] [QuasiSeparated f]
    (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    let a := relativeMVLocalArrow f f' g g' hpull K K' φ
    let aX := relativeMVGlobalArrow f f' g g' hpull K K' φ
    ∃ (δ : (a (U ⊓ V)).left ⟶ aX.left⟦(1 : ℤ)⟧)
      (δ' : (a (U ⊓ V)).right ⟶ aX.right⟦(1 : ℤ)⟧),
      Triangle.mk (relativeMVSourceFirst f g U V K)
        (relativeMVSourceSecond f g U V K) δ ∈ distTriang (schemeDerivedCategory S') ∧
      Triangle.mk (relativeMVTargetFirst g' f' U V K')
        (relativeMVTargetSecond g' f' U V K') δ' ∈ distTriang (schemeDerivedCategory S') ∧
      ∃ m :
        Triangle.mk (relativeMVSourceFirst f g U V K) (relativeMVSourceSecond f g U V K) δ ⟶
        Triangle.mk (relativeMVTargetFirst g' f' U V K')
          (relativeMVTargetSecond g' f' U V K') δ',
        m.hom₁ = aX.hom ∧ m.hom₂ = biprod.map (a U).hom (a V).hom ∧
        m.hom₃ = (a (U ⊓ V)).hom := by
  classical
  dsimp only
  obtain ⟨e₂, e₃, e₂', e₃', hf, hg, hf', hg', h₃⟩ :=
    relativeMV_pinned_vertex_comparisons f f' g g' hpull K K' φ U V
  obtain ⟨d, d', csF, csG, _, _, hT, hT', hd⟩ :=
    derivedBaseChange_mayerVietoris_connectingSquare f f' g g' hpull K K'
      φ U V hcover
  let F := schemeDerivedDirectImage f ⋙ derivedPullback g
  let G := schemeDerivedDirectImage f'
  let := csF
  let := csG
  let T := mvBaseChangeTriangle X U V (U ⊓ V) (homOfLE inf_le_left)
    (homOfLE inf_le_right) (mvOpenRestrictionAdjunction X U)
    (mvOpenRestrictionAdjunction X V) (mvOpenRestrictionAdjunction X (U ⊓ V)) K d
  let T' := mvBaseChangeTriangle X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) (g' ⁻¹ᵁ (U ⊓ V))
    ((TopologicalSpace.Opens.map g'.base).map (homOfLE (inf_le_left : U ⊓ V ≤ U)))
    ((TopologicalSpace.Opens.map g'.base).map (homOfLE (inf_le_right : U ⊓ V ≤ V)))
    (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ U))
    (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ V))
    (mvOpenRestrictionAdjunction X' (g' ⁻¹ᵁ (U ⊓ V))) K' d'
  let δ := e₃.inv ≫ (F.mapTriangle.obj T).mor₃
  let δ' := e₃'.inv ≫ (G.mapTriangle.obj T').mor₃
  have hs := relativeMV_restriction_squares f f' g g' hpull K K' φ U V
  have hc : δ ≫ (relativeMVGlobalArrow f f' g g' hpull K K' φ).hom⟦(1 : ℤ)⟧' =
      (relativeMVLocalArrow f f' g g' hpull K K' φ (U ⊓ V)).hom ≫ δ' := by
    have hi : e₃.inv ≫ mvBaseChangeOpenMap f f' g g' hpull.w K K' φ (U ⊓ V) =
        (relativeMVLocalArrow f f' g g' hpull K K' φ (U ⊓ V)).hom ≫ e₃'.inv := by
      apply (cancel_mono e₃'.hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      simp only [h₃, Iso.inv_hom_id_assoc]
    have hd' : (F.mapTriangle.obj T).mor₃ ≫
        (relativeMVGlobalArrow f f' g g' hpull K K' φ).hom⟦(1 : ℤ)⟧' =
        mvBaseChangeOpenMap f f' g g' hpull.w K K' φ (U ⊓ V) ≫
          (G.mapTriangle.obj T').mor₃ := by
      simpa only [Functor.mapTriangle, T, T', mvBaseChangeTriangle, Triangle.mk,
        Functor.id_obj, relativeMVGlobalArrow, Arrow.mk_hom, F, G, Category.assoc] using hd
    dsimp only [δ, δ']
    simp only [Category.assoc, hd']
    simpa only [Category.assoc] using
      congrArg (fun k ↦ k ≫ (G.mapTriangle.obj T').mor₃) hi
  refine ⟨δ, δ', ?_, ?_, ?_⟩
  · exact triangle_transport_distinguished (F.mapTriangle.obj T) hT e₂ e₃ _ _ hf hg
  · exact triangle_transport_distinguished (G.mapTriangle.obj T') hT' e₂' e₃' _ _ hf' hg'
  · exact ⟨Triangle.homMk _ _
      (relativeMVGlobalArrow f f' g g' hpull K K' φ).hom
      (biprod.map (relativeMVLocalArrow f f' g g' hpull K K' φ U).hom
        (relativeMVLocalArrow f f' g g' hpull K K' φ V).hom)
      (relativeMVLocalArrow f f' g g' hpull K K' φ (U ⊓ V)).hom
      hs.1 hs.2 hc, rfl, rfl, rfl⟩

end AlgebraicGeometry
