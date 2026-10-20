/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the LICENSE file.
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainMap
public import WeilConjectures.AlgebraicGeometry.DirectImageSquareUnitTransport
import Sheaf.AlgebraicGeometry.RelativeMVNormalizedCoefficientRoof
import Sheaf.AlgebraicGeometry.RelativeMVResolvedRoofOpenMateComparisons

/-! # Mate comparisons for the concrete resolved row roof -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits CochainComplex
namespace AlgebraicGeometry

private lemma mate_transpose_to
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    {M : C} {K : D} (β : M ⟶ R₁.obj K) (δ : L₂.obj M ⟶ K)
    (h : α.app M ≫ L₁.map β ≫ a₁.counit.app K = δ) :
    β ≫ (conjugateEquiv a₁ a₂ α).app K = a₂.homEquiv M K δ := by
  apply (a₂.homEquiv M K).symm.injective
  simp only [Adjunction.homEquiv_symm_apply, Functor.map_comp, Category.assoc]
  rw [conjugateEquiv_counit, ← Category.assoc, α.naturality, Category.assoc]
  have hδ : L₂.map ((a₂.homEquiv M K) δ) ≫ a₂.counit.app K = δ := by
    simpa only [Adjunction.homEquiv_symm_apply] using
      (a₂.homEquiv M K).symm_apply_apply δ
  exact h.trans hδ.symm

private lemma square_conjugate_transpose
    {C₀ C₁ C₂ C₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    {F : C₀ ⥤ C₁} {R : C₁ ⥤ C₀} {G : C₀ ⥤ C₂} {T : C₂ ⥤ C₀}
    {F' : C₂ ⥤ C₃} {R' : C₃ ⥤ C₂} {G' : C₁ ⥤ C₃} {T' : C₃ ⥤ C₁}
    (af : F ⊣ R) (ag : G ⊣ T) (af' : F' ⊣ R') (ag' : G' ⊣ T')
    (α : G ⋙ F' ≅ F ⋙ G') {K : C₁} {K' : C₃} (φ : G'.obj K ⟶ K') :
    ag.homEquiv _ _ (af'.homEquiv _ _
        (α.hom.app (R.obj K) ≫ G'.map (af.counit.app K) ≫ φ)) =
      R.map (ag'.homEquiv _ _ φ) ≫
        (conjugateEquiv (af.comp ag') (ag.comp af') α.hom).app K' := by
  have h := mate_transpose_to (af.comp ag') (ag.comp af') α.hom
    (R.map (ag'.homEquiv _ _ φ))
    (α.hom.app (R.obj K) ≫ G'.map (af.counit.app K) ≫ φ) ?_
  · rw [Adjunction.comp_homEquiv] at h
    exact h.symm
  · simp only [Functor.comp_map, Adjunction.comp_counit_app]
    have hn := af.counit.naturality (ag'.homEquiv _ _ φ)
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    rw [← G'.map_comp_assoc, hn]
    simp only [G'.map_comp, Category.assoc]
    have he : G'.map (ag'.homEquiv _ _ φ) ≫ ag'.counit.app K' = φ := by
      simpa only [Adjunction.homEquiv_symm_apply] using
        (ag'.homEquiv _ _).symm_apply_apply φ
    rw [he]

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
set_option cleanup.letToHave false
attribute [local irreducible] derivedPullback Functor.rightDerivedFunctor
  Functor.rightDerivedFunctorUnit DerivedCategory.Qh
set_option linter.all false in
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem global_arrow_transpose
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : CategoryTheory.IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') :
    let κ := relativeMVComp f' g ≪≫
      eqToIso (congrArg (fun t ↦ derivedPullback.{u, w} t) hpull.w.symm) ≪≫
      (relativeMVComp g' f).symm
    let δ := conjugateEquiv ((relativeMVAdj f).comp (relativeMVAdj g'))
      ((relativeMVAdj g).comp (relativeMVAdj f')) κ.hom
    (relativeMVAdj g).homEquiv _ _
        (relativeMVGlobalArrow f f' g g' hpull K K' φ).hom =
      (schemeDerivedDirectImage f).map ((relativeMVAdj g').homEquiv _ _ φ) ≫
        δ.app K' := by
  intro κ δ
  have he : schemeDerivedBaseChangeMap f f' g g' hpull.w K =
      (relativeMVAdj f').homEquiv _ _
        (κ.hom.app ((schemeDerivedDirectImage f).obj K) ≫
          (derivedPullback g').map ((relativeMVAdj f).counit.app K)) := by
    simp +instances only [schemeDerivedBaseChangeMap, relativeMVAdj, relativeMVComp, κ,
      Iso.trans_hom, Iso.symm_hom, Iso.app_hom, NatTrans.comp_app,
      eqToIso.hom, eqToHom_app, Category.assoc]
    rfl
  dsimp only [relativeMVGlobalArrow, Arrow.mk, Arrow.hom]
  rw [he]
  rw [← (relativeMVAdj f').homEquiv_naturality_right]
  simpa +instances only [Category.assoc, δ, Arrow.right] using
    square_conjugate_transpose (relativeMVAdj f) (relativeMVAdj g)
      (relativeMVAdj f') (relativeMVAdj g') κ φ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
-- The three vertex comparison types include composed derived and complex functors.
/-- Identify the three normalized roof maps with the prescribed base-change
arrows, after their denominator vertices are known invertible.
Source: Stacks Project, Tags 08FE, 08HY, 08HZ and 0D5T.
(blueprint: lem-pc-relative-mv-resolved-roof-mate-comparisons).
Proof: Compare Q(f_*I) with Rf_*K using the inverse K-injective computation
isomorphism followed by Rf_* of the resolution isomorphism. For an open W,
compare its open-image complex with Rj_* of exact restriction of K and then use
relativeMVExactOpenIso to pass to R(jf)_*Lj* K. Apply Lg* to the source
comparisons. On the target use the computation isomorphism for f'_*J and the
canonical inverse-open comparisons. The middle comparisons are the composite
of the localization and direct-image biproduct comparisons and the two open
comparisons. Naturality of direct-image localization at r and s cancels the
resolution maps from the roof. The composition comparison for pushforward
is the right-adjoint mate of the pinned derived-pullback composition comparison:
both are determined by their derived-unit equations. Expanding the counit of
the composite adjunction identifies the global roof map with the transpose of
the global base-change arrow. For W use the sectionwise open counit square,
the exact-open pullback comparison and inverse-open coefficient comparison.
Their mate equations identify the restricted roof map with the local
base-change arrow for W. Biproduct naturality combines W=U,V to give the
middle equation; W=U intersect V gives the third. This step constructs no
complex, chain map, exact sequence or quasi-isomorphism. It uses only the
normalized representatives supplied in the hypotheses, and the functorial
comparisons, so zero maps and empty or repeated opens need no exceptions. -/
theorem relativeMV_resolved_roof_mate_comparisons
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U V : X.Opens)
    (r : schemeMVResolution X K ⟶
      schemeMVResolution X ((schemeDerivedDirectImage g').obj K'))
    (s : ((RingedSpace.moduleDirectImage g'.toLRSHom.toShHom).mapHomologicalComplex
        (.up ℤ)).obj (schemeMVResolution X' K') ⟶
      schemeMVResolution X ((schemeDerivedDirectImage g').obj K'))
    (u₀ : schemeMayerVietorisComplex X U V (schemeMVResolution X K) ⟶
      schemeMayerVietorisComplex X U V
        (schemeMVResolution X ((schemeDerivedDirectImage g').obj K')))
    (hr : DerivedCategory.Q.map r = (schemeMVResolutionIso X K).hom ≫
      (relativeMVAdj g').homEquiv _ _ φ ≫
      (schemeMVResolutionIso X ((schemeDerivedDirectImage g').obj K')).inv)
    (hs : DerivedCategory.Q.map s =
      (schemeMVDirectImageLocalization g').app (schemeMVResolution X' K') ≫
      (schemeDerivedDirectImage g').map (schemeMVResolutionIso X' K').hom ≫
      (schemeMVResolutionIso X ((schemeDerivedDirectImage g').obj K')).inv)
    (hu₁ : u₀.τ₁ = r)
    (hu₂ : u₀.τ₂ = biprod.map
      (((schemeOpenModuleImage X U).mapHomologicalComplex (.up ℤ)).map r)
      (((schemeOpenModuleImage X V).mapHomologicalComplex (.up ℤ)).map r))
    (hu₃ : u₀.τ₃ =
      ((schemeOpenModuleImage X (U ⊓ V)).mapHomologicalComplex (.up ℤ)).map r) :
    let I := schemeMVResolution X K
    let J := schemeMVResolution X' K'
    let L := schemeMVResolution X ((schemeDerivedDirectImage g').obj K')
    let Ff := (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)
    let Ff' := (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)
    let A := (schemeMayerVietorisComplex X U V I).map Ff
    let R := (schemeMayerVietorisComplex X U V L).map Ff
    let B := (schemeMayerVietorisComplex X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) J).map Ff'
    let G := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
    let F := G.mapHomologicalComplex (.up ℤ)
    let η := schemeMVDirectImageLocalization g
    let adj := relativeMVAdj g
    let a := relativeMVGlobalArrow f f' g g' hpull K K' φ
    let b := relativeMVLocalArrow f f' g g' hpull K K' φ
    let c := (Functor.mapHomologicalComplexCompIso
        (directImageSquareIso g' f f' g hpull.w) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom ⋙
          RingedSpace.moduleDirectImage g.toLRSHom.toShHom)) (.up ℤ)).symm).symm
    let D := schemeMayerVietorisComplex X' (g' ⁻¹ᵁ U) (g' ⁻¹ᵁ V) J
    let u : A ⟶ R := Ff.mapShortComplex.map u₀
    let v : B.map F ⟶ R := (D.mapNatIso c).hom ≫
      Ff.mapShortComplex.map (schemeMVImageChainMap g' U V J L s)
    ∀ (hv₁ : IsIso (DerivedCategory.Q.map v.τ₁))
      (hv₂ : IsIso (DerivedCategory.Q.map v.τ₂))
      (hv₃ : IsIso (DerivedCategory.Q.map v.τ₃)),
      letI := hv₁
      letI := hv₂
      letI := hv₃
    ∃ (e₁ : (derivedPullback g).obj (DerivedCategory.Q.obj A.X₁) ≅ a.left)
      (e₂ : (derivedPullback g).obj (DerivedCategory.Q.obj A.X₂) ≅
        (b U).left ⊞ (b V).left)
      (e₃ : (derivedPullback g).obj (DerivedCategory.Q.obj A.X₃) ≅ (b (U ⊓ V)).left)
      (e₁' : DerivedCategory.Q.obj B.X₁ ≅ a.right)
      (e₂' : DerivedCategory.Q.obj B.X₂ ≅ (b U).right ⊞ (b V).right)
      (e₃' : DerivedCategory.Q.obj B.X₃ ≅ (b (U ⊓ V)).right),
      (DerivedCategory.Q.map u.τ₁ ≫ inv (DerivedCategory.Q.map v.τ₁) ≫ η.app B.X₁ =
        (adj.homEquiv _ _) (e₁.hom ≫ a.hom ≫ e₁'.inv)) ∧
      (DerivedCategory.Q.map u.τ₂ ≫ inv (DerivedCategory.Q.map v.τ₂) ≫ η.app B.X₂ =
        (adj.homEquiv _ _) (e₂.hom ≫ biprod.map (b U).hom (b V).hom ≫ e₂'.inv)) ∧
      (DerivedCategory.Q.map u.τ₃ ≫ inv (DerivedCategory.Q.map v.τ₃) ≫ η.app B.X₃ =
        (adj.homEquiv _ _) (e₃.hom ≫ (b (U ⊓ V)).hom ≫ e₃'.inv)) := by
  classical
  extract_lets (descend := false) I J L Ff Ff' A R B G F η adj a b c D u v
  intro hv₁ hv₂ hv₃
  have := hv₁
  have := hv₂
  have := hv₃
  let eI := schemeMVResolutionIso X K
  let eJ := schemeMVResolutionIso X' K'
  let eL := schemeMVResolutionIso X ((schemeDerivedDirectImage g').obj K')
  let t := (RingedSpace.derivedModuleDirectImageKInjectiveIso
    f.toLRSHom.toShHom I).symm ≪≫ (schemeDerivedDirectImage f).mapIso eI
  let t' := (RingedSpace.derivedModuleDirectImageKInjectiveIso
    f'.toLRSHom.toShHom J).symm ≪≫ (schemeDerivedDirectImage f').mapIso eJ
  let e₁ := (derivedPullback g).mapIso t
  let e₁' := t'
  have hroof := relativeMV_normalized_coefficient_roof f f' g g' hpull.w K K'
    I L J eI eJ eL ((relativeMVAdj g').homEquiv _ _ φ) r s hr hs hv₁
  have hglobal := global_arrow_transpose f f' g g' hpull K K' φ
  have h₁ : DerivedCategory.Q.map u.τ₁ ≫ inv (DerivedCategory.Q.map v.τ₁) ≫
      η.app B.X₁ = adj.homEquiv _ _ (e₁.hom ≫ a.hom ≫ e₁'.inv) := by
    change DerivedCategory.Q.map (Ff.map u₀.τ₁) ≫
      inv (DerivedCategory.Q.map v.τ₁) ≫ η.app B.X₁ =
      adj.homEquiv _ _ (e₁.hom ≫ a.hom ≫ e₁'.inv) 
    rw [hu₁]
    change DerivedCategory.Q.map (Ff.map r) ≫
      inv (DerivedCategory.Q.map v.τ₁) ≫ η.app (Ff'.obj J) =
      adj.homEquiv _ _ ((derivedPullback g).map t.hom ≫ a.hom ≫ t'.inv)
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
    rw [hglobal]
    have hvc : v.τ₁ = c.hom.app J ≫ Ff.map s := rfl
    simpa only [hvc, c, Iso.symm_hom, e₁, e₁', t, t', eI, eJ, eL, Category.assoc,
      Functor.mapIso_hom] using hroof
  obtain ⟨e₂, e₃, e₂', e₃', h₂, h₃⟩ :=
    relativeMV_resolved_roof_open_mate_comparisons f f' g g' hpull K K' φ U V
      r s u₀ hr hs hu₂ hu₃ hv₂ hv₃
  exact ⟨e₁, e₂, e₃, e₁', e₂', e₃', h₁, h₂, h₃⟩

end AlgebraicGeometry
