/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionModelOrientationDefinitions
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Model.ModelChartOrientationLeftOpen
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Model.ModelChartOrientationRightOpen
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Model.ModelOrientationTateDetection
/-! # Descent of the beta-delta equation from compatible affine charts -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

private theorem mapIso_eq_of_natIso {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D) (e : F ≅ G) {X Y : C} (a b : X ≅ Y)
    (h : F.mapIso a = F.mapIso b) : G.mapIso a = G.mapIso b := by
  apply Iso.ext
  apply (cancel_epi (e.hom.app X)).1
  simp only [Functor.mapIso_hom]
  rw [← e.hom.naturality, ← e.hom.naturality]
  exact congrArg (fun z ↦ z ≫ e.hom.app Y) (congrArg Iso.hom h)

/-- Beta-delta identities on all affine triples admitting compatible coordinates
imply the equation on every affine triple.
Source: model descent Steps 8--9.
(blueprint: lem-pur-model-chart-orientation-affine-descent).

Proof: for each point of U use composition_compatible_affine_charts to choose
affine opens U', V', T' and etale coordinates for the two restricted morphisms.
Apply hlocal to these restricted morphisms and the restricted structure map.
Write the two global composites in ModelChartOrientationEquation as L and R.
Both are isomorphisms with target the shifted Tate line on U, so form the
automorphism R.symm followed by L. The open restriction squares for diagonal
section pasting, normalized DNC invariance and normal-bundle orientation,
together with the canonical tensor and Tate pullback comparisons, identify
its restriction to U' with the quotient of the corresponding local composites.
The local equation makes that quotient the identity. Apply the injectivity
clause of model_orientation_tate_detection on the covering by the U'. Cancel
R.symm to obtain L = R. This argument is for each twist transport t separately;
the local hypothesis supplies the equation for every t. If U is empty take the
empty open cover; the same injectivity clause still applies. Empty coordinate
blocks in rank zero use the tensor-unit and empty-frame comparisons.
-/
theorem model_chart_orientation_affine_descent (P : PurityFiniteSetting.{u})
    {U V T : Scheme.{u}} [IsAffine U] [IsAffine V] [IsAffine T]
    (d e : ℕ) (f : U ⟶ V) (g : V ⟶ T)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aT : T ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aT] [QuasiCompact aT]
    (hlocal : ∀ (U' V' T' : Scheme.{u}) [IsAffine U'] [IsAffine V'] [IsAffine T']
      (f' : U' ⟶ V') (g' : V' ⟶ T')
      [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
      [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
      [SmoothOfRelativeDimension d f'] [SmoothOfRelativeDimension e g']
      (aT' : T' ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aT'] [QuasiCompact aT']
      (x : U' ⟶ DiagonalPasting.A d V') (y : V' ⟶ DiagonalPasting.A e T')
      [Etale x] [Etale y]
      (_hx : x ≫ DiagonalPasting.pr d V' = f')
      (_hy : y ≫ DiagonalPasting.pr e T' = g'),
      ModelChartOrientationEquation P d e f' g' aT') :
    ModelChartOrientationEquation P d e f g aT := by
  classical
  let := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
  choose Os Vs Ts hOs hVs hTs hmem hcharts using
    composition_compatible_affine_charts P d e f g aT
  have hcover : iSup Os = ⊤ := by
    apply top_unique
    intro z _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hmem z⟩
  intro t
  let A := P.modelChartLeft d e f g aT t
  let B := P.modelChartRight d e f g aT t
  have hdetect := model_orientation_tate_detection.{u, u} P U (f ≫ g ≫ aT) (d + e)
  have hquot : B.symm ≪≫ A = Iso.refl _ := by
    apply hdetect.2.2 U Os hcover
    funext z
    obtain ⟨hUV, hVT, x, y, hxet, hyet, hx, hy, _, hfd, hge, hfs, hgs,
      hfl, hfq, hgl, hgq, hTl, hTq⟩ := hcharts z
    have : IsAffine (Os z).toScheme := hOs z
    have : IsAffine (Vs z).toScheme := hVs z
    have : IsAffine (Ts z).toScheme := hTs z
    let := hxet
    let := hyet
    let := hfd
    let := hge
    let := hfs
    let := hgs
    let := hfl
    let := hfq
    let := hgl
    let := hgq
    let := hTl
    let := hTq
    let f' := f.resLE (Vs z) (Os z) hUV
    let g' := g.resLE (Ts z) (Vs z) hVT
    have hf : (Os z).ι ≫ f = f' ≫ (Vs z).ι :=
      (Scheme.Hom.resLE_comp_ι f hUV).symm
    have hg : (Vs z).ι ≫ g = g' ≫ (Ts z).ι :=
      (Scheme.Hom.resLE_comp_ι g hVT).symm
    have hl := model_chart_orientation_left_open P d e f g f' g'
      (Os z).ι (Vs z).ι (Ts z).ι hf hg aT t
    have hr := model_chart_orientation_right_open P d e f g f' g'
      (Os z).ι (Vs z).ι (Ts z).ι hf hg aT t
    have heq := hlocal (Os z).toScheme (Vs z).toScheme (Ts z).toScheme
      f' g' ((Ts z).ι ≫ aT) x y hx hy
    have hab : P.modelChartLeft d e f' g' ((Ts z).ι ≫ aT) t =
        P.modelChartRight d e f' g' ((Ts z).ι ≫ aT) t := by
      have := congrArg (fun k ↦ (P.compatibleKappa d e f' g' ((Ts z).ι ≫ aT)).symm ≪≫ k)
        (heq t)
      simpa only [modelChartLeft, modelChartRight, Iso.symm_self_id_assoc] using this
    rw [hab] at hl
    have hres := congrArg
      (fun k ↦ k ≪≫ (P.modelOrientationTwistPullback (Os z).ι
        (f ≫ g ≫ aT) (d + e)).symm) (hl.trans hr.symm)
    simp only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] at hres
    let R := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) (Os z).ι)
    have hmap : R.mapDerivedCategory.mapIso A = R.mapDerivedCategory.mapIso B :=
      mapIso_eq_of_natIso R.leftDerivedFunctor R.mapDerivedCategory
        (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory _ (Os z).ι) A B hres
    change R.mapDerivedCategory.mapIso (B.symm ≪≫ A) =
      R.mapDerivedCategory.mapIso (Iso.refl _)
    rw [Functor.mapIso_trans, Functor.mapIso_symm, hmap,
      Iso.symm_self_id, Functor.mapIso_refl]
  have hab := congrArg (fun k ↦ B ≪≫ k) hquot
  have hAB : A = B := by
    simpa only [Iso.self_symm_id_assoc, Iso.trans_refl] using hab
  have h := congrArg (fun k ↦ P.compatibleKappa d e f g aT ≪≫ k) hAB
  simpa only [A, B, modelChartLeft, modelChartRight, Iso.self_symm_id_assoc] using h

end WeilConjectures.PurityFiniteSetting
