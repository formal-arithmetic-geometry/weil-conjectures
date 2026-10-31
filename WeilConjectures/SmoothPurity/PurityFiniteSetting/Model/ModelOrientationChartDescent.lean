/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionModelOrientationDefinitions
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Model.ModelOrientationAlphaPasting
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Model.ModelOrientationQuotientRestriction

/-! # A step of the model orientation descent argument -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u w v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

private theorem chartBifunctorIso_trans
    {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (T : C ⥤ D ⥤ E) {A A' A'' : C} {B B' B'' : D}
    (a : A ≅ A') (a' : A' ≅ A'') (b : B ≅ B') (b' : B' ≅ B'') :
    compatibleBifunctorIso T a b ≪≫ compatibleBifunctorIso T a' b' =
      compatibleBifunctorIso T (a ≪≫ a') (b ≪≫ b') := by
  ext
  simp only [compatibleBifunctorIso, Functor.mapIso_trans, NatIso.trans_app, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc]
  change (T.map a.hom).app B ≫ (T.obj A').map b.hom ≫
    (T.map a'.hom).app B' ≫ (T.obj A'').map b'.hom =
      (T.map a.hom).app B ≫ (T.map a'.hom).app B ≫
        (T.obj A'').map b.hom ≫ (T.obj A'').map b'.hom
  rw [(T.map a'.hom).naturality_assoc]

private theorem cancel_chart_factors
    {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (T : C ⥤ D ⥤ E) {A A' L₁ : C} {B B' L₂ : D} {K K' L : E}
    (a : A ≅ A') (b : B ≅ B') (c : K ≅ K')
    (p : A ≅ L₁) (q : B ≅ L₂) (r : K ≅ L)
    (κ : (T.obj A).obj B ≅ K) (σ : (T.obj A').obj B' ⟶ K')
    (μ : (T.obj L₁).obj L₂ ≅ L)
    (hα : κ.hom ≫ c.hom = (compatibleBifunctorIso T a b).hom ≫ σ)
    (hβ : κ ≪≫ r = compatibleBifunctorIso T p q ≪≫ μ) :
    σ ≫ (c.symm ≪≫ r).hom =
      (compatibleBifunctorIso T (a.symm ≪≫ p) (b.symm ≪≫ q)).hom ≫ μ.hom := by
  apply (cancel_epi (compatibleBifunctorIso T a b).hom).mp
  have hT : compatibleBifunctorIso T a b ≪≫
      compatibleBifunctorIso T (a.symm ≪≫ p) (b.symm ≪≫ q) =
      compatibleBifunctorIso T p q := by
    rw [chartBifunctorIso_trans]
    simp
  calc
    _ = κ.hom ≫ r.hom := by
      simp only [Iso.trans_hom, Iso.symm_hom]
      rw [← Category.assoc, ← hα]
      simp
    _ = (compatibleBifunctorIso T p q).hom ≫ μ.hom := congrArg Iso.hom hβ
    _ = _ := by
      have h := congrArg Iso.hom hT
      simpa only [Iso.trans_hom, Category.assoc] using
        congrArg (fun k ↦ k ≫ μ.hom) h.symm

private theorem hom_eq_of_aut_restriction
    {C : Type u₁} [Category.{v₁} C] {I : Type u₂}
    {D : I → Type u₃} [∀ i, Category.{v₂} (D i)]
    (F : ∀ i, C ⥤ D i) {K L : C} (a : K ⟶ L) [IsIso a] (b : K ≅ L)
    (hinj : Function.Injective (fun e : Aut L ↦ fun i ↦ (F i).mapIso e))
    (hlocal : ∀ i, (F i).map a = (F i).map b.hom) : a = b.hom := by
  have hquot : b.symm ≪≫ asIso a = Iso.refl L := by
    apply hinj
    funext i
    apply Iso.ext
    simp only [Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom, asIso_hom,
      Functor.map_comp, hlocal i, Iso.refl_hom]
    rw [← (F i).map_comp, b.inv_hom_id, (F i).map_id]
  have h := congrArg Iso.hom hquot
  change b.inv ≫ a = 𝟙 L at h
  simpa using (Iso.inv_comp_eq b).mp h

private theorem orientation_hom_ext (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) [CompactSpace X] (r : ℕ)
    {K : _root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))}
    (a : K ⟶ P.diagonalTwist X r) [IsIso a] (b : K ≅ P.diagonalTwist X r)
    (hdetect : ModelOrientationDetection.{u, w} P X r)
    (hlocal : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) U.ι).mapDerivedCategory.map a =
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) U.ι).mapDerivedCategory.map
          b.hom) : a = b.hom := by
  classical
  choose U hx hU using hlocal
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X ↦ (U x : Set X)) (fun x ↦ (U x).isOpen) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, hx x⟩)
  let C : ULift.{w} (Fin s.card) → X.Opens :=
    fun i ↦ U (s.equivFin.symm i.down).val
  have hcover : iSup C = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ x))
    obtain ⟨his, hxi⟩ := Set.mem_iUnion.mp hi
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨ULift.up (s.equivFin ⟨i, his⟩), ?_⟩
    change x ∈ (U (s.equivFin.symm (s.equivFin ⟨i, his⟩)).val : Set X)
    rw [Equiv.symm_apply_apply]
    exact hxi
  apply hom_eq_of_aut_restriction
    (fun i ↦ (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (C i).ι).mapDerivedCategory) a b (hdetect.2.2 _ C hcover)
  intro i
  exact hU _

private theorem affine_orientation_eq (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aZ : Z ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    (hchart : ModelChartOrientationEquation P d e f g aZ) :
    letI := P.noetherian aZ
    letI := P.noetherian (g ≫ aZ)
    letI := Dnc.compactifiable P f (g ≫ aZ)
    letI := Dnc.compactifiable P g aZ
    letI := Dnc.compactifiable P (f ≫ g) aZ
    letI := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
    letI : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
    letI := ProEtale.upperStarPreservesFlat_moduleCat P.Coefficient
    ProEtale.CompositionTensorMate.sigma P.Coefficient f g ≫
        (P.modelOrientation (d + e) (f ≫ g) aZ).hom =
      (P.compatibleTensorIso (P.modelOrientation d f (g ≫ aZ))
        ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
          (P.modelOrientation e g aZ))).hom ≫
        (P.modelOrientationMu d e f (g ≫ aZ)).hom := by
  let := P.noetherian aZ
  let := P.noetherian (g ≫ aZ)
  let := Dnc.compactifiable P f (g ≫ aZ)
  let := Dnc.compactifiable P g aZ
  let := Dnc.compactifiable P (f ≫ g) aZ
  let := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
  let : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
  let := ProEtale.upperStarPreservesFlat_moduleCat P.Coefficient
  let t := Etale.projectiveLineTraceTransport P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level)
      P.Coefficient P.diagonalExponent_annihilates
  have h := cancel_chart_factors (P.compatibleTensor X)
    (P.chartDiagonalAlpha d f (g ≫ aZ) ≪≫ (P.modelOrientationUnit f).symm)
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
      (P.chartDiagonalAlpha e g aZ ≪≫ (P.modelOrientationUnit g).symm))
    (P.chartDiagonalAlpha (d + e) (f ≫ g) aZ ≪≫
      (P.modelOrientationUnit (f ≫ g)).symm)
    (P.chartDiagonalDelta d f (g ≫ aZ) ≪≫ P.chartDiagonalBeta d f (g ≫ aZ) t)
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
      (P.chartDiagonalDelta e g aZ ≪≫ P.chartDiagonalBeta e g aZ t))
    (P.chartDiagonalDelta (d + e) (f ≫ g) aZ ≪≫
      P.chartDiagonalBeta (d + e) (f ≫ g) aZ t)
    (P.compatibleKappa d e f g aZ)
    (ProEtale.CompositionTensorMate.sigma P.Coefficient f g)
    (P.modelOrientationMu d e f (g ≫ aZ))
    (model_orientation_alpha_pasting P d e f g aZ) (hchart t)
  have hf := diagonal_dnc_chart_normalization P d f (g ≫ aZ) t
  have hg := diagonal_dnc_chart_normalization P e g aZ t
  have ht := diagonal_dnc_chart_normalization P (d + e) (f ≫ g) aZ t
  simpa only [modelOrientation, hf, hg, ht, chartDiagonalAssembly,
    Iso.trans_symm, Iso.symm_symm_eq, Functor.mapIso_trans, Functor.mapIso_symm,
    Iso.trans_assoc, compatibleTensorIso] using h

/-- The beta-delta identity on compatible affine charts gives the global orientation
equality once automorphisms of its Tate target are detected on open coverings.
Source: model descent Steps 7--9
(blueprint: lem-pur-model-orientation-chart-descent).

Proof: cover X by the compatible affine charts of f and g. On each chart the DNC
assembly identifies theta_h with beta_h delta_h alpha_h inverse, and identifies
alpha_(gf) kappa with sigma applied to the tensor of alpha_f and f*alpha_g.
Substitute the assumed beta-delta equation and cancel that invertible tensor of
alpha maps. Compatibility with open restriction makes this the restriction of the
global equality. The two sides are isomorphisms by composition_tensor_mate. Their
quotient is therefore an automorphism of the total Tate twist whose restrictions
are identities. The assumed detection gives the identity globally; cancel the
inverse of the right-hand side to obtain the displayed equality. For empty
X use the empty chart cover and the same detection hypothesis. -/
theorem model_orientation_chart_descent (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}}
    (d e : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (aZ : Z ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    (hchart : ∀ (U V T : Scheme.{u}) [IsAffine U] [IsAffine V] [IsAffine T]
      (f' : U ⟶ V) (g' : V ⟶ T)
      [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
      [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
      [SmoothOfRelativeDimension d f'] [SmoothOfRelativeDimension e g']
      (aT : T ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aT] [QuasiCompact aT],
        ModelChartOrientationEquation P d e f' g' aT)
    (hdetect : ModelOrientationDetection.{u, w} P X (d + e)) :
    letI := P.noetherian aZ
    letI := P.noetherian (g ≫ aZ)
    letI := Dnc.compactifiable P f (g ≫ aZ)
    letI := Dnc.compactifiable P g aZ
    letI := Dnc.compactifiable P (f ≫ g) aZ
    letI := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
    letI : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
    letI := ProEtale.upperStarPreservesFlat_moduleCat P.Coefficient
    ProEtale.CompositionTensorMate.sigma P.Coefficient f g ≫
        (P.modelOrientation (d + e) (f ≫ g) aZ).hom =
      (P.compatibleTensorIso (P.modelOrientation d f (g ≫ aZ))
        ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
          (P.modelOrientation e g aZ))).hom ≫
        (P.modelOrientationMu d e f (g ≫ aZ)).hom := by
  classical
  let := P.noetherian aZ
  let := P.noetherian (g ≫ aZ)
  let := P.noetherian (f ≫ g ≫ aZ)
  let := Dnc.compactifiable P f (g ≫ aZ)
  let := Dnc.compactifiable P g aZ
  let := Dnc.compactifiable P (f ≫ g) aZ
  let := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
  let : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
  let := ProEtale.upperStarPreservesFlat_moduleCat P.Coefficient
  let t := P.compatibleTensorIso
    (P.chartDiagonalAlpha d f (g ≫ aZ) ≪≫ (P.modelOrientationUnit f).symm)
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
      (P.chartDiagonalAlpha e g aZ ≪≫ (P.modelOrientationUnit g).symm))
  have hα := model_orientation_alpha_pasting P d e f g aZ
  have hσcomp : IsIso (t.hom ≫
      ProEtale.CompositionTensorMate.sigma P.Coefficient f g) := by
    dsimp only [t]
    rw [← hα]
    infer_instance
  let : IsIso (ProEtale.CompositionTensorMate.sigma P.Coefficient f g) :=
    (isIso_comp_left_iff t.hom _).mp hσcomp
  let a := ProEtale.CompositionTensorMate.sigma P.Coefficient f g ≫
    (P.modelOrientation (d + e) (f ≫ g) aZ).hom
  let b := P.compatibleTensorIso (P.modelOrientation d f (g ≫ aZ))
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.mapIso
      (P.modelOrientation e g aZ)) ≪≫ P.modelOrientationMu d e f (g ≫ aZ)
  change a = b.hom
  apply orientation_hom_ext P X (d + e) a b hdetect
  intro x
  obtain ⟨U, V, T, hU, hV, hT, hx, hUV, hVT, x', y', hex, hey, hfx, hgy,
    hcomp, hfd, hge, hfs, hgs, hfl, hfq, hgl, hgq, hTl, hTq⟩ :=
    composition_compatible_affine_charts P d e f g aZ x
  refine ⟨U, hx, ?_⟩
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : IsAffine T.toScheme := hT
  have := hfd
  have := hge
  have := hfs
  have := hgs
  have := hfl
  have := hfq
  have := hgl
  have := hgq
  have := hTl
  have := hTq
  let f' := f.resLE V U hUV
  let g' := g.resLE T V hVT
  let aT := T.ι ≫ aZ
  let := P.noetherian aT
  let := P.noetherian (g' ≫ aT)
  let := Dnc.compactifiable P f' (g' ≫ aT)
  let := Dnc.compactifiable P g' aT
  let := Dnc.compactifiable P (f' ≫ g') aT
  let := (DiagonalPasting.geometryProperties d e f' g').2.2.2.2
  let F := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) U.ι).mapDerivedCategory
  let J := ((ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} P.Coefficient) U.ι).app (P.diagonalTwist X (d + e))).symm ≪≫
      P.modelOrientationTwistPullback U.ι (f ≫ g ≫ aZ) (d + e)
  let a' := ProEtale.CompositionTensorMate.sigma P.Coefficient f' g' ≫
    (P.modelOrientation (d + e) (f' ≫ g') aT).hom
  let b' := P.compatibleTensorIso (P.modelOrientation d f' (g' ≫ aT))
    ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f').leftDerivedFunctor.mapIso
      (P.modelOrientation e g' aT)) ≪≫ P.modelOrientationMu d e f' (g' ≫ aT)
  have hl : a' = b'.hom := affine_orientation_eq P d e f' g' aT (hchart _ _ _ f' g' aT)
  have hr := model_orientation_quotient_restriction P d e f g f' g' U.ι V.ι T.ι
    (by simp [f']) (by simp [g']) aZ
  change F.map (b.inv ≫ a) ≫ J.hom = J.hom ≫ (b'.inv ≫ a') at hr
  rw [hl, Iso.inv_hom_id, Category.comp_id] at hr
  have hQ : F.map (b.inv ≫ a) = 𝟙 _ := by
    apply (cancel_mono J.hom).mp
    simpa using hr
  apply (cancel_epi (F.map b.inv)).mp
  change F.map b.inv ≫ F.map a = F.map b.inv ≫ F.map b.hom
  rw [← F.map_comp, ← F.map_comp, b.inv_hom_id, F.map_id]
  exact hQ

end WeilConjectures.PurityFiniteSetting
