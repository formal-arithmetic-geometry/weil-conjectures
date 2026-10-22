/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Paper.StrictQuotientDiagonalPresentation
import Sheaf.Paper.StrictQuotientOrdinaryFlatPresentation
import all Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.CategoryTheory.SystemEvaluationTopos

/-! # Strict quotient systems and the completion unit

Source: Stacks Project, sites-cohomology.tex, Tags 0940 and 0941;
proetale.tex, Tags 099M and 099N; the strict quotient auxiliary
(blueprint: lem-pur-strict-quotient-diagonal-normalization).

The existing sequence site, ring sheaves, scalar extension, quotient transitions,
ordinary derived categories and completion reflector are used throughout.

## Main definitions

* `strictDiagonalRing`, `strictQuotientRing`: the published ringed sequence-site models.
* `StrictQuotientDiagonalPresentation`: section-normalized ordinary comparison data.
* `StrictQuotientDiagonalPresentation.representative`: the canonical cochain comparison.

## Main statement

* `strictQuotientDiagonalNormalization`: all four clauses, with the unit equation.

Index n means the positive exponent n+1. The presentation below fixes every
ordinary comparison on sections, and every derived comparison on representatives.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.ConstantCompletion

attribute [local irreducible] derivedExtension strictLimit quotientPresentation
  HasDerivedCategory.standard Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  constantSheaf Functor.leftDerivedLift SheafOfModules.monoidalCategory DerivedCategory
  extendComparison reductionUnit reductionTower strictDiagonalRing strictQuotientRing
  StrictQuotientDiagonalPresentation.diagonalD
  StrictQuotientDiagonalPresentation.restrictionD StrictQuotientDiagonalPresentation.reductionD

attribute [local instance 2000] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (A : Type u) [CommRing A] (I : Ideal A)

private theorem assemble_normalization
    {D₀ : Type*} {S₀ : D₀ → Prop} {I₀ E₀ B₀ : D₀ → Type*}
    {L₀ T₀ : Type*} {G₀ : ∀ d, I₀ d → E₀ d → Prop}
    {P₀ : ∀ d, I₀ d → L₀ → B₀ d → T₀ → Prop}
    (ordinary : ∃ d, S₀ d)
    (comparison : ∀ d, S₀ d → ∃ i e, G₀ d i e)
    (ell : L₀) (completion : ∀ d, E₀ d → B₀ d) (literal : T₀)
    (finish : ∀ d, S₀ d → ∀ i e, G₀ d i e →
      P₀ d i ell (completion d e) literal) :
    ∃ d i ell completion literal, P₀ d i ell completion literal := by
  obtain ⟨d, hd⟩ := ordinary
  obtain ⟨i, e, he⟩ := comparison d hd
  exact ⟨d, i, ell, completion d e, literal, finish d hd i e he⟩

private structure StrictConstantModel (O : Sheaf J CommRingCat.{u}) where
  functor : D O ⥤ TD O
  factors : Q O ⋙ functor ≅
    (constantTower J O).mapHomologicalComplex (.up ℤ) ⋙ TQ O

private def strict_constantModel (O : Sheaf J CommRingCat.{u}) : StrictConstantModel J O where
  functor := (constantTower J O).mapDerivedCategory
  factors := (constantTower J O).mapDerivedCategoryFactors

private theorem flatOnSite_flat {O : Sheaf J CommRingCat.{u}} (M : Mod O)
    (h : SheafOfModules.IsFlatOnSite (J := J) (R := O) M) : M.IsFlat :=
  (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso O M) h

private theorem strict_restriction_exact (d : StrictQuotientDiagonalPresentation J A I) :
    PreservesFiniteLimits d.restriction ∧ PreservesFiniteColimits d.restriction := by
  have := (siteRestrictScalars_exact d.ringMap).1
  have := (siteRestrictScalars_exact d.ringMap).2
  exact ⟨inferInstance, inferInstance⟩

private theorem strict_restriction_conservative
    (d : StrictQuotientDiagonalPresentation J A I)
    {V W : D (strictQuotientRing J A I)} (f : V ⟶ W)
    (hf : IsIso (d.restrictionD.map f)) : IsIso f := by
  unfold StrictQuotientDiagonalPresentation.restrictionD at hf
  rw [d.restrictionModel_eq] at hf
  let := hf
  have : (res d.ringMap).mapDerivedCategory.ReflectsIsomorphisms := by
    exact siteDerivedRestrictScalars_reflectsIsomorphisms d.ringMap
  have : d.towers.functor.mapDerivedCategory.ReflectsIsomorphisms := inferInstance
  have : IsIso (d.towers.functor.mapDerivedCategory.map
      ((res d.ringMap).mapDerivedCategory.map f)) := hf
  have : IsIso ((res d.ringMap).mapDerivedCategory.map f) :=
    isIso_of_reflects_iso _ d.towers.functor.mapDerivedCategory
  exact isIso_of_reflects_iso f (res d.ringMap).mapDerivedCategory

set_option maxHeartbeats 50000 in
-- Explicit comparison factors avoid unfolding the localization.
private theorem strict_representative_isIso
    (d : StrictQuotientDiagonalPresentation J A I) (P : Cx (constant J A))
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := strictDiagonalRing J A)
      ((d.diagonal.mapHomologicalComplex (.up ℤ)).obj P)) :
    IsIso (d.representative P) := by
  have : IsIso ((extendComparison d.ringMap).app
      ((d.diagonal.mapHomologicalComplex (.up ℤ)).obj P)) :=
    by
      unfold extendComparison
      exact (derivedExtension d.ringMap).computation _
        ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1 hP)
  exact d.representative_isIso_of_comparison P

attribute [local irreducible] StrictQuotientDiagonalPresentation.representative

private theorem strict_constant_kInjective (O : Sheaf J CommRingCat.{u}) (P : Cx O)
    (hP : P.IsKInjective) :
    CochainComplex.IsKInjective
      (((constantTower J O).mapHomologicalComplex (.up ℤ)).obj P) := by
  let adj₀ : (evaluation ℕᵒᵖ (Mod O)).obj (op 0) ⊣
      constantTower J O :=
    { unit :=
        { app := fun M ↦
            { app := fun n ↦ M.map (homOfLE (Nat.zero_le n.unop)).op
              naturality := by
                intro i j f
                change M.map f ≫ M.map _ = M.map _ ≫ 𝟙 _
                rw [Category.comp_id, ← M.map_comp]
                congr 1 }
          naturality := by
            intro M N f
            apply NatTrans.ext
            funext n
            exact (f.naturality _).symm }
      counit := 𝟙 _
      left_triangle_components := by intro M; simp
      right_triangle_components := by intro M; ext n; simp }
  let := adj₀.preservesKInjectiveComplexes
  let := hP
  infer_instance

private theorem strict_flat_representative (O : Sheaf J CommRingCat.{u}) (V : D O) :
    ∃ (P : Cx O) (_e : (Q O).obj P ≅ V),
      CochainComplex.IsKFlatIndependentCoefficients (R := O) P ∧
        (∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := O) (P.X q)) := by
  let G := (Q O).objPreimage V
  let e := (Q O).objObjPreimageIso V
  obtain ⟨P, f, hP, hf, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := O) G
  let := hq
  refine ⟨P, asIso ((Q O).map f) ≪≫ e, hP, ?_⟩
  intro q
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso O (P.X q)).symm (hf q)

private def strict_literalLimitIso (O : Sheaf J CommRingCat.{u}) :
    (constantTower J O).mapHomologicalComplex (.up ℤ) ⋙
      ordinaryLimit O ≅ 𝟭 (Cx O) := by
  have : (lim : (ℕᵒᵖ ⥤ Mod O) ⥤ Mod O).Additive :=
    Functor.additive_of_preserves_binary_products _
  let a : constantTower J O ⊣
      (lim : (ℕᵒᵖ ⥤ Mod O) ⥤ Mod O) := constLimAdj
  have : IsIso a.unit := a.unit_isIso_of_L_fully_faithful
  exact Functor.mapHomologicalComplexCompIso (asIso a.unit).symm (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ _

private theorem strict_literalLimitIso_f (O : Sheaf J CommRingCat.{u}) (P : Cx O) (q : ℤ) :
    ((strict_literalLimitIso J O).app P).hom.f q =
      limit.π ((constantTower J O).obj (P.X q)) (op 0) := by
  have : (lim : (ℕᵒᵖ ⥤ Mod O) ⥤ Mod O).Additive :=
    Functor.additive_of_preserves_binary_products _
  let a : constantTower J O ⊣
      (lim : (ℕᵒᵖ ⥤ Mod O) ⥤ Mod O) := constLimAdj
  have : IsIso a.unit := a.unit_isIso_of_L_fully_faithful
  change (asIso a.unit).inv.app (P.X q) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  apply (cancel_epi (a.unit.app (P.X q))).1
  simp [a, constLimAdj]

private theorem strict_literalLimitIso_inv_f (O : Sheaf J CommRingCat.{u}) (P : Cx O) (q : ℤ) :
    ((strict_literalLimitIso J O).inv.app P).f q =
      constLimAdj.unit.app (P.X q) := by
  change 𝟙 _ ≫ constLimAdj.unit.app (P.X q) = _
  exact Category.id_comp _

attribute [local irreducible] strict_literalLimitIso

private def strict_constantLimitUnit (O : Sheaf J CommRingCat.{u})
    (k : StrictConstantModel J O) : 𝟭 (D O) ⟶
    k.functor ⋙ rlim O := by
  let q := Q O
  let F := k.functor ⋙ rlim O
  let τ : q ⋙ 𝟭 _ ⟶ q ⋙ F :=
    Functor.whiskerRight (strict_literalLimitIso J O).inv q ≫
      Functor.whiskerLeft
        ((constantTower J O).mapHomologicalComplex (.up ℤ))
        (limitComparison O) ≫
      Functor.whiskerRight k.factors.inv
        (rlim O)
  exact (Localization.fullyFaithfulWhiskeringLeft q
    (HomologicalComplex.quasiIso (Mod O) (.up ℤ)) _).preimage τ

private theorem strict_constantLimitUnit_app (O : Sheaf J CommRingCat.{u})
    (k : StrictConstantModel J O) (P : Cx O) :
    (strict_constantLimitUnit J O k).app ((Q O).obj P) =
      (Q O).map ((strict_literalLimitIso J O).inv.app P) ≫
        (limitComparison O).app
          (((constantTower J O).mapHomologicalComplex (.up ℤ)).obj P) ≫
        (rlim O).map
          (k.factors.inv.app P) := by
  exact NatTrans.congr_app
    ((Localization.fullyFaithfulWhiskeringLeft (Q O)
      (HomologicalComplex.quasiIso (Mod O) (.up ℤ)) _).map_preimage _) P

attribute [local irreducible] strict_constantLimitUnit

private theorem strict_constantLimitUnit_isIso (O : Sheaf J CommRingCat.{u})
    (k : StrictConstantModel J O) :
    IsIso (strict_constantLimitUnit J O k) := by
  have hcomp (P : Cx O) (hP : P.IsKInjective) :
      IsIso ((strict_constantLimitUnit J O k).app ((Q O).obj P)) := by
    rw [strict_constantLimitUnit_app]
    have : IsIso ((limitComparison O).app
        (((constantTower J O).mapHomologicalComplex (.up ℤ)).obj P)) :=
      (strictLimit O).computation _ (strict_constant_kInjective J O P hP)
    infer_instance
  obtain ⟨R, η, hR⟩ :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u, u, u}
      J O).2.2
  have hi (V : D O) : IsIso ((strict_constantLimitUnit J O k).app V) := by
    let P := (Q O).objPreimage V
    let e := (Q O).objObjPreimageIso V
    have := (hR P).1
    have h := hcomp (R.obj P) (hR P).2.1
    have hn := (strict_constantLimitUnit J O k).naturality ((Q O).map (η.app P))
    dsimp only [Functor.id_map, Functor.id_obj] at hn
    have hs : IsIso ((strict_constantLimitUnit J O k).app ((Q O).obj P)) := by
      rw [← isIso_comp_right_iff _
        ((k.functor ⋙ rlim O).map
          ((Q O).map (η.app P))), ← hn]
      infer_instance
    exact (NatTrans.isIso_app_iff_of_iso (strict_constantLimitUnit J O k) e).1 hs
  exact NatIso.isIso_of_isIso_app _

private theorem strict_resolving_ext (O : Sheaf J CommRingCat.{u})
    {F G : D O ⥤ D O} (α β : F ⟶ G)
    (h : ∀ P : Cx O,
      CochainComplex.IsKFlatIndependentCoefficients (R := O) P →
      (∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := O) (P.X q)) →
      α.app ((Q O).obj P) = β.app ((Q O).obj P)) : α = β := by
  ext V
  obtain ⟨P, e, hP, hf⟩ := strict_flat_representative J O V
  apply (cancel_epi (F.map e.hom)).1
  rw [α.naturality, β.naturality, h P hP hf]

private theorem resolvingComparison
    {A₀ D₀ D₁ : Type*} [Category A₀] [Category D₀] [Category D₁]
    (q : A₀ ⥤ D₀) (W : MorphismProperty A₀) [q.IsLocalization W]
    {R : A₀ ⥤ D₁} (T F : D₀ ⥤ D₁) (β : q ⋙ T ⟶ R) (α : q ⋙ F ⟶ R)
    [T.IsLeftDerivedFunctor β W] (S : A₀ → Prop)
    (hrep : ∀ V : D₀, ∃ P : A₀, Nonempty (q.obj P ≅ V) ∧ S P)
    (hβ : ∀ P, S P → IsIso (β.app P)) (hα : ∀ P, S P → IsIso (α.app P)) :
    ∃ e : F ≅ T, (Functor.whiskerLeft q e.hom ≫ β = α) ∧
      F.IsLeftDerivedFunctor α W := by
  let c := T.leftDerivedLift β W F α
  have hc : Functor.whiskerLeft q c ≫ β = α := T.leftDerived_fac β W F α
  have hi (V : D₀) : IsIso (c.app V) := by
    obtain ⟨P, ⟨e⟩, hP⟩ := hrep V
    have := hβ P hP
    have := hα P hP
    have : IsIso (c.app (q.obj P) ≫ β.app P) := by
      have hcP : c.app (q.obj P) ≫ β.app P = α.app P := by
        simpa only [NatTrans.comp_app, Functor.whiskerLeft_app] using NatTrans.congr_app hc P
      rw [hcP]
      infer_instance
    have : IsIso (c.app (q.obj P)) := IsIso.of_isIso_comp_right _ (β.app P)
    exact (NatTrans.isIso_app_iff_of_iso c e).1 this
  have : IsIso c := NatIso.isIso_of_isIso_app _
  exact ⟨asIso c, hc,
    (Functor.isLeftDerivedFunctor_iff_isIso_leftDerivedLift T β W F α).2 inferInstance⟩

private theorem comparison_whisker_app
    {A₀ D₀ D₁ D₂ : Type*} [Category A₀] [Category D₀]
    [Category D₁] [Category D₂]
    (q : A₀ ⥤ D₀) {F G : D₀ ⥤ D₁} {R : A₀ ⥤ D₁}
    (e : F ≅ G) (β : q ⋙ G ⟶ R) (α : q ⋙ F ⟶ R)
    (h : Functor.whiskerLeft q e.hom ≫ β = α) (H : D₁ ⥤ D₂) (X : A₀) :
    H.map (e.hom.app (q.obj X)) ≫ H.map (β.app X) =
      H.map (α.app X) := by
  rw [← H.map_comp]
  exact congrArg H.map (NatTrans.congr_app h X)

private def strict_augmentationComparison (k : StrictConstantModel J (constant J A)) :
    Q (constant J A) ⋙ k.functor ⟶
      (reductionTower J A I false).mapHomologicalComplex (.up ℤ) ⋙ TQ (constant J A) :=
  k.factors.hom ≫
    Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (reductionUnit J A I false) (.up ℤ))
      (TQ (constant J A))

attribute [local irreducible] strict_augmentationComparison

private theorem strict_quotient_comparison_isIso
    (p : QuotientPresentation J A I false) (P : Cx (constant J A))
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := constant J A) P)
    (hf : ∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := constant J A) (P.X q)) :
    IsIso (p.comparison.app P) :=
  p.laws.2.1 P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).1 hP)
    (fun q ↦ flatOnSite_flat J (P.X q) (hf q))

private theorem strict_reduction_comparison
    (p : QuotientPresentation J A I false)
    (k : StrictConstantModel J (constant J A))
    (d : StrictQuotientDiagonalPresentation J A I)
    (hdiag : ∀ P : Cx (constant J A),
      CochainComplex.IsKFlatIndependentCoefficients (R := constant J A) P →
      (∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := constant J A) (P.X q)) →
      CochainComplex.IsKFlatIndependentCoefficients (R := strictDiagonalRing J A)
        ((d.diagonal.mapHomologicalComplex (.up ℤ)).obj P)) :
    ∃ (i : k.functor ⟶
        d.reductionD ⋙ d.restrictionD)
      (e : d.reductionD ⋙ d.restrictionD ≅ p.tower),
      Functor.whiskerLeft (Q (constant J A)) e.hom ≫
        p.comparison = d.representativeTransformation ∧
      Functor.whiskerLeft (Q (constant J A)) i ≫ d.representativeTransformation =
        strict_augmentationComparison J A I k := by
  let T := p.tower
  let β : Q (constant J A) ⋙ T ⟶
      (reductionTower J A I false).mapHomologicalComplex (.up ℤ) ⋙ TQ (constant J A) :=
    p.comparison
  let F := d.reductionD ⋙ d.restrictionD
  let α := d.representativeTransformation
  let W := HomologicalComplex.quasiIso (Mod (constant J A)) (.up ℤ)
  have : (Q (constant J A)).IsLocalization W := by
    change (Q (constant J A)).IsLocalization
      (HomologicalComplex.quasiIso (Mod (constant J A)) (.up ℤ))
    infer_instance
  have : T.IsLeftDerivedFunctor β W := p.laws.1
  let S : Cx (constant J A) → Prop := fun P ↦
    CochainComplex.IsKFlatIndependentCoefficients (R := constant J A) P ∧
      ∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := constant J A) (P.X q)
  obtain ⟨e, he, hu⟩ := resolvingComparison (Q (constant J A)) W T F β α S
    (fun V ↦ by
      obtain ⟨P, e, hP, hf⟩ := strict_flat_representative J (constant J A) V
      exact ⟨P, ⟨e⟩, hP, hf⟩)
    (fun P h ↦ strict_quotient_comparison_isIso J A I p P h.1 h.2)
    (fun P h ↦ by
      have h := strict_representative_isIso J A I d P (hdiag P h.1 h.2)
      unfold StrictQuotientDiagonalPresentation.representative at h
      exact h)
  have : F.IsLeftDerivedFunctor α W := hu
  let i := F.leftDerivedLift α W
    k.functor (strict_augmentationComparison J A I k)
  refine ⟨i, e, ?_, ?_⟩
  · exact he
  · exact F.leftDerived_fac α W _ (strict_augmentationComparison J A I k)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinary_unit_factorization (O : Sheaf J CommRingCat.{u})
    (T : Mod O ⥤ (ℕᵒᵖ ⥤ Mod O)) [T.Additive]
    (η : constantTower J O ⟶ T) (P : Cx O)
    (μ : P ⟶ (ordinaryLimit O).obj ((T.mapHomologicalComplex (.up ℤ)).obj P))
    (hμ : ∀ q n, μ.f q ≫ limit.π (T.obj (P.X q)) (op n) = (η.app (P.X q)).app (op n)) :
    (strict_literalLimitIso J O).inv.app P ≫ (ordinaryLimit O).map
      ((NatTrans.mapHomologicalComplex η (.up ℤ)).app P) = μ := by
  have : (lim : (ℕᵒᵖ ⥤ Mod O) ⥤ Mod O).Additive :=
    Functor.additive_of_preserves_binary_products _
  ext1 q
  apply limit.hom_ext
  intro n
  change (((strict_literalLimitIso J O).inv.app P).f q ≫ limMap (η.app (P.X q))) ≫
    limit.π _ n = μ.f q ≫ limit.π _ n
  rw [Category.assoc, limMap_π, ← Category.assoc, strict_literalLimitIso_inv_f]
  change (limit.lift _ { pt := P.X q, π := 𝟙 _ } ≫ limit.π _ n) ≫ _ = _
  rw [limit.lift_π]
  change 𝟙 (P.X q) ≫ (η.app (P.X q)).app n = μ.f q ≫ limit.π (T.obj (P.X q)) n
  rw [Category.id_comp]
  exact (hμ q n.unop).symm

private def strict_completionIso
    (p : QuotientPresentation J A I false)
    (d : StrictQuotientDiagonalPresentation J A I)
    (e : d.reductionD ⋙ d.restrictionD ≅ p.tower) :
    d.reductionD ⋙ d.restrictionD ⋙ rlim (constant J A) ≅ p.tower ⋙ rlim (constant J A) :=
  (Functor.associator d.reductionD d.restrictionD (rlim (constant J A))).symm ≪≫
    Functor.isoWhiskerRight e (rlim (constant J A))

private theorem strict_completionIso_hom_app
    (p : QuotientPresentation J A I false)
    (d : StrictQuotientDiagonalPresentation J A I)
    (e : d.reductionD ⋙ d.restrictionD ≅ p.tower)
    (V : D (constant J A)) :
    (strict_completionIso J A I p d e).hom.app V =
      (rlim (constant J A)).map (e.hom.app V) := by
  change 𝟙 _ ≫ (rlim (constant J A)).map (e.hom.app V) = _
  exact Category.id_comp _

attribute [local irreducible] strict_completionIso

private theorem normalize_inverse
    {B : Type*} [Category B] {X Y Z : B} (κ : X ≅ Y) (a : Y ⟶ Z)
    (ε : X ≅ Z) (h : κ.hom ≫ a = ε.hom) : a ≫ ε.inv = κ.inv := by
  apply (cancel_epi κ.hom).1
  rw [← Category.assoc, h, ε.hom_inv_id, κ.hom_inv_id]

private theorem normalize_inverse_two
    {B : Type*} [Category B] {X Y W Z : B} (κ : X ≅ Y)
    (a : Y ⟶ W) (b : W ⟶ Z) (ε : X ≅ Z)
    (h : κ.hom ≫ a ≫ b = ε.hom) : a ≫ b ≫ ε.inv = κ.inv := by
  simpa only [Category.assoc] using
    normalize_inverse κ (a ≫ b) ε (by simpa only [Category.assoc] using h)

private def strict_constantLimitIso (O : Sheaf J CommRingCat.{u})
    (k : StrictConstantModel J O) :
    k.functor ⋙ rlim O ≅
      𝟭 (D O) := by
  have : IsIso (strict_constantLimitUnit J O k) := strict_constantLimitUnit_isIso J O k
  exact (asIso (strict_constantLimitUnit J O k)).symm

private theorem strict_constantLimitIso_inv (O : Sheaf J CommRingCat.{u})
    (k : StrictConstantModel J O) :
    (strict_constantLimitIso J O k).inv = strict_constantLimitUnit J O k := rfl

private theorem strict_constantLimitIso_app (O : Sheaf J CommRingCat.{u})
    (k : StrictConstantModel J O) (P : Cx O) :
    (limitComparison O).app
        (((constantTower J O).mapHomologicalComplex (.up ℤ)).obj P) ≫
      (rlim O).map
        (k.factors.inv.app P) ≫
      (strict_constantLimitIso J O k).hom.app ((Q O).obj P) =
        (Q O).map ((strict_literalLimitIso J O).app P).hom := by
  have : IsIso (strict_constantLimitUnit J O k) := strict_constantLimitUnit_isIso J O k
  exact normalize_inverse_two
    ((Q O).mapIso ((strict_literalLimitIso J O).symm.app P))
    ((limitComparison O).app
      (((constantTower J O).mapHomologicalComplex (.up ℤ)).obj P))
    ((rlim O).map
      (k.factors.inv.app P))
    ((asIso (strict_constantLimitUnit J O k)).app ((Q O).obj P))
    (strict_constantLimitUnit_app J O k P).symm

attribute [local irreducible] strict_constantLimitIso

private theorem unit_map_calculation
    {B T : Type*} [Category B] [Category T] (L : T ⥤ B)
    {X X' Y Z W : T} {U V : B}
    (κ : X ≅ X') (i : X ⟶ Y) (e : Y ⟶ Z) (β : Z ⟶ W)
    (t : X' ⟶ W) (a : U ⟶ V) (ρ : V ⟶ L.obj X')
    (h : i ≫ e ≫ β = κ.hom ≫ t) :
    ((a ≫ ρ ≫ L.map κ.inv) ≫ L.map i ≫ L.map e) ≫ L.map β =
      a ≫ ρ ≫ L.map t := by
  simp only [Category.assoc, ← L.map_comp]
  rw [h, κ.inv_hom_id_assoc]

private theorem unit_normalization
    {B T : Type*} [Category B] [Category T] (L : T ⥤ B)
    {X X' Y Z W : T} {U V : B}
    (κ : X ≅ X') (i : X ⟶ Y) (e : Y ⟶ Z) (β : Z ⟶ W) [IsIso β]
    (t : X' ⟶ W) (a : U ⟶ V) (ρ : V ⟶ L.obj X')
    (δ : U ⟶ L.obj X) (ε : U ⟶ L.obj Z)
    (hδ : δ = a ≫ ρ ≫ L.map κ.inv)
    (h : i ≫ e ≫ β = κ.hom ≫ t)
    (hε : a ≫ ρ ≫ L.map t = ε ≫ L.map β) :
    δ ≫ L.map i ≫ L.map e = ε := by
  apply (cancel_mono (L.map β)).1
  rw [hδ]
  exact (unit_map_calculation L κ i e β t a ρ h).trans hε

private theorem limit_naturality_calculation
    {A₀ A₁ B T : Type*} [Category A₀] [Category A₁] [Category B] [Category T]
    (Q₀ : A₀ ⥤ B) (Q₁ : A₁ ⥤ T) (L₀ : A₁ ⥤ A₀) (L₁ : T ⥤ B)
    (γ : L₀ ⋙ Q₀ ⟶ Q₁ ⋙ L₁) {P : A₀} {X Y : A₁}
    (a : P ⟶ L₀.obj X) (η : X ⟶ Y) (μ : P ⟶ L₀.obj Y)
    (hμ : a ≫ L₀.map η = μ) :
    Q₀.map a ≫ γ.app X ≫ L₁.map (Q₁.map η) = Q₀.map μ ≫ γ.app Y := by
  have hn : Q₀.map (L₀.map η) ≫ γ.app Y = γ.app X ≫ L₁.map (Q₁.map η) := by
    simpa only [Functor.comp_map] using γ.naturality η
  rw [← hn, ← Category.assoc, ← Q₀.map_comp, hμ]

private theorem completion_unit_on_representative
    (O : Sheaf J CommRingCat.{u}) (k : StrictConstantModel J O)
    (T : Mod O ⥤ (ℕᵒᵖ ⥤ Mod O)) [T.Additive]
    (η : constantTower J O ⟶ T) (P : Cx O)
    (μ : P ⟶ (ordinaryLimit O).obj ((T.mapHomologicalComplex (.up ℤ)).obj P))
    (hμ : ∀ q n, μ.f q ≫ limit.π (T.obj (P.X q)) (op n) = (η.app (P.X q)).app (op n))
    {F H : D O ⥤ TD O}
    (β : Q O ⋙ H ⟶ T.mapHomologicalComplex (.up ℤ) ⋙ TQ O)
    (α : Q O ⋙ F ⟶ T.mapHomologicalComplex (.up ℤ) ⋙ TQ O)
    (i : k.functor ⟶ F) (e : F ≅ H)
    (ε : 𝟭 (D O) ⟶ H ⋙ rlim O) [IsIso (β.app P)]
    (he : e.hom.app ((Q O).obj P) ≫ β.app P = α.app P)
    (hi : i.app ((Q O).obj P) ≫ α.app P = k.factors.hom.app P ≫
      (TQ O).map ((NatTrans.mapHomologicalComplex η (.up ℤ)).app P))
    (hε : ε.app ((Q O).obj P) ≫ (rlim O).map (β.app P) =
      (Q O).map μ ≫ (limitComparison O).app ((T.mapHomologicalComplex (.up ℤ)).obj P)) :
    (strict_constantLimitUnit J O k).app ((Q O).obj P) ≫
      (rlim O).map (i.app ((Q O).obj P)) ≫
      (rlim O).map (e.hom.app ((Q O).obj P)) = ε.app ((Q O).obj P) := by
  refine unit_normalization (rlim O) (k.factors.app P)
    (i.app ((Q O).obj P)) (e.hom.app ((Q O).obj P)) (β.app P)
    ((TQ O).map ((NatTrans.mapHomologicalComplex η (.up ℤ)).app P))
    ((Q O).map ((strict_literalLimitIso J O).inv.app P))
    ((limitComparison O).app
      (((constantTower J O).mapHomologicalComplex (.up ℤ)).obj P))
    _ _ (strict_constantLimitUnit_app J O k P) ?_ ?_
  · rw [he]
    exact hi
  · refine (limit_naturality_calculation (Q O) (TQ O) (ordinaryLimit O) (rlim O)
      (limitComparison O) ((strict_literalLimitIso J O).inv.app P)
      ((NatTrans.mapHomologicalComplex η (.up ℤ)).app P) μ
      (ordinary_unit_factorization J O T η P μ hμ)).trans ?_
    exact hε.symm

set_option maxHeartbeats 50000 in
-- Keep the concrete universal-comparison interface while avoiding exploratory unfolding.
private theorem strict_completion_unit
    (p : QuotientPresentation J A I false)
    (k : StrictConstantModel J (constant J A))
    (d : StrictQuotientDiagonalPresentation J A I)
    (i : k.functor ⟶
      d.reductionD ⋙ d.restrictionD)
    (e : d.reductionD ⋙ d.restrictionD ≅ p.tower)
    (he : Functor.whiskerLeft (Q (constant J A)) e.hom ≫
      p.comparison = d.representativeTransformation)
    (hi : Functor.whiskerLeft (Q (constant J A)) i ≫ d.representativeTransformation =
      strict_augmentationComparison J A I k) :
    strict_constantLimitUnit J (constant J A) k ≫ Functor.whiskerRight i (rlim (constant J A)) ≫
      (strict_completionIso J A I p d e).hom =
        p.unit := by
  let := reductionTower_additive J A I false
  apply strict_resolving_ext J (constant J A)
  intro P hP hf
  have heP : e.hom.app ((Q (constant J A)).obj P) ≫ p.comparison.app P =
      d.representativeTransformation.app P := NatTrans.congr_app he P
  have hiP : i.app ((Q (constant J A)).obj P) ≫ d.representativeTransformation.app P =
      k.factors.hom.app P ≫ (TQ (constant J A)).map
        ((NatTrans.mapHomologicalComplex (reductionUnit J A I false) (.up ℤ)).app P) := by
    have h := NatTrans.congr_app hi P
    unfold strict_augmentationComparison at h
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
    exact h
  have hβ : IsIso (p.comparison.app P) :=
    strict_quotient_comparison_isIso J A I p P hP hf
  change (strict_constantLimitUnit J (constant J A) k).app ((Q (constant J A)).obj P) ≫
    (rlim (constant J A)).map (i.app ((Q (constant J A)).obj P)) ≫
    (strict_completionIso J A I p d e).hom.app ((Q (constant J A)).obj P) = _
  rw [strict_completionIso_hom_app]
  exact completion_unit_on_representative J (constant J A) k
    (reductionTower J A I false) (reductionUnit J A I false) P
    (ordinaryUnit J A I false P) (ordinaryUnit_spec J A I false P)
    p.comparison d.representativeTransformation i e p.unit heP hiP
    (p.laws.2.2 P ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).1 hP)
      (fun q ↦ flatOnSite_flat J (P.X q) (hf q)))


set_option maxHeartbeats 50000 in
-- Check the normalized comparisons without unfolding their universal constructions.
/-- The strict quotient realization, common diagonal K-flat model, constant K-injective
normalization, and completion-unit equation, natural in every derived input.

Source: Stacks Project, sites-cohomology.tex, Tags 0940 and 0941;
proetale.tex, Tags 099M and 099N; agent strict quotient auxiliary
(blueprint: lem-pur-strict-quotient-diagonal-normalization).

Proof:
1. The ordinary strict quotient presentation constructs the coefficient map, diagonal,
tower equivalence, insertion and tensor normalization, and proves diagonal flatness.
2. Exact evaluation and scalar restriction use their existing APIs. The derived scalar
restriction reflects isomorphisms, and the tower equivalence retains this property.
3. A flat-term K-flat resolution gives one common representative. The scalar-extension
comparison is invertible on its K-flat diagonal, hence so is the canonical representative.
4. Evaluation at zero is exact and left adjoint to the constant-tower functor, so that
functor preserves K-injectives. The constant/limit adjunction supplies the ordinary limit
isomorphism, with degree maps the zero-level projections. Descend its inverse followed
by the right-derived limit comparison through localization. This map is invertible on
K-injectives and therefore on all derived objects; its inverse is ell.
5. The quotient presentation universal property gives a comparison from reduction
followed by restriction to the quotient-tower functor. Both comparisons are invertible
on flat-term K-flat representatives, so this is an isomorphism everywhere. Transport
the universal property along it and lift the ordinary quotient augmentation to obtain i.
Whiskering the comparison isomorphism with derived limit gives c.
6. The inverse ordinary constant-limit isomorphism followed by the limit of the quotient
augmentation is ordinaryUnit, by its unique projection formula. Check the desired natural
transformation equality on flat-term K-flat representatives, which detect equality.
Cancel the invertible quotient comparison, substitute the representative formulas for i,
c and ell inverse, and use naturality of the right-derived limit comparison. The result
is the ordinaryUnit equality followed by the existing quotient-presentation unit law.
This identifies the entire derived completion-unit morphism. -/
theorem strictQuotientDiagonalNormalization [IsNoetherianRing A] :
    ∃ (d : StrictQuotientDiagonalPresentation J A I)
      (i : (constantTower J (constant J A)).mapDerivedCategory ⟶
        d.reductionD ⋙ d.restrictionD)
      (ell : (constantTower J (constant J A)).mapDerivedCategory ⋙
        rlim (constant J A) ≅ 𝟭 (D (constant J A)))
      (c : d.reductionD ⋙ d.restrictionD ⋙ rlim (constant J A) ≅ completion J A I false)
      (literalLimit : ∀ P : Cx (constant J A),
        (ordinaryLimit (constant J A)).obj
          (((constantTower J (constant J A)).mapHomologicalComplex (.up ℤ)).obj P) ≅ P),
      (∀ n : ℕ, PreservesFiniteLimits
        (SheafOfModules.systemSequenceEvaluation (finiteSystem J A I) n) ∧
        PreservesFiniteColimits
          (SheafOfModules.systemSequenceEvaluation (finiteSystem J A I) n)) ∧
      PreservesFiniteLimits d.restriction ∧ PreservesFiniteColimits d.restriction ∧
      (∀ {V W : D (strictQuotientRing J A I)} (f : V ⟶ W),
        IsIso (d.restrictionD.map f) → IsIso f) ∧
      (∀ P : Cx (constant J A),
        CochainComplex.IsKFlatIndependentCoefficients (R := constant J A) P →
        (∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := constant J A) (P.X q)) →
        (CochainComplex.IsKFlatIndependentCoefficients (R := strictDiagonalRing J A)
          ((d.diagonal.mapHomologicalComplex (.up ℤ)).obj P) ∧
          (∀ q : ℤ, SheafOfModules.IsFlatOnSite
            (J := WeilConjectures.coefficientSequenceTopology J)
            (R := strictDiagonalRing J A) (d.diagonal.obj (P.X q))) ∧
          IsIso (d.representative P) ∧
          i.app ((Q (constant J A)).obj P) ≫ d.representative P =
            (constantTower J (constant J A)).mapDerivedCategoryFactors.hom.app P ≫
              (TQ (constant J A)).map
                ((NatTrans.mapHomologicalComplex (reductionUnit J A I false) (.up ℤ)).app P))) ∧
      (∀ V : D (constant J A), ∃ (P : Cx (constant J A))
        (_e : (Q (constant J A)).obj P ≅ V),
        CochainComplex.IsKFlatIndependentCoefficients (R := constant J A) P ∧
          (∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := constant J A) (P.X q))) ∧
      (∀ P : Cx (constant J A), P.IsKInjective →
        CochainComplex.IsKInjective
          (((constantTower J (constant J A)).mapHomologicalComplex (.up ℤ)).obj P)) ∧
      (∀ (P : Cx (constant J A)) (q : ℤ), (literalLimit P).hom.f q =
        limit.π ((constantTower J (constant J A)).obj (P.X q)) (op 0)) ∧
      (∀ P : Cx (constant J A), P.IsKInjective →
        (limitComparison (constant J A)).app
            (((constantTower J (constant J A)).mapHomologicalComplex (.up ℤ)).obj P) ≫
          (rlim (constant J A)).map
            ((constantTower J (constant J A)).mapDerivedCategoryFactors.inv.app P) ≫
          ell.hom.app ((Q (constant J A)).obj P) =
            (Q (constant J A)).map (literalLimit P).hom) ∧
      (∀ P : Cx (constant J A),
        CochainComplex.IsKFlatIndependentCoefficients (R := constant J A) P →
        (∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := constant J A) (P.X q)) →
        c.hom.app ((Q (constant J A)).obj P) ≫
          (rlim (constant J A)).map ((quotientPresentation J A I false).comparison.app P) =
            (rlim (constant J A)).map (d.representative P)) ∧
      ell.inv ≫ Functor.whiskerRight i (rlim (constant J A)) ≫ c.hom =
        completionUnit J A I false := by
  let p := quotientPresentation J A I false
  let k := strict_constantModel J (constant J A)
  refine assemble_normalization (strictQuotientOrdinaryFlatPresentation J A I)
    (fun d hd ↦ strict_reduction_comparison J A I p k d
      (fun P hP hf ↦ (hd P hP hf).1))
    (strict_constantLimitIso J (constant J A) k)
    (fun d e ↦ strict_completionIso J A I p d e)
    (fun P ↦ (strict_literalLimitIso J (constant J A)).app P) ?_
  intro d hd i e h
  obtain ⟨he, hi⟩ := h
  exact ⟨(fun n ↦ ⟨inferInstance, inferInstance⟩),
    (strict_restriction_exact J A I d).1, (strict_restriction_exact J A I d).2,
    strict_restriction_conservative J A I d,
    (fun P hP hf ↦ ⟨(hd P hP hf).1, (hd P hP hf).2,
      strict_representative_isIso J A I d P (hd P hP hf).1,
      by
        unfold StrictQuotientDiagonalPresentation.representative
        have h := NatTrans.congr_app hi P
        unfold strict_augmentationComparison at h
        dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
        exact h⟩),
    strict_flat_representative J (constant J A), strict_constant_kInjective J (constant J A),
    strict_literalLimitIso_f J (constant J A),
    (fun P _ ↦ strict_constantLimitIso_app J (constant J A) k P),
    (fun P _ _ ↦ by
      unfold StrictQuotientDiagonalPresentation.representative
      rw [strict_completionIso_hom_app]
      exact comparison_whisker_app (Q (constant J A)) e
        p.comparison d.representativeTransformation
        he (rlim (constant J A)) P),
    (by
      rw [strict_constantLimitIso_inv]
      exact strict_completion_unit J A I p k d i e he hi)⟩

end CategoryTheory.ConstantCompletion
