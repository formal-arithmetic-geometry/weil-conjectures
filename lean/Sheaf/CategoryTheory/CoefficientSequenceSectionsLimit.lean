/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q138
-/
module

public import Sheaf.CategoryTheory.CoefficientSequenceGlobalSections
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.CategoryTheory.SequencePushforwardLimitProjections
import Sheaf.CategoryTheory.SystemGrothendieck
import Sheaf.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all Sheaf.Algebra.Homology.ExactProductsRoosComparison
import all Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients

/-! # Derived sections and total inverse limit of strict coefficient systems

Source: Stacks Project, Cohomology on Sites, Tags 0941 and 0D6E; Injectives, Tag 079P
(blueprint: lem-coef-sequence-sections-limit-comparison).

The direct image of the specified ringed sequence projection is inverse limit after
termwise restriction. Its cone and the abelian inverse-limit cone are normalized on
complexes. The unit equation specifies the comparison, in addition to its finite projections.
Index `n : ℕ` denotes positive level `n+1`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules

section Generic

universe a av b bv c cv da db dc sep
variable {E : Type a} [Category.{av} E] [Abelian E] [HasDerivedCategory.{da} E]
  {F : Type b} [Category.{bv} F] [Abelian F] [HasDerivedCategory.{db} F]
  {H : Type c} [Category.{cv} H] [Abelian H] [HasDerivedCategory.{dc} H]

omit [HasDerivedCategory E] in
private theorem sectionsDerives (T : E ⥤ F) [T.Additive] :
    (CochainComplex.KInjectives.localizerMorphism E).Derives
      (T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) := by
  intro X Y f hf
  have : X.obj.IsKInjective := X.property
  have : Y.obj.IsKInjective := Y.property
  have : QuasiIso f.hom := hf
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff f.hom).mp
    (inferInstance : QuasiIso f.hom)
  have : QuasiIso ((T.mapHomologicalComplex (.up ℤ)).map f.hom) := by
    rw [← he]
    exact (T.mapHomotopyEquiv e).quasiIso_hom
  change IsIso (DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map f.hom))
  infer_instance

private theorem sectionsPairExists [Abelian.HasKInjectiveResolutions E]
    (T : E ⥤ F) [T.Additive] : Nonempty (SequenceSectionsDerivedPair T) := by
  let G := T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  let W := HomologicalComplex.quasiIso E (.up ℤ)
  have h := sectionsDerives T
  have := h.hasPointwiseRightDerivedFunctor
  refine ⟨⟨G.totalRightDerived DerivedCategory.Q W,
    G.totalRightDerivedUnit DerivedCategory.Q W, inferInstance, ?_⟩⟩
  intro I hI
  exact h.isIso_of_isRightDerivedFunctor _ (CochainComplex.KInjectives.mk I)

private def sectionsCompositeUnit (T : E ⥤ F) (S : F ⥤ H) [T.Additive] [S.Additive]
    (R : SequenceSectionsDerivedPair T) (P : SequenceSectionsDerivedPair S) :
    (T ⋙ S).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (R.functor ⋙ P.functor) where
  app X := P.unit.app ((T.mapHomologicalComplex (.up ℤ)).obj X) ≫
    P.functor.map (R.unit.app X)
  naturality X Y f := by
    change DerivedCategory.Q.map ((S.mapHomologicalComplex (.up ℤ)).map
        ((T.mapHomologicalComplex (.up ℤ)).map f)) ≫ _ = _
    have hn := P.unit.naturality ((T.mapHomologicalComplex (.up ℤ)).map f)
    have hm := R.unit.naturality f
    dsimp only [Functor.comp_map] at hn hm
    rw [← Category.assoc, hn]
    simp only [Category.assoc]
    rw [← P.functor.map_comp, hm, P.functor.map_comp]
    rfl

private theorem sectionsCompositeDerived [Abelian.HasKInjectiveResolutions E]
    (T : E ⥤ F) (S : F ⥤ H) [T.Additive] [S.Additive]
    (R : SequenceSectionsDerivedPair T) (P : SequenceSectionsDerivedPair S)
    (h : ∀ I : CochainComplex E ℤ, I.IsKInjective →
      IsIso (P.unit.app ((T.mapHomologicalComplex (.up ℤ)).obj I))) :
    (R.functor ⋙ P.functor).IsRightDerivedFunctor
      (sectionsCompositeUnit T S R P) (HomologicalComplex.quasiIso E (.up ℤ)) := by
  apply (sectionsDerives (T ⋙ S)).isRightDerivedFunctor_of_isIso
  intro I
  have := R.computes I.obj I.property
  have := h I.obj I.property
  change IsIso (P.unit.app _ ≫ P.functor.map (R.unit.app I.obj))
  infer_instance

private def sectionsExactCompositeUnit (T : E ⥤ F) (S : F ⥤ H)
    [T.Additive] [S.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (P : SequenceSectionsDerivedPair S) :
    (T ⋙ S).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (T.mapDerivedCategory ⋙ P.functor) where
  app X := P.unit.app ((T.mapHomologicalComplex (.up ℤ)).obj X) ≫
    P.functor.map (T.mapDerivedCategoryFactors.inv.app X)
  naturality X Y f := by
    have hn := P.unit.naturality ((T.mapHomologicalComplex (.up ℤ)).map f)
    have hm := T.mapDerivedCategoryFactors.inv.naturality f
    dsimp only [Functor.comp_map] at hn hm
    change DerivedCategory.Q.map ((S.mapHomologicalComplex (.up ℤ)).map
        ((T.mapHomologicalComplex (.up ℤ)).map f)) ≫ _ = _
    rw [← Category.assoc, hn]
    simp only [Category.assoc]
    rw [← P.functor.map_comp, hm, P.functor.map_comp]
    rfl

private def sectionsExactComposite [Abelian.HasKInjectiveResolutions E]
    (T : E ⥤ F) (S : F ⥤ H)
    [T.Additive] [S.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (P : SequenceSectionsDerivedPair S)
    (h : ∀ I : CochainComplex E ℤ, I.IsKInjective →
      IsIso (P.unit.app ((T.mapHomologicalComplex (.up ℤ)).obj I))) :
    SequenceSectionsDerivedPair (T ⋙ S) := by
  have hi (I : CochainComplex E ℤ) (hI : I.IsKInjective) :
      IsIso ((sectionsExactCompositeUnit T S P).app I) := by
    have := h I hI
    change IsIso (P.unit.app _ ≫ P.functor.map (T.mapDerivedCategoryFactors.inv.app I))
    infer_instance
  have hd : (T.mapDerivedCategory ⋙ P.functor).IsRightDerivedFunctor
      (sectionsExactCompositeUnit T S P) (HomologicalComplex.quasiIso E (.up ℤ)) := by
    apply (sectionsDerives (T ⋙ S)).isRightDerivedFunctor_of_isIso
    intro I
    exact hi I.obj I.property
  exact ⟨_, _, hd, hi⟩

private theorem sectionsProjections [HasLimitsOfShape ℕᵒᵖ E]
    [HasDerivedCategory (ℕᵒᵖ ⥤ E)]
    [(lim : (ℕᵒᵖ ⥤ E) ⥤ E).Additive]
    (L : SequenceSectionsDerivedPair (lim : (ℕᵒᵖ ⥤ E) ⥤ E)) :
    ∃ p : ∀ n : ℕ, L.functor ⟶
        ((CategoryTheory.evaluation ℕᵒᵖ E).obj (op n)).mapDerivedCategory,
      ∀ (X : CochainComplex (ℕᵒᵖ ⥤ E) ℤ) (n : ℕ),
        L.unit.app X ≫ (p n).app (DerivedCategory.Q.obj X) ≫
          ((CategoryTheory.evaluation ℕᵒᵖ E).obj (op n)).mapDerivedCategoryFactors.hom.app X =
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app X) := by
  have := L.universal
  let β (n : ℕ) := Functor.whiskerRight
    (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)) DerivedCategory.Q ≫
      ((CategoryTheory.evaluation ℕᵒᵖ E).obj (op n)).mapDerivedCategoryFactors.inv
  let p (n : ℕ) := L.functor.rightDerivedDesc L.unit
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ E) (.up ℤ)) _ (β n)
  refine ⟨p, ?_⟩
  intro X n
  rw [← Category.assoc, Functor.rightDerived_fac_app]
  simp [β]

private theorem sectionsNatTransExt [Abelian.HasKInjectiveResolutions E]
    {R S : DerivedCategory E ⥤ DerivedCategory F} (a b : R ⟶ S)
    (h : ∀ I : CochainComplex E ℤ, I.IsKInjective →
      a.app (DerivedCategory.Q.obj I) = b.app (DerivedCategory.Q.obj I)) : a = b := by
  apply NatTrans.ext
  funext X
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective X
  apply (cancel_mono (S.map e.hom)).mp
  rw [← a.naturality, ← b.naturality, h I hI]

omit [HasDerivedCategory E] in
private theorem sectionsTowerGrothendieck
    [IsGrothendieckAbelian.{sep} E] : IsGrothendieckAbelian.{sep} (ℕᵒᵖ ⥤ E) := by
  let G := separator E
  have hG := isSeparator_separator E
  have hS : ObjectProperty.IsSeparating
      (.ofObj fun n : ℕᵒᵖ ↦ (evaluationLeftAdjoint E n).obj G) := by
    intro M N f g hfg
    apply NatTrans.ext
    funext n
    apply hG.def
    intro a
    let adj := evaluationAdjunctionRight E n
    apply (adj.homEquiv G N).symm.injective
    have h := hfg _ (ObjectProperty.ofObj_apply _ n) ((adj.homEquiv G M).symm a)
    exact (adj.homEquiv_naturality_right_symm a f).trans
      (h.trans (adj.homEquiv_naturality_right_symm a g).symm)
  have : HasSeparator (ℕᵒᵖ ⥤ E) := ⟨_, hS.isSeparator_coproduct⟩
  have : HasFilteredColimitsOfSize.{sep, sep} (ℕᵒᵖ ⥤ E) := ⟨fun _ _ _ ↦ inferInstance⟩
  have : AB5OfSize.{sep, sep} (ℕᵒᵖ ⥤ E) := ⟨fun _ _ _ ↦ inferInstance⟩
  exact { locallySmall := ⟨fun M N ↦ small_of_injective
    (f := fun f : M ⟶ N ↦ f.app) (fun f g h ↦ NatTrans.ext h)⟩ }

private theorem sectionsSplitRoos
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [∀ (p : ℤ) (n : ℕ),
      IsSplitEpi ((I.X p).map (homOfLE (Nat.le_succ n)).op)] :
    let L := (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)
    let p : L.obj I ⟶ ∏ᶜ (fun n : ℕ ↦ I.asFunctor.obj (op n)) :=
      Pi.lift (fun n : ℕ ↦ (NatTrans.mapHomologicalComplex
        (lim.π (op n)) (ComplexShape.up ℤ)).app I)
    let t := towerTransitionEndomorphism
      (fun n : ℕ ↦ I.asFunctor.map (homOfLE (Nat.le_succ n)).op)
    ∃ h : p ≫ t = 0, (ShortComplex.mk p t h).ShortExact := by
  intro L p t
  let c : Cone I.asFunctor :=
    { pt := L.obj I
      π := { app := fun n ↦ (NatTrans.mapHomologicalComplex
                (lim.π n) (ComplexShape.up ℤ)).app I
             naturality := by
               intro n m f
               ext r
               change 𝟙 _ ≫ limit.π (I.X r) m =
                 limit.π (I.X r) n ≫ (I.X r).map f
               rw [Category.id_comp]
               exact (limit.w _ _).symm } }
  have hc : IsLimit c := by
    apply HomologicalComplex.isLimitOfEval
    intro r
    exact limit.isLimit (I.X r)
  let K := fun n : ℕ ↦ I.asFunctor.obj (op n)
  let P : Fan K := limit.cone (Discrete.functor K)
  have ht (n) : t ≫ P.proj n = P.proj n - P.proj (n + 1) ≫
      I.asFunctor.map (homOfLE (Nat.le_succ n)).op := by
    change t ≫ Pi.π K n = Pi.π K n - Pi.π K (n + 1) ≫ _
    simp [t, K, towerTransitionEndomorphism, towerProductShift]
  obtain ⟨h, ⟨hk⟩⟩ := CategoryTheory.tower_kernel I.asFunctor c hc P
    (limit.isLimit _) p t (fun n ↦ Pi.lift_π _ n) ht
  refine ⟨h, HomologicalComplex.shortExact_of_degreewise_shortExact _ ?_⟩
  intro r
  let ev := HomologicalComplex.eval A (ComplexShape.up ℤ) r
  have hkr := KernelFork.mapIsLimit _ hk ev
  have hPr : IsLimit (Fan.mk (P.pt.X r) (fun n ↦ (P.proj n).f r)) :=
    (Fan.isLimitMapConeEquiv ev K P) (isLimitOfPreserves ev (limit.isLimit _))
  have htr : IsSplitEpi (t.f r) := CategoryTheory.fan_shift_splitEpi
    (fun n : ℕ ↦ (I.X r).obj (op n)) _ hPr
    (fun n : ℕ ↦ (I.X r).map (homOfLE (Nat.le_succ n)).op) (t.f r)
    (fun n ↦ congrArg (fun f ↦ f.f r) (ht n))
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ hkr)
    (mono_of_isLimit_fork hkr) htr.epi


private theorem sectionsRoosComparisonQuasiIso
    (I : CochainComplex (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ℤ)
    [∀ (p : ℤ) (n : ℕ), IsSplitEpi ((I.X p).map (homOfLE (Nat.le_succ n)).op)] :
    QuasiIso (ExactProductsRoos.comparison.app I) := by
  obtain ⟨h, hs⟩ := sectionsSplitRoos I
  let S := ShortComplex.mk (ExactProductsRoos.inclusion.app I)
    (-ExactProductsRoos.difference.app I)
    (by rw [Preadditive.comp_neg, ExactProductsRoos.inclusion_difference, neg_zero])
  have hS : S.ShortExact := by
    apply ShortComplex.shortExact_of_iso (S₁ := ShortComplex.mk _ _ h) _ hs
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      { hom := -𝟙 _
        inv := -𝟙 _
        hom_inv_id := by simp
        inv_hom_id := by simp } (by simp [S]) (by
          change 𝟙 _ ≫ (-ExactProductsRoos.difference.app I) = _ ≫ (-𝟙 _)
          simp)
  exact AlgebraicGeometry.ProEtale.cocone_lift_quasiIso S hS
    (ExactProductsRoos.comparison_condition I)

omit [HasDerivedCategory E] in
private theorem sectionsTowerImageAcyclic
    [IsGrothendieckAbelian.{sep} E]
    (T : E ⥤ AddCommGrpCat.{w}) [T.Additive]
    [(lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).Additive]
    (L : SequenceSectionsDerivedPair
      (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}))
    (I : CochainComplex (ℕᵒᵖ ⥤ E) ℤ) (hI : I.IsKInjective) :
    IsIso (L.unit.app
      ((((Functor.whiskeringRight ℕᵒᵖ E AddCommGrpCat.{w}).obj T).mapHomologicalComplex
        (.up ℤ)).obj I)) := by
  have : IsGrothendieckAbelian.{sep} (ℕᵒᵖ ⥤ E) := sectionsTowerGrothendieck
  have : IsGrothendieckAbelian.{w} (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) :=
    sectionsTowerGrothendieck
  have := hI
  let W := (Functor.whiskeringRight ℕᵒᵖ E AddCommGrpCat.{w}).obj T
  let J := (CochainComplex.kInjectiveResolutionFunctor.{sep} (ℕᵒᵖ ⥤ E)).obj I
  let q : I ⟶ J := (CochainComplex.toKInjectiveResolution.{sep} (ℕᵒᵖ ⥤ E)).app I
  have : QuasiIso q :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app _ I).2
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff q).mp inferInstance
  have hWq : QuasiIso ((W.mapHomologicalComplex (.up ℤ)).map q) := by
    rw [← he]
    exact (W.mapHomotopyEquiv e).quasiIso_hom
  have hLq : QuasiIso
      ((lim.mapHomologicalComplex (.up ℤ)).map ((W.mapHomologicalComplex (.up ℤ)).map q)) := by
    rw [← he]
    exact (lim.mapHomotopyEquiv (W.mapHomotopyEquiv e)).quasiIso_hom
  have (p : ℤ) (n : ℕ) : IsSplitEpi
      ((((W.mapHomologicalComplex (.up ℤ)).obj J).X p).map
        (homOfLE (Nat.le_succ n)).op) := by
    have := CategoryTheory.injective_tower_transition_split (J.X p) n
    change IsSplitEpi (T.map ((J.X p).map (homOfLE (Nat.le_succ n)).op))
    infer_instance
  have : QuasiIso (ExactProductsRoos.comparison.app
      ((W.mapHomologicalComplex (.up ℤ)).obj J)) := sectionsRoosComparisonQuasiIso _
  obtain ⟨a, ha⟩ := ExactProductsRoos.comparisonIso L.functor L.unit L.computes
  have hη : IsIso (L.unit.app ((W.mapHomologicalComplex (.up ℤ)).obj J)) := by
    have heq := congrArg (fun η ↦ η.app ((W.mapHomologicalComplex (.up ℤ)).obj J)) ha
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app] at heq
    rw [← heq]
    infer_instance
  have hn := L.unit.naturality ((W.mapHomologicalComplex (.up ℤ)).map q)
  have : IsIso (L.unit.app ((W.mapHomologicalComplex (.up ℤ)).obj I) ≫
      L.functor.map (DerivedCategory.Q.map ((W.mapHomologicalComplex (.up ℤ)).map q))) := by
    change _ = L.unit.app ((W.mapHomologicalComplex (.up ℤ)).obj I) ≫
      L.functor.map (DerivedCategory.Q.map ((W.mapHomologicalComplex (.up ℤ)).map q)) at hn
    rw [← hn]
    change IsIso (DerivedCategory.Q.map
      ((lim.mapHomologicalComplex (.up ℤ)).map
        ((W.mapHomologicalComplex (.up ℤ)).map q)) ≫
      L.unit.app ((W.mapHomologicalComplex (.up ℤ)).obj J))
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (L.functor.map (DerivedCategory.Q.map ((W.mapHomologicalComplex (.up ℤ)).map q)))

end Generic

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

/-- The actual module direct image of the ringed sequence projection: compatible families
of scalar-restricted sections. Source: Stacks 0941, 0D6E
(blueprint: lem-coef-sequence-sections-limit-comparison). -/
def sequenceProjectionDirectImage
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {A : Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B} (d : SequenceSectionsComparisons B A α) :
    StrictRingSystem B ⥤ sequenceCoefficientModules A :=
  d.restriction.functor ⋙ lim

/-- Inverse limit is additive, being a finite-product-preserving functor.
Source: Stacks 0941 (blueprint: lem-coef-sequence-sections-limit-comparison). -/
instance sequenceModuleLimitAdditive (A : Sheaf J CommRingCat.{w}) :
    (lim : (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ⥤ sequenceCoefficientModules A).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Abelian inverse limit is additive.
Source: Stacks 0941 (blueprint: lem-coef-sequence-sections-limit-comparison). -/
instance sequenceAbLimitAdditive :
    (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Additivity of the specified projection direct image.
Source: Stacks 0941, 0D6E (blueprint: lem-coef-sequence-sections-limit-comparison). -/
instance sequenceProjectionDirectImageAdditive
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {A : Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B} (d : SequenceSectionsComparisons B A α) :
    (sequenceProjectionDirectImage d).Additive :=
  inferInstanceAs (d.restriction.functor ⋙ lim).Additive

/-- Global sections preserve tower limits, with the usual limit-preservation structure.
Source: Stacks 01FT, 0941 (blueprint: lem-coef-sequence-sections-limit-comparison). -/
instance sequenceSectionsPreservesTowerLimits (A : Sheaf J CommRingCat.{w}) :
    PreservesLimitsOfShape ℕᵒᵖ (sequenceCoefficientSections A) := by
  change PreservesLimitsOfShape ℕᵒᵖ
    (SheafOfModules.forget (derivedChangeRingIndependentCoefficients J A) ⋙
      PresheafOfModules.toPresheaf (derivedChangeRingIndependentCoefficients J A).obj ⋙ lim)
  infer_instance

/-- The ordinary comparison sends a section to its actual family of cone projections.
Source: Stacks 0941, 0D6E (blueprint: lem-coef-sequence-sections-limit-comparison). -/
def sequenceSectionsLimitOrdinary
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {A : Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B} (d : SequenceSectionsComparisons B A α) :
    sequenceProjectionDirectImage d ⋙ sequenceCoefficientSections A ≅
      (d.restriction.functor ⋙ sequenceTowerSections A) ⋙
        (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}) :=
  Functor.isoWhiskerLeft d.restriction.functor
    (preservesLimitNatIso (sequenceCoefficientSections A))

@[irreducible] private def sectionsRestrictionIso
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {A : Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B}
    (r : SequenceCoefficientRestrictionData B A α)
    (U : StrictRingSystem B ⥤ (ℕᵒᵖ ⥤ sequenceCoefficientModules A))
    (uObj : ∀ (N : StrictRingSystem B) (n : ℕ),
      (U.obj N).obj (op n) = (sequenceCoefficientRestriction (α.app (op n))).obj (N.level n))
    (uEval : ∀ n : ℕ, U ⋙ (CategoryTheory.evaluation ℕᵒᵖ _).obj (op n) ≅
      systemEvaluation B n ⋙ sequenceCoefficientRestriction (α.app (op n)))
    (hu : ∀ (N : StrictRingSystem B) {m n : ℕ} (h : m ≤ n)
      (V : Cᵒᵖ) (x : (N.level n).val.obj V),
      ((U.obj N).map (homOfLE h).op).val.app V
        ((eqToHom (uObj N n).symm).val.app V x) =
      (eqToHom (uObj N m).symm).val.app V ((N.transition h).val.app V x))
    (he : ∀ (N : StrictRingSystem B) (n : ℕ),
      (uEval n).hom.app N = eqToHom (uObj N n)) : r.functor ≅ U := by
  let en (N : StrictRingSystem B) (n : ℕ) :=
    (r.evaluation n).app N ≪≫ ((uEval n).app N).symm
  refine NatIso.ofComponents (fun N ↦ NatIso.ofComponents (fun n ↦ en N n.unop) ?_) ?_
  · intro n m f
    have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
    have hle := leOfHom f.unop
    rw [hf]
    apply (cancel_mono ((uEval m.unop).hom.app N)).mp
    dsimp only [en, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    ext x
    have hr := r.transitions N hle V x
    have hh := hu N hle V (((r.evaluation n.unop).hom.app N).val.app V x)
    have hinv (k : ℕ) : (uEval k).inv.app N = eqToHom (uObj N k).symm := by
      apply (cancel_mono ((uEval k).hom.app N)).mp
      rw [Iso.inv_hom_id_app, he]
      simp
    have hi (k : ℕ) (y : (N.level k).val.obj V) :
        ((uEval k).hom.app N).val.app V
          ((eqToHom (uObj N k).symm).val.app V y) = y := by
      change ((eqToHom (uObj N k).symm ≫ (uEval k).hom.app N).val.app V) y = y
      rw [he]
      simp
      rfl
    change (((r.evaluation m.unop).hom.app N).val.app V
      (((r.functor.obj N).map (homOfLE hle).op).val.app V x)) =
      ((uEval m.unop).hom.app N).val.app V
        (((U.obj N).map (homOfLE hle).op).val.app V
          (((uEval n.unop).inv.app N).val.app V
            (((r.evaluation n.unop).hom.app N).val.app V x)))
    erw [hinv, hh, hi]
    exact eq_of_heq hr
  · intro N N' f
    apply NatTrans.ext
    funext n
    change (r.functor.map f).app n ≫
        ((r.evaluation n.unop).hom.app N' ≫ (uEval n.unop).inv.app N') =
      ((r.evaluation n.unop).hom.app N ≫ (uEval n.unop).inv.app N) ≫ (U.map f).app n
    have h₁ := (r.evaluation n.unop).hom.naturality f
    have h₂ := (uEval n.unop).inv.naturality f
    dsimp only [Functor.comp_map] at h₁ h₂
    erw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]


private theorem sectionsRestrictionLimitAcyclic
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} {A : Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B}
    (r : SequenceCoefficientRestrictionData B A α)
    (LA : SequenceSectionsDerivedPair
      (lim : (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ⥤ sequenceCoefficientModules A))
    (I : CochainComplex (StrictRingSystem B) ℤ) (hI : I.IsKInjective) :
    IsIso (LA.unit.app ((r.functor.mapHomologicalComplex (.up ℤ)).obj I)) := by
  have h := SequenceProjection.pushforwardLimitProjections.{u, v, w, max u v (w + 1)}
    A B α
  obtain ⟨G, F, hG, hF, e, π, adj, h₀⟩ := h
  obtain ⟨L, R, ε, η, dadj, h₁⟩ := h₀.2.2.2.2.2.2
  obtain ⟨U, hU, hUl, hUc, uObj, uEval, πOrd, fLim,
    RL, ηL, πL, xi, c, la, dla, h₂⟩ := h₁.2.2.2.2.2.2
  have hutr := h₂.2.1
  have heval := h₂.2.2.1
  have hacyc := h₂.2.2.2.2.2.2.2.2.2.1
  let eU := sectionsRestrictionIso r U uObj uEval hutr heval
  have : IsGrothendieckAbelian.{w} (sequenceCoefficientModules A) :=
    isGrothendieckAbelian_coefficientUniverse _
  have : IsGrothendieckAbelian.{w} (ℕᵒᵖ ⥤ sequenceCoefficientModules A) :=
    sectionsTowerGrothendieck
  let X := (r.functor.mapHomologicalComplex (.up ℤ)).obj I
  let K := (CochainComplex.kInjectiveResolutionFunctor.{w} _).obj X
  let j : X ⟶ K := (CochainComplex.toKInjectiveResolution.{w} _).app X
  have : QuasiIso j := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app _ X).2
  let ec := (NatIso.mapHomologicalComplex eU (.up ℤ)).app I
  let j' := ec.inv ≫ j
  have : QuasiIso j' := inferInstance
  have hj' := (hacyc I hI K inferInstance j').1
  have : QuasiIso (((lim : (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ⥤
      sequenceCoefficientModules A).mapHomologicalComplex (.up ℤ)).map j) := by
    have hj'' : QuasiIso
        (((lim : (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ⥤
          sequenceCoefficientModules A).mapHomologicalComplex (.up ℤ)).map ec.inv ≫
        ((lim : (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ⥤
          sequenceCoefficientModules A).mapHomologicalComplex (.up ℤ)).map j) := by
      simpa only [j', Functor.map_comp] using hj'
    exact quasiIso_of_comp_left
      (((lim : (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ⥤
        sequenceCoefficientModules A).mapHomologicalComplex (.up ℤ)).map ec.inv)
      (((lim : (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ⥤
        sequenceCoefficientModules A).mapHomologicalComplex (.up ℤ)).map j)
  have := LA.computes K inferInstance
  have hn := LA.unit.naturality j
  change DerivedCategory.Q.map
      (((lim : (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ⥤
        sequenceCoefficientModules A).mapHomologicalComplex (.up ℤ)).map j) ≫ LA.unit.app K =
    LA.unit.app X ≫ LA.functor.map (DerivedCategory.Q.map j) at hn
  have : IsIso (LA.unit.app X ≫ LA.functor.map (DerivedCategory.Q.map j)) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (LA.functor.map (DerivedCategory.Q.map j))

private theorem sectionsConstantComparison
    (A : Sheaf J CommRingCat.{w})
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B} (d : SequenceSectionsComparisons B A α)
    (LA : SequenceSectionsDerivedPair
      (lim : (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ⥤ sequenceCoefficientModules A))
    (LB : SequenceSectionsDerivedPair
      (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}))
    (hacyc : ∀ I : CochainComplex (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ℤ,
      I.IsKInjective → IsIso (LB.unit.app
        (((sequenceTowerSections A).mapHomologicalComplex (.up ℤ)).obj I))) :
    ∃ κ : LA.functor ⋙ (d.finite A).functor ≅ d.tower.functor ⋙ LB.functor,
      ∀ X : CochainComplex (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ℤ,
        (d.finite A).unit.app
            (((lim : (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ⥤
              sequenceCoefficientModules A).mapHomologicalComplex (.up ℤ)).obj X) ≫
          (d.finite A).functor.map (LA.unit.app X) ≫
          κ.hom.app (DerivedCategory.Q.obj X) =
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (preservesLimitNatIso (sequenceCoefficientSections A) (J := ℕᵒᵖ))
            (.up ℤ)).hom.app X) ≫
          LB.unit.app (((sequenceTowerSections A).mapHomologicalComplex (.up ℤ)).obj X) ≫
          LB.functor.map (d.tower.unit.app X) := by
  have : IsGrothendieckAbelian.{w} (sequenceCoefficientModules A) :=
    isGrothendieckAbelian_coefficientUniverse _
  have : IsGrothendieckAbelian.{w} (ℕᵒᵖ ⥤ sequenceCoefficientModules A) :=
    sectionsTowerGrothendieck
  have : (lim : (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ⥤
      sequenceCoefficientModules A).PreservesKInjectiveComplexes :=
    Adjunction.preservesKInjectiveComplexes constLimAdj
  let a := sectionsCompositeUnit _ _ LA (d.finite A)
  let b := sectionsCompositeUnit _ _ d.tower LB
  have ha := sectionsCompositeDerived _ _ LA (d.finite A) (fun I hI ↦ by
    have := hI
    exact (d.finite A).computes _ inferInstance)
  have hb := sectionsCompositeDerived _ _ d.tower LB hacyc
  let τ := Functor.isoWhiskerRight (NatIso.mapHomologicalComplex
    (preservesLimitNatIso (sequenceCoefficientSections A) (J := ℕᵒᵖ)) (.up ℤ))
      DerivedCategory.Q
  let κ := Functor.rightDerivedNatIso _ _ a b
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ sequenceCoefficientModules A) (.up ℤ)) τ
  refine ⟨κ, ?_⟩
  intro X
  have h := Functor.rightDerivedNatTrans_app _ _ a b
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ sequenceCoefficientModules A) (.up ℤ)) τ.hom X
  change (a.app X ≫ κ.hom.app (DerivedCategory.Q.obj X)) =
    τ.hom.app X ≫ b.app X at h
  simpa only [a, b, sectionsCompositeUnit, τ, NatIso.mapHomologicalComplex,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.assoc] using h

private theorem sectionsConstantProjections
    (A : Sheaf J CommRingCat.{w})
    {B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}}
    {α : (Functor.const ℕᵒᵖ).obj A ⟶ B} (d : SequenceSectionsComparisons B A α)
    (hd : d.Normalized)
    (LA : SequenceSectionsDerivedPair
      (lim : (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ⥤ sequenceCoefficientModules A))
    (LB : SequenceSectionsDerivedPair
      (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}))
    (pA : ∀ n : ℕ, LA.functor ⟶
      ((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
        (op n)).mapDerivedCategory)
    (pB : ∀ n : ℕ, LB.functor ⟶
      ((CategoryTheory.evaluation ℕᵒᵖ AddCommGrpCat.{w}).obj (op n)).mapDerivedCategory)
    (hpA : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ℤ) (n : ℕ),
      LA.unit.app X ≫ (pA n).app (DerivedCategory.Q.obj X) ≫
        ((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
          (op n)).mapDerivedCategoryFactors.hom.app X =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app X))
    (hpB : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ℤ) (n : ℕ),
      LB.unit.app X ≫ (pB n).app (DerivedCategory.Q.obj X) ≫
        ((CategoryTheory.evaluation ℕᵒᵖ AddCommGrpCat.{w}).obj
          (op n)).mapDerivedCategoryFactors.hom.app X =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app X))
    (κ : LA.functor ⋙ (d.finite A).functor ≅ d.tower.functor ⋙ LB.functor)
    (hκ : ∀ X : CochainComplex (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ℤ,
      (d.finite A).unit.app
          (((lim : (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ⥤
            sequenceCoefficientModules A).mapHomologicalComplex (.up ℤ)).obj X) ≫
        (d.finite A).functor.map (LA.unit.app X) ≫ κ.hom.app (DerivedCategory.Q.obj X) =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
        (preservesLimitNatIso (sequenceCoefficientSections A) (J := ℕᵒᵖ))
          (.up ℤ)).hom.app X) ≫
        LB.unit.app (((sequenceTowerSections A).mapHomologicalComplex (.up ℤ)).obj X) ≫
        LB.functor.map (d.tower.unit.app X)) :
    ∀ (M : DerivedCategory (ℕᵒᵖ ⥤ sequenceCoefficientModules A)) (n : ℕ),
      κ.hom.app M ≫ (pB n).app (d.tower.functor.obj M) ≫ (d.evaluation n).hom.app M =
        (d.finite A).functor.map ((pA n).app M) := by
  have : IsGrothendieckAbelian.{w} (sequenceCoefficientModules A) :=
    isGrothendieckAbelian_coefficientUniverse _
  have : IsGrothendieckAbelian.{w} (ℕᵒᵖ ⥤ sequenceCoefficientModules A) :=
    sectionsTowerGrothendieck
  have : (lim : (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ⥤
      sequenceCoefficientModules A).PreservesKInjectiveComplexes :=
    Adjunction.preservesKInjectiveComplexes constLimAdj
  intro M n
  let γ₁ : LA.functor ⋙ (d.finite A).functor ⟶
      ((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
        (op n)).mapDerivedCategory ⋙ (d.finite A).functor :=
    κ.hom ≫ Functor.whiskerLeft d.tower.functor (pB n) ≫ (d.evaluation n).hom
  let γ₂ := Functor.whiskerRight (pA n) (d.finite A).functor
  have hγ : γ₁ = γ₂ := by
    apply sectionsNatTransExt
    intro I hI
    have := hI
    have := LA.computes I hI
    have := (d.finite A).computes
      (((lim : (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ⥤
        sequenceCoefficientModules A).mapHomologicalComplex (.up ℤ)).obj I) inferInstance
    have : IsIso ((sectionsCompositeUnit _ _ LA (d.finite A)).app I) := by
      change IsIso ((d.finite A).unit.app _ ≫ (d.finite A).functor.map (LA.unit.app I))
      infer_instance
    apply (cancel_epi ((sectionsCompositeUnit _ _ LA (d.finite A)).app I)).mp
    change ((d.finite A).unit.app _ ≫ (d.finite A).functor.map (LA.unit.app I)) ≫
      (κ.hom.app _ ≫ (pB n).app _ ≫ (d.evaluation n).hom.app _) =
      ((d.finite A).unit.app _ ≫ (d.finite A).functor.map (LA.unit.app I)) ≫
        (d.finite A).functor.map ((pA n).app _)
    apply (cancel_mono ((d.finite A).functor.map
      (((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
        (op n)).mapDerivedCategoryFactors.hom.app I))).mp
    have he := hd.evaluation_unit n I hI
    have he' := congrArg (fun z ↦
      ((CategoryTheory.evaluation ℕᵒᵖ AddCommGrpCat.{w}).obj
        (op n)).mapDerivedCategoryFactors.hom.app
          (((sequenceTowerSections A).mapHomologicalComplex (.up ℤ)).obj I) ≫ z) he
    simp only [Iso.hom_inv_id_app_assoc] at he'
    have hn := (pB n).naturality (d.tower.unit.app I)
    have hc : (NatIso.mapHomologicalComplex
        (preservesLimitNatIso (sequenceCoefficientSections A) (J := ℕᵒᵖ))
          (.up ℤ)).hom.app I ≫
        (NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app
          (((sequenceTowerSections A).mapHomologicalComplex (.up ℤ)).obj I) =
      ((sequenceCoefficientSections A).mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I) := by
      apply HomologicalComplex.hom_ext
      intro i
      exact preservesLimitIso_hom_π (sequenceCoefficientSections A) (I.X i) (op n)
    have hfπ := (d.finite A).unit.naturality
      ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I)
    dsimp only [Functor.comp_map] at hfπ
    simp only [Category.assoc]
    have hk := congrArg (fun z ↦ z ≫
      (pB n).app (d.tower.functor.obj (DerivedCategory.Q.obj I)) ≫
      (d.evaluation n).hom.app (DerivedCategory.Q.obj I) ≫
      (d.finite A).functor.map
        (((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
          (op n)).mapDerivedCategoryFactors.hom.app I)) (hκ I)
    simp only [Category.assoc] at hk
    rw [hk]
    erw [← Category.assoc (LB.functor.map (d.tower.unit.app I)), hn]
    simp only [Category.assoc]
    erw [he']
    have hs := congrArg (fun z ↦ z ≫ (d.finite A).unit.app
      ((((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
        (op n)).mapHomologicalComplex (.up ℤ)).obj I))
      (hpB (((sequenceTowerSections A).mapHomologicalComplex (.up ℤ)).obj I) n)
    simp only [Category.assoc] at hs
    erw [hs]
    erw [← Category.assoc, ← DerivedCategory.Q.map_comp, hc, hfπ]
    simp only [← (d.finite A).functor.map_comp]
    rw [hpA I n]
  exact NatTrans.congr_app hγ M

/-- Derived global sections of the total direct image agree canonically with the total
inverse limit of strict derived sections, retaining all actual finite projections.
Source: Stacks 079P, 0941 and 0D6E
(blueprint: lem-coef-sequence-sections-limit-comparison).

Proof:
1. The coefficient-universe Grothendieck theorems provide K-injective resolutions of
   module sheaves and strict systems. Evaluation left adjoints applied to a separator
   give a separator for constant-coefficient towers, so these also admit resolutions.
2. Use the normalized sequence-projection theorem's inverse-limit acyclicity clause.
   Its restriction is isomorphic to the specified restriction: the level comparisons
   and sectionwise transition equations give the isomorphism. Naturality of the limit
   unit then shows that exact derived restriction followed by derived limit is a
   universal derived pair for the actual projection direct image.
3. The exact constant-tower left adjoint makes limit preserve K-injectives. In the other
   order, resolve a K-injective tower by one with injective terms. Its successor maps
   split, and sections preserve their splittings. The split-transition Roos short exact
   sequence and exact products in abelian groups make the abelian limit unit invertible
   on termwise sections. The resolution is a homotopy equivalence, so this also holds
   for the original K-injective tower. No exact products of module sheaves are used.
4. The ordinary sections/limit isomorphism induces an isomorphism between the two
   universal derived pairs. Its universal-unit equation, whiskered with exact derived
   restriction, is precisely the asserted normalization on every complex.
5. Derive the actual limit projections by the universal property. On K-injective
   representatives, cancel the invertible composite unit and apply the normalized
   sections/evaluation equation and the ordinary limit-cone equation. Naturality extends
   this identity to all derived objects. Whisker by restriction and compose with the
   given restriction/evaluation and scalar comparisons to obtain the final equation. -/
theorem coefficientSequenceSectionsLimitComparison
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (A : Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B)
    (d : SequenceSectionsComparisons B A α) (_hd : d.Normalized) :
    ∃ (P : SequenceSectionsDerivedPair (sequenceProjectionDirectImage d))
      (L : SequenceSectionsDerivedPair
        (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w}))
      (πP : ∀ n : ℕ, P.functor ⟶ d.restriction.functor.mapDerivedCategory ⋙
        ((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
          (op n)).mapDerivedCategory)
      (πL : ∀ n : ℕ, L.functor ⟶
        ((CategoryTheory.evaluation ℕᵒᵖ AddCommGrpCat.{w}).obj (op n)).mapDerivedCategory)
      (κ : P.functor ⋙ (d.finite A).functor ≅ d.global ⋙ L.functor),
      (∀ (X : CochainComplex (StrictRingSystem B) ℤ) (n : ℕ),
        P.unit.app X ≫ (πP n).app (DerivedCategory.Q.obj X) ≫
          ((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
            (op n)).mapDerivedCategory.map
              (d.restriction.functor.mapDerivedCategoryFactors.hom.app X) ≫
          ((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
            (op n)).mapDerivedCategoryFactors.hom.app
              ((d.restriction.functor.mapHomologicalComplex (.up ℤ)).obj X) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (lim.π (op n))
          (.up ℤ)).app ((d.restriction.functor.mapHomologicalComplex (.up ℤ)).obj X))) ∧
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ℤ) (n : ℕ),
        L.unit.app X ≫ (πL n).app (DerivedCategory.Q.obj X) ≫
          ((CategoryTheory.evaluation ℕᵒᵖ AddCommGrpCat.{w}).obj
            (op n)).mapDerivedCategoryFactors.hom.app X =
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app X)) ∧
      (∀ X : CochainComplex (StrictRingSystem B) ℤ,
        (d.finite A).unit.app
            (((sequenceProjectionDirectImage d).mapHomologicalComplex (.up ℤ)).obj X) ≫
          (d.finite A).functor.map (P.unit.app X) ≫
          κ.hom.app (DerivedCategory.Q.obj X) =
        DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (sequenceSectionsLimitOrdinary d) (.up ℤ)).hom.app X) ≫
          L.unit.app (((d.restriction.functor ⋙ sequenceTowerSections A).mapHomologicalComplex
            (.up ℤ)).obj X) ≫
          L.functor.map (d.tower.unit.app
            ((d.restriction.functor.mapHomologicalComplex (.up ℤ)).obj X)) ≫
          L.functor.map (d.tower.functor.map
            (d.restriction.functor.mapDerivedCategoryFactors.inv.app X))) ∧
      (∀ (M : DerivedCategory (StrictRingSystem B)) (n : ℕ),
        κ.hom.app M ≫ (πL n).app (d.global.obj M) ≫ (d.finiteEvaluation n).hom.app M =
          (d.finite A).functor.map ((πP n).app M) ≫
            (d.finite A).functor.map
              ((sequenceRestrictionDerivedEvaluation d.restriction n).hom.app M) ≫
            (d.scalar (α.app (op n))).inv.app ((derivedSystemEvaluation B n).obj M)) := by
  have : IsGrothendieckAbelian.{w} (sequenceCoefficientModules A) :=
    isGrothendieckAbelian_coefficientUniverse _
  have : IsGrothendieckAbelian.{w} (ℕᵒᵖ ⥤ sequenceCoefficientModules A) :=
    sectionsTowerGrothendieck
  have : IsGrothendieckAbelian.{w} (StrictRingSystem B) :=
    strictRingSystem_isGrothendieckAbelian B
  have : IsGrothendieckAbelian.{w} (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) :=
    sectionsTowerGrothendieck
  obtain ⟨LA⟩ := sectionsPairExists
    (lim : (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ⥤ sequenceCoefficientModules A)
  obtain ⟨LB⟩ := sectionsPairExists
    (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ AddCommGrpCat.{w})
  let P : SequenceSectionsDerivedPair (sequenceProjectionDirectImage d) :=
    sectionsExactComposite d.restriction.functor _ LA
      (sectionsRestrictionLimitAcyclic d.restriction LA)
  obtain ⟨pA, hpA⟩ := sectionsProjections LA
  obtain ⟨pB, hpB⟩ := sectionsProjections LB
  obtain ⟨κ₀, hκ₀⟩ := sectionsConstantComparison A d LA LB
    (fun I hI ↦ sectionsTowerImageAcyclic (sequenceCoefficientSections A) LB I hI)
  have hproj := sectionsConstantProjections A d _hd LA LB pA pB hpA hpB κ₀ hκ₀
  let p (n : ℕ) := Functor.whiskerLeft d.restriction.functor.mapDerivedCategory (pA n)
  let κ := Functor.isoWhiskerLeft d.restriction.functor.mapDerivedCategory κ₀
  refine ⟨P, LB, p, pB, κ, ?_, hpB, ?_, ?_⟩
  · intro X n
    let e := d.restriction.functor.mapDerivedCategoryFactors.app X
    let Y := (d.restriction.functor.mapHomologicalComplex (.up ℤ)).obj X
    have hn := (pA n).naturality e.inv
    change (LA.unit.app Y ≫ LA.functor.map e.inv) ≫ (pA n).app _ ≫
      ((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
        (op n)).mapDerivedCategory.map e.hom ≫ _ = _
    simp only [Category.assoc]
    erw [← Category.assoc (LA.functor.map e.inv) ((pA n).app _) _, hn]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id]
    have hid := ((CategoryTheory.evaluation ℕᵒᵖ (sequenceCoefficientModules A)).obj
      (op n)).mapDerivedCategory.map_id (DerivedCategory.Q.obj Y)
    erw [hid, Category.id_comp]
    exact hpA Y n
  · intro X
    let e := d.restriction.functor.mapDerivedCategoryFactors.app X
    let Y := (d.restriction.functor.mapHomologicalComplex (.up ℤ)).obj X
    change (d.finite A).unit.app
        (((lim : (ℕᵒᵖ ⥤ sequenceCoefficientModules A) ⥤
          sequenceCoefficientModules A).mapHomologicalComplex (.up ℤ)).obj Y) ≫
        (d.finite A).functor.map (LA.unit.app Y ≫ LA.functor.map e.inv) ≫
        κ₀.hom.app (d.restriction.functor.mapDerivedCategory.obj (DerivedCategory.Q.obj X)) =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
        (preservesLimitNatIso (sequenceCoefficientSections A) (J := ℕᵒᵖ))
          (.up ℤ)).hom.app Y) ≫
        LB.unit.app (((sequenceTowerSections A).mapHomologicalComplex (.up ℤ)).obj Y) ≫
        LB.functor.map (d.tower.unit.app Y) ≫ LB.functor.map (d.tower.functor.map e.inv)
    have hn := κ₀.hom.naturality e.inv
    dsimp only [Functor.comp_map] at hn
    erw [Functor.map_comp, Category.assoc, hn]
    simpa only [Functor.comp_obj, Category.assoc] using congrArg
      (fun f ↦ f ≫ LB.functor.map (d.tower.functor.map e.inv)) (hκ₀ Y)
  · intro M n
    simpa only [κ, p, P, sectionsExactComposite, SequenceSectionsComparisons.global,
      Iso.symm_hom, SequenceSectionsComparisons.finiteEvaluation,
      SequenceSectionsComparisons.restrictedEvaluation, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
      Functor.comp_obj, Category.assoc] using congrArg
        (fun f ↦ f ≫ (d.finite A).functor.map
          ((sequenceRestrictionDerivedEvaluation d.restriction n).hom.app M) ≫
          (d.scalar (α.app (op n))).inv.app ((derivedSystemEvaluation B n).obj M))
        (hproj (d.restriction.functor.mapDerivedCategory.obj M) n)

end SheafOfModules
