/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.AlgebraicGeometry.ClopenStrictTowerRoosEquivalence
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing
public import Sheaf.AlgebraicGeometry.ProEtaleClopenTotalTensorKFlatDetection
public import Sheaf.AlgebraicGeometry.ProEtaleClopenUnboundedDerivedLocalization
import Sheaf.Algebra.Homology.RingIsomorphismTensorTransport
import all Sheaf.CategoryTheory.StrictRoosAdditiveComparison
import all Sheaf.CategoryTheory.InjectiveTowerRoosShifts
import WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexFunctorEquiv

/-! # Strict completed operation towers under clopen restriction

Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 3.4.12(4), p. 22;
Proposition 3.5.1(3) and Definition 3.5.2, p. 24.
(blueprint: lem-pur-clopen-completed-operation-towers).

The index n denotes the positive exponent n+1. The coefficient isomorphisms below
are the already recorded constant-section and inverse-limit comparisons. All tower
transitions and Roos maps are those of the recorded operation constructions.
-/

@[expose] public noncomputable section
-- Avoid scanning the large specified comparison types for unused finite instances.
-- Kernel checking and the mathematical declarations are unchanged.
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.ClopenRoos.modulesAbelian
  AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.hasDerived
universe t u w a b vA vB
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
namespace WeilConjectures.ClopenCompletedOperations

attribute [local irreducible] SheafOfModules.monoidalCategory
  unrestrictedIntegralReductionExistence integralScalarReduction

/-- The canonical restricted product followed by the level comparison, with each coordinate
fixed. Source: Bhatt--Scholze, Definition 3.4.10; Stacks 08TC
(blueprint: lem-pur-clopen-completed-operation-towers). -/
def productMap {A : Type a} {B : Type b} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] (C : ℕᵒᵖ ⥤ CochainComplex (A) ℤ)
    (D : ℕᵒᵖ ⥤ CochainComplex (B) ℤ)
    (α : ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (F.mapHomologicalComplex (.up ℤ))).obj C ≅ D) :
    (F.mapHomologicalComplex (.up ℤ)).obj (∏ᶜ (fun n : ℕ ↦ C.obj (op n))) ⟶
      ∏ᶜ (fun n : ℕ ↦ D.obj (op n)) :=
  piComparison (F.mapHomologicalComplex (.up ℤ)) (fun n : ℕ ↦ C.obj (op n)) ≫
    Limits.Pi.map (fun n : ℕ ↦ α.hom.app (op n))

/-- The diagonal strict cone normalization: both mapping-fibre coordinates are the
specified product map. This fixes the cone map before localization.
Source: Stacks 08TC; Bhatt--Scholze, Definition 3.4.10
(blueprint: lem-pur-clopen-completed-operation-towers). -/
def RoosNormalized {A : Type a} {B : Type b} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive]
    (C : ℕᵒᵖ ⥤ CochainComplex (A) ℤ)
    (D : ℕᵒᵖ ⥤ CochainComplex (B) ℤ)
    (α : ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (F.mapHomologicalComplex (.up ℤ))).obj C ≅ D)
    (β : (F.mapHomologicalComplex (.up ℤ)).obj ((integralOperationsRoosFunctor (A := A)).obj C) ≅
      (integralOperationsRoosFunctor (A := B)).obj D) : Prop :=
  (∀ r : ℤ, β.hom.f r ≫
      (CochainComplex.mappingCocone.fst
        (towerTransitionEndomorphism (K := fun n : ℕ ↦ D.obj (op n))
          (integralOperationsTowerStep D))).f r =
    (F).map
      ((CochainComplex.mappingCocone.fst
        (towerTransitionEndomorphism (K := fun n : ℕ ↦ C.obj (op n))
          (integralOperationsTowerStep C))).f r) ≫
          (productMap F C D α).f r) ∧
  (∀ r : ℤ, β.hom.f r ≫
      (CochainComplex.mappingCocone.snd
        (towerTransitionEndomorphism (K := fun n : ℕ ↦ D.obj (op n))
          (integralOperationsTowerStep D))).v r (r + -1) rfl =
    (F).map
      ((CochainComplex.mappingCocone.snd
        (towerTransitionEndomorphism (K := fun n : ℕ ↦ C.obj (op n))
          (integralOperationsTowerStep C))).v r (r + -1) rfl) ≫
          (productMap F C D α).f (r + -1))


/-- The canonical Roos map formed from restriction and the given strict tower isomorphism.
Source: Bhatt--Scholze 3.4.10; Stacks 08TC
(blueprint: lem-pur-clopen-completed-operation-towers). -/
def roosMap {A : Type a} {B : Type b} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) (D : ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (α : ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      (F.mapHomologicalComplex (.up ℤ))).obj C ≅ D)
    (β : integralOperationsRoosFunctor ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj
        (F.mapHomologicalComplex (.up ℤ)) ⋙ integralOperationsRoosFunctor) :
    (F.mapHomologicalComplex (.up ℤ)).obj (integralOperationsRoosFunctor.obj C) ⟶
      integralOperationsRoosFunctor.obj D :=
  β.hom.app C ≫ integralOperationsRoosFunctor.map α.hom

attribute [local irreducible] roosMap


set_option backward.defeqAttrib.useBackward true in
private theorem additive_roos_comparison
    {A : Type a} {B : Type b} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F] :
    ∃ β : integralOperationsRoosFunctor ⋙ F.mapHomologicalComplex (.up ℤ) ≅
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj (F.mapHomologicalComplex (.up ℤ)) ⋙
          integralOperationsRoosFunctor,
      ∀ C : ℕᵒᵖ ⥤ CochainComplex A ℤ,
        RoosNormalized F C (C ⋙ F.mapHomologicalComplex (.up ℤ)) (Iso.refl _) (β.app C) := by
  have : PreservesLimitsOfShape (Discrete ℕ) (F.mapHomologicalComplex (.up ℤ)) :=
    HomologicalComplex.preservesLimitsOfShape_of_eval _ (fun n ↦ by
      change PreservesLimitsOfShape (Discrete ℕ) (HomologicalComplex.eval A (.up ℤ) n ⋙ F)
      infer_instance)
  let U := (HomologicalComplex.functorEquivalence A (.up ℤ) ℕᵒᵖ).inverse
  have (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) : IsIso (roosComparison F (U.obj C)) := by
    dsimp only [roosComparison]
    infer_instance
  let β : integralOperationsRoosFunctor ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj (F.mapHomologicalComplex (.up ℤ)) ⋙
        integralOperationsRoosFunctor :=
    NatIso.ofComponents (fun C ↦ by
      change (F.mapHomologicalComplex (.up ℤ)).obj (strictRoosComplex (U.obj C)) ≅
        strictRoosComplex ((roosTowerMap F).obj (U.obj C))
      exact roosTheta F (U.obj C)) (by
      intro C D f
      have h := roosTheta_map F _ _ (strictRoosProductMap_comm (U.map f)) _ _
        (strictRoosProductMap_comm ((roosTowerMap F).map (U.map f)))
        (roosComparison_map F (U.map f)) (roosComparison_map F (U.map f))
      exact h)
  refine ⟨β, ?_⟩
  intro C
  unfold RoosNormalized
  have hcoord (p : ℤ) : (roosTheta F (U.obj C)).hom.f (p + 1) ≫
      (roosχ ((roosTowerMap F).obj (U.obj C)) p).hom =
      F.map (roosχ (U.obj C) p).hom ≫
        F.biprodComparison ((strictRoosProduct (U.obj C)).X p)
          ((strictRoosProduct (U.obj C)).X (p + 1)) ≫
        biprod.map ((roosComparison F (U.obj C)).f p)
          ((roosComparison F (U.obj C)).f (p + 1)) :=
    roosTheta_coordinates F (U.obj C) p
  have hprod : productMap F C (C ⋙ F.mapHomologicalComplex (.up ℤ)) (Iso.refl _) =
      roosComparison F (U.obj C) := by
    unfold productMap roosComparison
    have hid : (Limits.Pi.map (fun n : ℕ ↦
        𝟙 ((F.mapHomologicalComplex (.up ℤ)).obj (C.obj (op n))))) = 𝟙 _ :=
      Limits.Pi.map_id
    exact (congrArg (fun z ↦ piComparison (F.mapHomologicalComplex (.up ℤ))
      (fun n ↦ C.obj (op n)) ≫ z) hid).trans (Category.comp_id _)
  constructor
  · intro r
    obtain ⟨p, rfl⟩ : ∃ p : ℤ, r = p + 1 := ⟨r - 1, by omega⟩
    have h := congrArg (fun z ↦ z ≫ biprod.snd) (hcoord p)
    simp only [Category.assoc] at h
    erw [biprod.map_snd, Functor.biprodComparison_snd_assoc] at h
    simp only [← F.map_comp_assoc, roosχ_snd] at h
    erw [roosχ_snd] at h
    rw [hprod]
    exact h
  · intro r
    obtain ⟨p, rfl⟩ : ∃ p : ℤ, r = p + 1 := ⟨r - 1, by omega⟩
    have h := congrArg (fun z ↦ z ≫ biprod.fst) (hcoord p)
    simp only [Category.assoc] at h
    erw [biprod.map_fst, Functor.biprodComparison_fst_assoc] at h
    simp only [← F.map_comp_assoc, roosχ_fst] at h
    erw [roosχ_fst] at h
    rw [hprod]
    have hq (q : ℤ) (hq : p + 1 + -1 = q) :
        (roosTheta F (U.obj C)).hom.f (p + 1) ≫
          (CochainComplex.mappingCocone.snd (roosU ((roosTowerMap F).obj (U.obj C)))).v
            (p + 1) q hq =
        F.map ((CochainComplex.mappingCocone.snd (roosU (U.obj C))).v
          (p + 1) q hq) ≫ (roosComparison F (U.obj C)).f q := by
      obtain rfl : q = p := by omega
      exact h
    exact hq _ rfl

set_option backward.defeqAttrib.useBackward true in
private theorem scalarTransport_equivalence
    {C : Type a} [Category.{vA} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{b}} (c : R ≅ S) :
    (SheafOfModules.restrictScalars.{vB} c.hom).IsEquivalence := by
  let ec : C ≌ C := CategoryTheory.Equivalence.refl
  have : ec.functor.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  have : ec.inverse.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  let e := SheafOfModules.pushforwardPushforwardEquivalence (J := J) (K := J)
    ec c.hom c.inv
    (by
      ext U x
      dsimp [ec, CategoryTheory.Equivalence.refl]
      rw [CategoryTheory.Functor.map_id]
      exact congrArg (fun f : S ⟶ S ↦ f.hom.app U x) c.inv_hom_id.symm)
    (by
      ext U x
      dsimp [ec, CategoryTheory.Equivalence.refl]
      rw [CategoryTheory.Functor.map_id]
      exact congrArg (fun f : R ⟶ R ↦ f.hom.app U x) c.hom_inv_id)
  change e.functor.IsEquivalence
  exact e.isEquivalence_functor

variable (X : Scheme.{t}) (I : Type w) [Finite I] (Xi : I → Scheme.{t})
  (j : ∀ i, Xi i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
  (hd : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
  (hc : ∀ x : X, ∃ i, x ∈ Set.range (j i))
  (l : ℕ) [Fact l.Prime] (hl : IsUnit (l : Γ(X, ⊤)))
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The existing finite coefficient comparison, uniquely fixed on constant sections.
Source: Bhatt--Scholze, Definition 3.4.10; clopen module gluing coefficient clause
(blueprint: lem-pur-clopen-completed-operation-towers). -/
def finiteIso (i : I) (n : ℕ) :=
  (Scheme.ProEt.clopen_integral_coefficients X I Xi j hd hc l hl E).choose i n

/-- The existing inverse-limit coefficient comparison, fixed by all finite projections.
Source: Bhatt--Scholze, Definition 3.5.2; clopen module gluing coefficient clause
(blueprint: lem-pur-clopen-completed-operation-towers). -/
def ringIso (i : I) :=
  (Scheme.ProEt.clopen_integral_coefficients X I Xi j hd hc l hl E).choose_spec.choose i

attribute [local irreducible] ringIso finiteIso completedIntegralCoefficientSheafUnrestricted
  HasDerivedCategory.standard

/-- Sectionwise restriction with the canonical completed coefficient action.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: lem-pur-clopen-completed-operation-towers). -/
def restriction (i : I) : integralTowerModules l E X ⥤ integralTowerModules l E (Xi i) :=
  Scheme.ProEt.clopenModuleRestriction (j i)
    (completedIntegralCoefficientSheafUnrestricted l E X) ⋙
      SheafOfModules.restrictScalars (ringIso X I Xi j hd hc l hl E i).inv

/-- Restriction and scalar transport retain addition of maps.
Source: Stacks 04TR (blueprint: lem-pur-clopen-completed-operation-towers). -/
instance restrictionAdditive (i : I) : (restriction X I Xi j hd hc l hl E i).Additive :=
  inferInstanceAs ((Scheme.ProEt.clopenModuleRestriction (j i)
    (completedIntegralCoefficientSheafUnrestricted l E X) ⋙
      SheafOfModules.restrictScalars (ringIso X I Xi j hd hc l hl E i).inv).Additive)

/-- Exactness of the same normalized restriction, including the empty component.
Source: Stacks 04TR, 015F (blueprint: lem-pur-clopen-completed-operation-towers).
Proof: clopen unbounded localization gives exact sectionwise restriction. Transport
along the coefficient isomorphism is an equivalence, so it preserves kernels and
cokernels. Their composite is the displayed restriction. -/
theorem restriction_exact (i : I) :
    PreservesFiniteLimits (restriction X I Xi j hd hc l hl E i) ∧
      PreservesFiniteColimits (restriction X I Xi j hd hc l hl E i) := by
  let R := completedIntegralCoefficientSheafUnrestricted l E X
  have h := Scheme.ProEt.ClopenLocalization.restriction_exact.{t, max u (t + 1), u, 0}
    (j i) R
  have : PreservesFiniteLimits (Scheme.ProEt.clopenModuleRestriction (j i) R) := h.1
  have : PreservesFiniteColimits (Scheme.ProEt.clopenModuleRestriction (j i) R) := h.2
  have : (SheafOfModules.restrictScalars.{max u (t + 1)}
      (ringIso X I Xi j hd hc l hl E i).inv).IsEquivalence :=
    scalarTransport_equivalence (ringIso X I Xi j hd hc l hl E i).symm
  constructor
  · change PreservesFiniteLimits
      (Scheme.ProEt.clopenModuleRestriction (j i) R ⋙
        SheafOfModules.restrictScalars (ringIso X I Xi j hd hc l hl E i).inv)
    infer_instance
  · change PreservesFiniteColimits
      (Scheme.ProEt.clopenModuleRestriction (j i) R ⋙
        SheafOfModules.restrictScalars (ringIso X I Xi j hd hc l hl E i).inv)
    infer_instance

/-- Kernels are preserved by the recorded exact restriction.
Source: Stacks 015F (blueprint: lem-pur-clopen-completed-operation-towers). -/
instance restrictionLimits (i : I) :
    PreservesFiniteLimits (restriction X I Xi j hd hc l hl E i) :=
  (restriction_exact X I Xi j hd hc l hl E i).1

/-- Cokernels are preserved by the recorded exact restriction.
Source: Stacks 015F (blueprint: lem-pur-clopen-completed-operation-towers). -/
instance restrictionColimits (i : I) :
    PreservesFiniteColimits (restriction X I Xi j hd hc l hl E i) :=
  (restriction_exact X I Xi j hd hc l hl E i).2

/-- Degreewise ordinary restriction of unbounded complexes.
Source: Stacks 015F (blueprint: lem-pur-clopen-completed-operation-towers). -/
abbrev cxRestriction (i : I) :=
  (restriction X I Xi j hd hc l hl E i).mapHomologicalComplex (.up ℤ)

/-- Ordinary derived restriction, without derived completion of the input.
Source: Stacks 015F (blueprint: lem-pur-clopen-completed-operation-towers). -/
abbrev dRestriction (i : I) := (restriction X I Xi j hd hc l hl E i).mapDerivedCategory

/-- Restriction in the strict inverse-system category retains every transition.
Source: Bhatt--Scholze, Definition 3.5.2
(blueprint: lem-pur-clopen-completed-operation-towers). -/
abbrev towerRestriction (i : I) :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (cxRestriction X I Xi j hd hc l hl E i)

/-- The restriction of an admissible resolving complex is admissible.
Source: Stacks 06YN, 03ER (blueprint: lem-pur-clopen-completed-operation-towers).
Proof: clopen total-tensor K-flat detection preserves flat terms and K-flatness.
Transport along ringIso preserves the tensor test and exactness. No boundedness
or derived completeness is required. -/
theorem goodRestriction_property (i : I)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory) :
    integralOperationsGoodComplex l E (Xi i)
      ((cxRestriction X I Xi j hd hc l hl E i).obj P.obj) := by
  let R := completedIntegralCommRingSheafUnrestricted l E X
  let S := (Scheme.ProEt.clopenTensorRings (j i)).obj R
  let T := completedIntegralCommRingSheafUnrestricted l E (Xi i)
  let ff := fullyFaithfulSheafCompose (Scheme.ProEt.topology (Xi i))
    CommRingCat.fullyFaithfulForget₂ToRingCat
  let c : T ≅ S := ff.preimageIso (ringIso X I Xi j hd hc l hl E i).symm
  have hc' : (sheafCompose (Scheme.ProEt.topology (Xi i))
      (forget₂ CommRingCat RingCat)).map c.hom =
      (ringIso X I Xi j hd hc l hl E i).inv := by
    exact ff.map_preimage _
  let := HasDerivedCategory.standard
    (SheafOfModules.scalarModules (Scheme.ProEt.topology (Xi i)) S)
  let := HasDerivedCategory.standard
    (SheafOfModules.scalarModules (Scheme.ProEt.topology (Xi i)) T)
  obtain ⟨tr⟩ := SheafOfModules.ringIso_tensor_transport c
  have h := Scheme.ProEt.clopen_total_tensor_kflat_detection X I Xi j hd hc R
  have hP := P.property
  change CochainComplex.IsKFlatIndependentCoefficients (R := R) P.obj ∧
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology X)
      (R := R) (P.obj.X n)) at hP
  constructor
  · have hK := (h.2.1 P.obj).1 hP.1 i
    have hh := (tr.kflat_iff
      ((Scheme.ProEt.clopenTensorComplexRestriction (j i) R).obj P.obj)).2 hK
    dsimp only [SheafOfModules.scalarRestriction] at hh
    simp only [hc'] at hh
    exact hh
  · intro n
    have hF := (h.1 (P.obj.X n)).1 (hP.2 n) i
    have hh := (tr.flat_iff
      ((Scheme.ProEt.clopenTensorRestriction (j i) R).obj (P.obj.X n))).2 hF
    dsimp only [SheafOfModules.scalarRestriction] at hh
    simp only [hc'] at hh
    exact hh

/-- Restriction on the existing resolving full subcategories.
Source: Stacks 06YN (blueprint: lem-pur-clopen-completed-operation-towers). -/
def goodRestriction (i : I) :
    (integralOperationsGoodComplex l E X).FullSubcategory ⥤
      (integralOperationsGoodComplex l E (Xi i)).FullSubcategory :=
  ObjectProperty.lift _ ((integralOperationsGoodComplex l E X).ι ⋙
    cxRestriction X I Xi j hd hc l hl E i)
      (goodRestriction_property X I Xi j hd hc l hl E i)

/-- The actual total-tensor tower on two admissible resolutions.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: lem-pur-clopen-completed-operation-towers). -/
abbrev tensorTower :=
  ((integralOperationsGoodComplex l E X).ι.prod (integralOperationsGoodComplex l E X).ι) ⋙
    integralOperationsTensorTowerFunctor l E X

/-- The localized good complex and its exact restriction have the canonical comparison.
Source: Stacks 015F (blueprint: lem-pur-clopen-completed-operation-towers). -/
def localizationIso (i : I)
    (P : (integralOperationsGoodComplex l E X).FullSubcategory) :
    (dRestriction X I Xi j hd hc l hl E i).obj (DerivedCategory.Q.obj P.obj) ≅
      DerivedCategory.Q.obj ((goodRestriction X I Xi j hd hc l hl E i).obj P).obj :=
  ((restriction X I Xi j hd hc l hl E i).mapDerivedCategoryFactors).app P.obj

private theorem restriction_products (i : I) :
    PreservesLimitsOfShape (Discrete ℕ) (restriction X I Xi j hd hc l hl E i) := by
  let R := completedIntegralCoefficientSheafUnrestricted l E X
  let Ri := (Scheme.ProEt.clopenRingRestriction (j i)).obj R
  let V := SheafOfModules.forget.{max u (t + 1)} Ri ⋙
    PresheafOfModules.toPresheaf Ri.obj
  have : PreservesLimitsOfShape (Discrete ℕ)
      (Scheme.ProEt.clopenModuleRestriction (j i) R ⋙ V) := by
    change PreservesLimitsOfShape (Discrete ℕ)
      ((SheafOfModules.forget.{max u (t + 1)} R ⋙
        PresheafOfModules.toPresheaf R.obj) ⋙
        (Functor.whiskeringLeft (Xi i).ProEtᵒᵖ X.ProEtᵒᵖ
          AddCommGrpCat.{max u (t + 1)}).obj
            (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (j i))).op)
    infer_instance
  have : ReflectsLimitsOfShape (Discrete ℕ) V :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  have : PreservesLimitsOfShape (Discrete ℕ)
      (Scheme.ProEt.clopenModuleRestriction (j i) R) :=
    preservesLimitsOfShape_of_reflects_of_preserves _ V
  have : (SheafOfModules.restrictScalars.{max u (t + 1)}
      (ringIso X I Xi j hd hc l hl E i).inv).IsEquivalence :=
    scalarTransport_equivalence (ringIso X I Xi j hd hc l hl E i).symm
  change PreservesLimitsOfShape (Discrete ℕ)
    (Scheme.ProEt.clopenModuleRestriction (j i) R ⋙
      SheafOfModules.restrictScalars (ringIso X I Xi j hd hc l hl E i).inv)
  infer_instance

/-- Strict cone comparisons are natural for every strict tower morphism, not only
those obtained from a map of resolutions.
Source: Stacks 08TC (blueprint: lem-pur-clopen-completed-operation-towers).
Proof: compare termwise products by their projections. The levelwise coefficient
transport preserves the transition equation. The resulting product square for 1-s
induces the diagonal map on the actual shifted cones. The inverse product and
cone maps prove invertibility, and their projection coordinates prove naturality. -/
theorem roos_restriction (i : I) :
    ∃ β : integralOperationsRoosFunctor ⋙ cxRestriction X I Xi j hd hc l hl E i ≅
        towerRestriction X I Xi j hd hc l hl E i ⋙ integralOperationsRoosFunctor,
      ∀ C : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E X) ℤ,
        RoosNormalized (restriction X I Xi j hd hc l hl E i) C
          ((towerRestriction X I Xi j hd hc l hl E i).obj C)
          (Iso.refl _) (β.app C) := by
  have := restriction_products X I Xi j hd hc l hl E i
  exact additive_roos_comparison (restriction X I Xi j hd hc l hl E i)

attribute [local irreducible] DerivedCategory.Q Functor.mapDerivedCategoryFactors


/-- A double reduction pure tensor in the actual signed total direct-sum summand.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: lem-pur-clopen-completed-operation-towers). -/
def tensorPure
    (P Q : (integralOperationsGoodComplex l E X).FullSubcategory)
    (n : ℕ) (p q : ℤ) (V : X.ProEtᵒᵖ)
    (a b : (integralCoefficientSheaf l E X n).obj.obj V)
    (x : (P.obj.X p).val.obj V) (y : (Q.obj.X q).val.obj V) :
    (((((integralOperationsTensorTowerFunctor l E X).obj (P.obj, Q.obj)).obj
      (op n)).X (p + q)).val.obj V) :=
  integralOperationsTotalTensorSection l E X n P.obj Q.obj p q V
    (unrestrictedIntegralTensorSection l E X n (P.obj.X p) V a x)
    (unrestrictedIntegralTensorSection l E X n (Q.obj.X q) V b y)


/-- The defining equality between the recorded operation complex and its strict Roos model.
Source: Bhatt--Scholze 3.4.10
(blueprint: lem-pur-clopen-completed-operation-towers). -/
def tensorRoosIso (P Q : (integralOperationsGoodComplex l E X).FullSubcategory) :
    (integralOperationsTensorComplexFunctor l E X).obj (P.obj, Q.obj) ≅
      integralOperationsRoosFunctor.obj ((tensorTower X l E).obj (P, Q)) := Iso.refl _

/-- The recorded completed tensor comparison expressed in its defining strict Roos model.
Source: Bhatt--Scholze 3.4.10
(blueprint: lem-pur-clopen-completed-operation-towers). -/
def tensorModelComparison
    (P Q : (integralOperationsGoodComplex l E X).FullSubcategory) :
    (integralCompletedTensor l E X).obj
      (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≅
    DerivedCategory.Q.obj (integralOperationsRoosFunctor.obj
      ((tensorTower X l E).obj (P, Q))) :=
  (integralCompletedTensorComparison l E X).app (P, Q) ≪≫
    DerivedCategory.Q.mapIso (tensorRoosIso X l E P Q)

attribute [local irreducible] tensorModelComparison tensorRoosIso
  Functor.mapDerivedCategory integralCompletedTensor integralCompletedTensorComparison

attribute [local irreducible] integralOperationsTensorComplexFunctor
  integralOperationsTensorOnGood

attribute [local irreducible] constantSheaf presheafToSheaf
  completedIntegralCommRingSheafUnrestricted

attribute [local irreducible] integralOperationsRoosFunctor

/-- The tensor tower, pure-tensor formula, strict cone map and its normalized descent.
These are conclusions, rather than additional assumptions on the input complexes.
Source: Bhatt--Scholze, Definition 3.4.10 and Lemma 3.4.12(4)
(blueprint: lem-pur-clopen-completed-operation-towers). -/
def TensorComparison (i : I) : Prop :=
  ∃ tower : tensorTower X l E ⋙ towerRestriction X I Xi j hd hc l hl E i ≅
  ((goodRestriction X I Xi j hd hc l hl E i).prod
    (goodRestriction X I Xi j hd hc l hl E i)) ⋙ tensorTower (Xi i) l E,
  (∀ (P Q : (integralOperationsGoodComplex l E X).FullSubcategory)
    (n : ℕ) (p q : ℤ) (V : (Xi i).ProEt)
    (a b : (integralCoefficientSheaf l E X n).obj.obj
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (j i))).obj V)))
    (x : (P.obj.X p).val.obj
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (j i))).obj V)))
    (y : (Q.obj.X q).val.obj
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (j i))).obj V))),
  ((((tower.hom.app (P, Q)).app (op n)).f (p + q)).val.app (op V))
    (tensorPure X l E P Q n p q _ a b x y) =
  tensorPure (Xi i) l E
    ((goodRestriction X I Xi j hd hc l hl E i).obj P)
    ((goodRestriction X I Xi j hd hc l hl E i).obj Q) n p q (op V)
    ((finiteIso X I Xi j hd hc l hl E i n).hom.hom.app (op V) a)
    ((finiteIso X I Xi j hd hc l hl E i n).hom.hom.app (op V) b) x y) ∧
  ∃ roos : integralOperationsRoosFunctor ⋙ cxRestriction X I Xi j hd hc l hl E i ≅
  towerRestriction X I Xi j hd hc l hl E i ⋙ integralOperationsRoosFunctor,
  (∀ C : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E X) ℤ,
  RoosNormalized (restriction X I Xi j hd hc l hl E i) C
    ((towerRestriction X I Xi j hd hc l hl E i).obj C) (Iso.refl _) (roos.app C)) ∧
  ∃ derived : integralCompletedTensor l E X ⋙ dRestriction X I Xi j hd hc l hl E i ≅
  ((dRestriction X I Xi j hd hc l hl E i).prod
    (dRestriction X I Xi j hd hc l hl E i)) ⋙ integralCompletedTensor l E (Xi i),
  (∀ P Q : (integralOperationsGoodComplex l E X).FullSubcategory,
  (dRestriction X I Xi j hd hc l hl E i).map
      (X := (integralCompletedTensor l E X).obj
        (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj))
      (Y := DerivedCategory.Q.obj (integralOperationsRoosFunctor.obj
        ((tensorTower X l E).obj (P, Q))))
      (tensorModelComparison X l E P Q).hom ≫
    ((restriction X I Xi j hd hc l hl E i).mapDerivedCategoryFactors).hom.app
      (integralOperationsRoosFunctor.obj ((tensorTower X l E).obj (P, Q))) ≫
    DerivedCategory.Q.map
      (X := (cxRestriction X I Xi j hd hc l hl E i).obj
        (integralOperationsRoosFunctor.obj ((tensorTower X l E).obj (P, Q))))
      (Y := integralOperationsRoosFunctor.obj ((tensorTower (Xi i) l E).obj
        (((goodRestriction X I Xi j hd hc l hl E i).obj P),
         ((goodRestriction X I Xi j hd hc l hl E i).obj Q))))
      (roosMap (restriction X I Xi j hd hc l hl E i)
        ((tensorTower X l E).obj (P, Q))
        ((tensorTower (Xi i) l E).obj
          ((goodRestriction X I Xi j hd hc l hl E i).obj P,
           (goodRestriction X I Xi j hd hc l hl E i).obj Q))
        (tower.app (P, Q)) roos) =
  derived.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
    (integralCompletedTensor l E (Xi i)).map
      (X := ((dRestriction X I Xi j hd hc l hl E i).obj (DerivedCategory.Q.obj P.obj),
        (dRestriction X I Xi j hd hc l hl E i).obj (DerivedCategory.Q.obj Q.obj)))
      (Y := (DerivedCategory.Q.obj ((goodRestriction X I Xi j hd hc l hl E i).obj P).obj,
        DerivedCategory.Q.obj ((goodRestriction X I Xi j hd hc l hl E i).obj Q).obj))
      ((localizationIso X I Xi j hd hc l hl E i P).hom,
       (localizationIso X I Xi j hd hc l hl E i Q).hom) ≫
    (tensorModelComparison (Xi i) l E
      ((goodRestriction X I Xi j hd hc l hl E i).obj P)
      ((goodRestriction X I Xi j hd hc l hl E i).obj Q)).hom)

variable (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- The strict extension tower on the existing admissible representatives.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: lem-pur-clopen-completed-operation-towers). -/
abbrev scalarTower := (integralOperationsGoodComplex l E X).ι ⋙
  integralScalarTowerFunctor l E L ι X

/-- The defining equality for the recorded scalar-extension strict Roos model.
Source: Bhatt--Scholze 3.4.10
(blueprint: lem-pur-clopen-completed-operation-towers). -/
def scalarRoosIso (P : (integralOperationsGoodComplex l E X).FullSubcategory) :
    (integralScalarComplexFunctor l E L ι X).obj P.obj ≅
      integralOperationsRoosFunctor.obj ((scalarTower X l E L ι).obj P) := Iso.refl _

/-- The recorded scalar-extension comparison expressed in its defining strict Roos model.
Source: Bhatt--Scholze 3.4.10
(blueprint: lem-pur-clopen-completed-operation-towers). -/
def scalarModelComparison
    (P : (integralOperationsGoodComplex l E X).FullSubcategory) :
    (integralScalarExtensionOfUniverses l E L ι X).obj (DerivedCategory.Q.obj P.obj) ≅
    DerivedCategory.Q.obj (integralOperationsRoosFunctor.obj
      ((scalarTower X l E L ι).obj P)) :=
  (integralScalarExtensionComparisonOfUniverses l E L ι X).app P ≪≫
    DerivedCategory.Q.mapIso (scalarRoosIso X l E L ι P)

attribute [local irreducible] scalarModelComparison scalarRoosIso
  integralScalarExtensionOfUniverses integralScalarExtensionComparisonOfUniverses

attribute [local irreducible] integralScalarComplexFunctor integralScalarOnGood

/-- The finite-extension comparison retains quotient inclusion, units, transitions,
the strict cone normalization, and its descent on all derived morphisms.
Source: Bhatt--Scholze, Definition 3.4.10 and Proposition 3.5.1(3)
(blueprint: lem-pur-clopen-completed-operation-towers). -/
def ScalarComparison (i : I) : Prop :=
  ∃ tower : scalarTower X l E L ι ⋙ towerRestriction X I Xi j hd hc l hl L i ≅
  goodRestriction X I Xi j hd hc l hl E i ⋙ scalarTower (Xi i) l E L ι,
  (∀ (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (n : ℕ) (p : ℤ) (V : (Xi i).ProEt)
    (a : (integralCoefficientSheaf l L X n).obj.obj
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (j i))).obj V)))
    (x : (P.obj.X p).val.obj
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (j i))).obj V))),
  ((((tower.hom.app P).app (op n)).f p).val.app (op V))
    (integralScalarTensorSection l E L ι X n (P.obj.X p) _ a x) =
  integralScalarTensorSection l E L ι (Xi i) n
    (((goodRestriction X I Xi j hd hc l hl E i).obj P).obj.X p) (op V)
    ((finiteIso X I Xi j hd hc l hl L i n).hom.hom.app (op V) a) x) ∧
  (∀ (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (n : ℕ) (p : ℤ) (V : (Xi i).ProEt)
    (x : (P.obj.X p).val.obj
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (j i))).obj V))),
  ((((tower.hom.app P).app (op n)).f p).val.app (op V))
    (integralScalarTensorSection l E L ι X n (P.obj.X p) _ 1 x) =
  integralScalarTensorSection l E L ι (Xi i) n
    (((goodRestriction X I Xi j hd hc l hl E i).obj P).obj.X p) (op V) 1 x) ∧
  ∃ roos : integralOperationsRoosFunctor ⋙ cxRestriction X I Xi j hd hc l hl L i ≅
  towerRestriction X I Xi j hd hc l hl L i ⋙ integralOperationsRoosFunctor,
  (∀ C : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l L X) ℤ,
  RoosNormalized (restriction X I Xi j hd hc l hl L i) C
    ((towerRestriction X I Xi j hd hc l hl L i).obj C) (Iso.refl _) (roos.app C)) ∧
  ∃ derived : integralScalarExtensionOfUniverses l E L ι X ⋙
    dRestriction X I Xi j hd hc l hl L i ≅
  dRestriction X I Xi j hd hc l hl E i ⋙
    integralScalarExtensionOfUniverses l E L ι (Xi i),
  (∀ P : (integralOperationsGoodComplex l E X).FullSubcategory,
  (dRestriction X I Xi j hd hc l hl L i).map
      (X := (integralScalarExtensionOfUniverses l E L ι X).obj
        (DerivedCategory.Q.obj P.obj))
      (Y := DerivedCategory.Q.obj (integralOperationsRoosFunctor.obj
        ((scalarTower X l E L ι).obj P)))
      (scalarModelComparison X l E L ι P).hom ≫
    ((restriction X I Xi j hd hc l hl L i).mapDerivedCategoryFactors).hom.app
      (integralOperationsRoosFunctor.obj ((scalarTower X l E L ι).obj P)) ≫
    DerivedCategory.Q.map
      (X := (cxRestriction X I Xi j hd hc l hl L i).obj
        (integralOperationsRoosFunctor.obj ((scalarTower X l E L ι).obj P)))
      (Y := integralOperationsRoosFunctor.obj ((scalarTower (Xi i) l E L ι).obj
        ((goodRestriction X I Xi j hd hc l hl E i).obj P)))
      (roosMap (restriction X I Xi j hd hc l hl L i)
        ((scalarTower X l E L ι).obj P)
        ((scalarTower (Xi i) l E L ι).obj
          ((goodRestriction X I Xi j hd hc l hl E i).obj P))
        (tower.app P) roos) =
  derived.hom.app (DerivedCategory.Q.obj P.obj) ≫
    (integralScalarExtensionOfUniverses l E L ι (Xi i)).map
      (localizationIso X I Xi j hd hc l hl E i P).hom ≫
    (scalarModelComparison (Xi i) l E L ι
      ((goodRestriction X I Xi j hd hc l hl E i).obj P)).hom)
attribute [local irreducible] TensorComparison ScalarComparison
  integralOperationsGoodComplex integralOperationsGoodLocalization
  integralOperationsTensorTowerFunctor integralScalarTowerFunctor
  restriction goodRestriction

set_option backward.isDefEq.respectTransparency true in
/-- Strict tensor and scalar-extension towers, their normalized derived comparisons,
coefficient units and quotient maps, for arbitrary unbounded derived inputs.
Source: Bhatt--Scholze, Definition 3.4.10, Lemma 3.4.12(4), Proposition 3.5.1(3)
and Definition 3.5.2 (blueprint: lem-pur-clopen-completed-operation-towers).

Proof (the node's eight steps):
1. Clopen ringed module gluing supplies finite and completed coefficient identifications,
including 1 and all projections. Total-tensor K-flat detection and unbounded localization
make the restricted flat-term K-flat resolutions admissible.
2. The ordinary scalar comparison for each completed projection is linear after scalar
restriction, with formula p tensor a mapped to r(p) tensor r(a); a=1 gives the unit.
3. Combine the total-complex comparison with the two scalar comparisons. On every (p,q)
direct-sum summand it has the stated double pure-tensor formula and signed differential.
4. Both transition-square paths reduce both coefficient factors. Tensor's bilinear
universal property and coproduct extensionality make the squares equal. Conjugation gives
compatibility with all strict tower maps.
5. Apply the same calculation to rho=(iota)_X pi_E. Functorial constant sheafification
preserves iota, and clopen gluing for L preserves pi_L. The tensor formula preserves every
unit and quotient transition, including ramified extensions.
6. The strict tower Roos equivalence compares products by their projections; the square
for 1-s gives the diagonal cone isomorphism (y,x) mapped to (Ay,Ax).
7. Localize using the defining operation comparisons. Resolve arbitrary objects by
flat-term K-flat complexes, extend natural transformations using the resolving-class
lemma and the quasi-isomorphism fraction calculus, then descend through the localization
universal property, in both variables for tensor. Uniqueness gives compatibility with
every resolution computation and independence of all resolution choices.
8. Empty components and the empty partition are the zero cases of clopen gluing.
No boundedness, derived completeness, or unramifiedness is used. -/
theorem clopen_completed_operation_towers :
    (∀ i : I, TensorComparison X I Xi j hd hc l hl E i) ∧
    (∀ (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
      (ι : E →ₐ[Padic l] L) (i : I),
      ScalarComparison X I Xi j hd hc l hl E L ι i) := by
  sorry

end WeilConjectures.ClopenCompletedOperations
