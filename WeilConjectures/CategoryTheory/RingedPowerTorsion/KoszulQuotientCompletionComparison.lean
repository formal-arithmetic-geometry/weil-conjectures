/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.CategoryTheory.PrincipalQuotientCompletion.PrincipalQuotientCompletionModel
public import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeBasic
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all WeilConjectures.CategoryTheory.StrictRoosDerivation
import all WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
import all WeilConjectures.ProperBaseChange.RingedStrictTowerHomotopyLimitIndependentCoefficients
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.CategoryTheory.Triangulated.Triangulated
import all WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.CategoryTheory.PrincipalQuotientCompletion.PrincipalQuotientCompletionExists
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all WeilConjectures.Algebra.Homology.TotalTensorSigns.TotalTensorHomotopyConeSigns
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.PerfectReductionRoos.PerfectReductionKoszulDeltaData
import WeilConjectures.CategoryTheory.PerfectReductionRoos.PerfectReductionRoosData
import WeilConjectures.SmoothPurity.SheafRingCoefficientOrdinaryAdjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.CategoryTheory.RingedPowerTorsion.SignedDoubleRoosChainIso
import all WeilConjectures.CategoryTheory.RingedPowerTorsion.SignedDoubleRoosAugmentation
import all WeilConjectures.CategoryTheory.RoosConeCalculus.RoosConeCalculus

/-! # From raw Koszul completion to universal quotient completion

Source: Bhatt--Scholze, Lemmas 3.4.9 and 3.5.5; Stacks Tags 06YT and 0941.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r w a b

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory.RingedPowerTorsion

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  (R : Sheaf J CommRingCat.{r})

set_option hygiene false in
local notation "A" => ringedSiteModules.{r}
  (SheafOfModules.derivedChangeRingIndependentCoefficients J R)
set_option hygiene false in
local notation "Section" => (SheafOfModules.unit
  (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance] SheafOfModules.monoidalCategory
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

private theorem principalKoszul_term_flat (t : Section) (n : ℕ) (i : ℤ) :
    SheafOfModules.IsFlatOnSite (J := J) (R := R) ((principalKoszul R t n).X i) := by
  let := SheafOfModules.tensorPreadditive R
  let := SheafOfModules.symmetricCategory R
  have (M : A) : PreservesColimitsOfSize.{0, 0} (tensorLeft M) := by
    have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R M
    exact preservesColimitsOfSize_shrink (tensorLeft M)
  have (M : A) : PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  let S := (CochainComplex.singleFunctor A 0).obj (SheafOfModules.unit
    (SheafOfModules.derivedChangeRingIndependentCoefficients J R))
  let f := principalKoszulScalarComplex R t n
  have hs (j : ℤ) : ObjectProperty.flat (S.X j) := by
    by_cases hj : j = 0
    · exact ObjectProperty.prop_of_iso _
        (HomologicalComplex.singleObjXIsoOfEq (.up ℤ) 0 _ j hj).symm
        (ObjectProperty.prop_unit _)
    · exact ObjectProperty.prop_of_isZero _
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hj)
  have hb : ObjectProperty.flat (S.X (i + 1) ⊞ S.X i) :=
    ObjectProperty.prop_biprod_of_isClosedUnderBinaryProducts _ _ _ (hs _) (hs _)
  have h : ObjectProperty.flat ((principalKoszul R t n).X i) :=
    ObjectProperty.prop_of_iso _
      (HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) rfl).symm hb
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R _).symm h.2

private theorem principalKoszul_kflat (t : Section) (n : ℕ) :
    CochainComplex.IsKFlatIndependentCoefficients (R := R) (principalKoszul R t n) := by
  let := SheafOfModules.tensorPreadditive R
  let S := (CochainComplex.singleFunctor A 0).obj (SheafOfModules.unit
    (SheafOfModules.derivedChangeRingIndependentCoefficients J R))
  have : (principalKoszul R t n).IsStrictlyLE 0 := by
    apply (CochainComplex.isStrictlyLE_iff _ 0).2
    intro i hi
    apply (CochainComplex.mappingCone.isZero_X_iff _ i).2
    exact ⟨S.isZero_of_isStrictlyLE 0 (i + 1) (by omega),
      S.isZero_of_isStrictlyLE 0 i hi⟩
  exact SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    R _ 0 (principalKoszul_term_flat R t n)

variable [HasDerivedCategory.{w} (ringedSiteModules.{r}
    (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
  [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{r}
    (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]

set_option maxHeartbeats 1600000 in
-- Unfolding the specified transposed Roos map exceeds the default heartbeat budget.
private theorem quotientComparison_quasiIso
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (ht : Mono (globalSectionMultiplication R t))
    (P : CochainComplex (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    QuasiIso (quotientComparison R t P) := by
  have ha : QuasiIso (koszulTowerComplexMap R (koszulTensorTowerComparison R P t)) := by
    apply (HomologicalComplex.quasiIso_iff_evaluation _).mpr
    intro n
    exact kFlatTensorPreservesQuasiIsoIndependentCoefficients R P hP
      (principalAugmentation R t n.unop) (principalAugmentation_quasiIso R t ht n.unop)
  change QuasiIso (roosF.map (koszulTowerComplexMap R (koszulTensorTowerComparison R P t)))
  exact CategoryTheory.roos_map_quasiIso _

set_option maxHeartbeats 1600000 in
-- Representative conversion requires the larger budget used for the parent statement.
omit [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{r}
    (SheafOfModules.derivedChangeRingIndependentCoefficients J R))] in
private theorem quotient_unit_square
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (P : CochainComplex (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
    (M : PrincipalQuotientCompletion.Model R t) :
    rowUnit R t P ≫ quotientComparison R t P = M.augmentation P := by
  have haug := roosAugment_map (koszulTowerComplexMap R (koszulTensorTowerComparison R P t))
    (koszulRepresentativeAugmentation R P t)
    (fun n ↦ (koszulRepresentativeAugmentation_naturality R P t n).symm)
    (PrincipalQuotientCompletion.quotientMap R t P)
    (PrincipalQuotientCompletion.quotient_transition R t P)
    (fun n ↦ koszulRepresentativeAugmentation_quotient R P t n)
  have he : roosAugment (PrincipalQuotientCompletion.quotientMap R t P)
      (PrincipalQuotientCompletion.quotient_transition R t P) = M.augmentation P := by
    ext k : 1
    obtain ⟨p, hp⟩ := (Equiv.addRight (1 : ℤ)).surjective k
    change p + 1 = k at hp
    subst k
    apply (cancel_mono (roosχ ((PrincipalQuotientCompletion.quotientTower R t).obj P)
      p).hom).mp
    rw [roosAugment_χ, M.coordinates]
    rfl
  exact haug.trans he

set_option maxHeartbeats 1600000 in
-- Converting tensor symmetry and transposed Roos representatives needs extra heartbeats.
private theorem koszulCompletion_quasiIso (t : Section)
    {P P' : CochainComplex A ℤ} (f : P ⟶ P') (hf : QuasiIso f) :
    QuasiIso ((koszulCompletion R t).map f) := by
  let := SheafOfModules.tensorPreadditive R
  let := SheafOfModules.symmetricCategory R
  have hlevel (n : ℕ) : QuasiIso
      (((curriedTensor A).map₂CochainComplex.obj (principalKoszul R t n)).map f) := by
    have h := kFlatTensorPreservesQuasiIsoIndependentCoefficients R
      (principalKoszul R t n) (principalKoszul_kflat R t n) f hf
    change QuasiIso (HomologicalComplex.mapBifunctorMap f
      (𝟙 (principalKoszul R t n)) (curriedTensor A) (.up ℤ)) at h
    let e := SheafOfModules.TotalTensorSigns.Generic.swap A
    have he := SheafOfModules.TotalTensorSigns.Generic.swap_naturality A
      (principalKoszul R t n) (principalKoszul R t n) P P' (𝟙 _) f
    have hq : QuasiIso
        ((e P (principalKoszul R t n)).hom ≫
          (((curriedTensor A).map₂CochainComplex.obj
            (principalKoszul R t n)).map f)) := by
      change QuasiIso
        ((SheafOfModules.TotalTensorSigns.Generic.swap A P
          (principalKoszul R t n)).hom ≫
          HomologicalComplex.mapBifunctorMap (𝟙 (principalKoszul R t n)) f
            (curriedTensor A) (.up ℤ))
      rw [← he]
      have := h
      infer_instance
    exact quasiIso_of_comp_left (e P (principalKoszul R t n)).hom _
  have htow : QuasiIso
      ((PrincipalQuotientCompletion.transpose R).map ((koszulRows R t).map f)) := by
    apply (HomologicalComplex.quasiIso_iff_evaluation _).mpr
    intro n
    exact hlevel n.unop
  exact CategoryTheory.roos_map_quasiIso _

set_option maxHeartbeats 1600000 in
-- Unfolding the chosen quotient and Koszul tensor functors needs extra heartbeats.
omit [HasDerivedCategory.{w} A] [HasExactLimitsOfShape (Discrete ℕ) A] in
private theorem quotientComparison_natural (t : Section)
    {P P' : CochainComplex A ℤ} (f : P ⟶ P') :
    (koszulCompletion R t).map f ≫ quotientComparison R t P' =
      quotientComparison R t P ≫ (PrincipalQuotientCompletion.quotientRoos R t).map f := by
  let B := (curriedTensor A).map₂CochainComplex
  change (limitComplex R).map ((koszulRows R t).map f) ≫
      (limitComplex R).map (koszulTensorTowerComparison R P' t) =
    (limitComplex R).map (koszulTensorTowerComparison R P t) ≫
      (limitComplex R).map
        (Functor.whiskerLeft (principalReductionTower R t) (B.flip.map f))
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg (limitComplex R).map
  apply NatTrans.ext
  funext n
  exact (B.map ((principalTowerComparison R t).app n)).naturality f

set_option maxHeartbeats 1600000 in
-- The localization and K-flat representative conversions need extra heartbeats.
private theorem completion_comparison (t : Section)
    (ht : Mono (globalSectionMultiplication R t))
    (M : PrincipalQuotientCompletion.Model R t) :
    ∃ e : M.completion ≅
        Localization.lift (W := HomologicalComplex.quasiIso A (.up ℤ))
          (koszulCompletion R t ⋙ DerivedCategory.Q)
          (fun _ _ f hf ↦ (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
            (koszulCompletion_quasiIso R t f hf)) DerivedCategory.Q,
      ∀ P, e.hom.app (DerivedCategory.Q.obj P) ≫
          (Localization.fac (W := HomologicalComplex.quasiIso A (.up ℤ))
            (koszulCompletion R t ⋙ DerivedCategory.Q)
            (fun _ _ f hf ↦ (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
              (koszulCompletion_quasiIso R t f hf)) DerivedCategory.Q).hom.app P ≫
          DerivedCategory.Q.map (quotientComparison R t P) = M.counit.app P := by
  classical
  let Q := DerivedCategory.Q (C := A)
  let W := HomologicalComplex.quasiIso A (.up ℤ)
  let F := koszulCompletion R t ⋙ Q
  let hinv : W.IsInvertedBy F := fun _ _ f hf ↦
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
      (koszulCompletion_quasiIso R t f hf)
  let L := Localization.lift F hinv Q
  let κ : Q ⋙ L ≅ F := Localization.fac F hinv Q
  let β : F ⟶ PrincipalQuotientCompletion.quotientRoos R t ⋙ Q :=
    { app := fun P ↦ Q.map (quotientComparison R t P)
      naturality := fun P P' f ↦ by
        change Q.map ((koszulCompletion R t).map f) ≫
            Q.map (quotientComparison R t P') =
          Q.map (quotientComparison R t P) ≫
            Q.map ((PrincipalQuotientCompletion.quotientRoos R t).map f)
        simpa only [← Functor.map_comp] using
          congrArg Q.map (quotientComparison_natural R t f) }
  let := M.universal
  let c : L ⟶ M.completion := M.completion.leftDerivedLift M.counit W L (κ.hom ≫ β)
  have hc (P : CochainComplex A ℤ) :
      c.app (Q.obj P) ≫ M.counit.app P = κ.hom.app P ≫ β.app P :=
    M.completion.leftDerived_fac_app M.counit W L (κ.hom ≫ β) P
  have hcflat (P : CochainComplex A ℤ)
      (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
      IsIso (c.app (Q.obj P)) := by
    have := M.computes P hP
    have hq := quotientComparison_quasiIso R t ht P hP
    have : IsIso (β.app P) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hq
    have : IsIso (c.app (Q.obj P) ≫ M.counit.app P) := by
      rw [hc P]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (M.counit.app P)
  have hcobj (X : DerivedCategory A) : IsIso (c.app X) := by
    let P := Q.objPreimage X
    let i := Q.objObjPreimageIso X
    obtain ⟨K, a, hK, _, ha, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) P
    have : IsIso (Q.map a) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr ha
    have := hcflat K hK
    have hn := c.naturality (Q.map a ≫ i.hom)
    have : IsIso (c.app (Q.obj K) ≫ M.completion.map (Q.map a ≫ i.hom)) :=
      inferInstance
    rw [← hn] at this
    exact IsIso.of_isIso_comp_left (L.map (Q.map a ≫ i.hom)) _
  have : IsIso c := (NatTrans.isIso_iff_isIso_app c).mpr hcobj
  refine ⟨(asIso c).symm, ?_⟩
  intro P
  change (inv c).app (Q.obj P) ≫ κ.hom.app P ≫ β.app P = M.counit.app P
  rw [NatIso.isIso_inv_app, ← hc P]
  simp

omit [EssentiallySmall.{r} C] [HasDerivedCategory.{w} A]
  [HasExactLimitsOfShape (Discrete ℕ) A] in
private theorem coordinate_false_chi (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    coordinate R X (p + 1) false = (roosχ X p).hom ≫ biprod.snd :=
  roosProj_f X p

omit [EssentiallySmall.{r} C] [HasDerivedCategory.{w} A]
  [HasExactLimitsOfShape (Discrete ℕ) A] in
private theorem shifted_coordinate_chi (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (CochainComplex.mappingCocone.snd (roosU X)).v (p + 1) p (by omega) =
      (roosχ X p).hom ≫ biprod.fst :=
  RoosConeCalculus.ucoord_χ X p

omit [EssentiallySmall.{r} C] [HasDerivedCategory.{w} A]
  [HasExactLimitsOfShape (Discrete ℕ) A] in
private theorem coordinate_true_reindex
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    coordinate R X (p + 1) true ≫
        ((roosP X).XIsoOfEq (show degree (p + 1) true = p by simp [degree])).hom =
      (roosχ X p).hom ≫ biprod.fst := by
  calc
    _ = (CochainComplex.mappingCocone.snd (roosU X)).v (p + 1) p (by omega) := by
      exact CochainComplex.HomComplex.Cochain.v_comp_XIsoOfEq_hom
        (CochainComplex.mappingCocone.snd (roosU X)) (p + 1) _ p _ _
    _ = _ := shifted_coordinate_chi R X p

omit [EssentiallySmall.{r} C] [HasDerivedCategory.{w} A]
  [HasExactLimitsOfShape (Discrete ℕ) A] in
-- Stated by hand: generating it with `@[reassoc]` took about 180 s.
private theorem coordinate_true_reindex_assoc
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) {Z : A} (h : (roosP X).X p ⟶ Z) :
    coordinate R X (p + 1) true ≫
        ((roosP X).XIsoOfEq (show degree (p + 1) true = p by simp [degree])).hom ≫ h =
      (roosχ X p).hom ≫ biprod.fst ≫ h := by
  rw [← Category.assoc, coordinate_true_reindex, Category.assoc]

omit [HasDerivedCategory.{w} A] [HasExactLimitsOfShape (Discrete ℕ) A]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem tensor_ι_reindex
    (K P : CochainComplex A ℤ) (i a a' z z' : ℤ) (h : i + a = z)
    (ha : a = a') (hz : z = z') :
    SheafOfModules.TotalTensorSigns.ι R K P i a z h ≫
        ((((SheafOfModules.TotalTensorSigns.total R).obj K).obj P).XIsoOfEq hz).hom =
      ((SheafOfModules.TotalTensorSigns.tensor R).obj (K.X i)).map
          (P.XIsoOfEq ha).hom ≫
        SheafOfModules.TotalTensorSigns.ι R K P i a' z' (by rw [← ha, ← hz]; exact h) := by
  subst a'
  subst z'
  simp only [HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_hom,
    Functor.map_id, Category.comp_id, Category.id_comp]

set_option maxHeartbeats 3200000 in
-- Converting the finite-comparison and strict-tower representatives needs extra heartbeats.
omit [HasDerivedCategory.{w} A] [HasExactLimitsOfShape (Discrete ℕ) A] in
private theorem distribution_exists (t : Section)
    (ht : Mono (globalSectionMultiplication R t))
    (U : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ∃ D : (koszulRows R t).obj (roosF.obj U) ≅
        (koszulDouble R t U).flip ⋙ limitComplex R,
      distributionCoordinates R t U D := by
  classical
  let : PreservesFilteredColimitsOfSize.{r, r} (forget CommRingCat.{r}) :=
    preservesFilteredColimitsOfSize_shrink _
  let : HasSheafify J CommRingCat.{r} :=
    hasSheafifyEssentiallySmallSite J CommRingCat.{r}
  let := HasDerivedCategory.standard A
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ A)
  let (m : ℕ) := HasDerivedCategory.standard
    (SheafOfModules.RegularQuotientCone.Modules (PerfectReductionRoos.powerRing R t m))
  let (m : ℕ) := HasDerivedCategory.standard
    (ℕᵒᵖ ⥤ SheafOfModules.RegularQuotientCone.Modules
      (PerfectReductionRoos.powerRing R t m))
  let d := fun m ↦ Classical.choice
    (SheafOfModules.nonempty_derivedChangeOfRingsCochainModel
      (PerfectReductionRoos.powerProjection R t m))
  obtain ⟨c⟩ := PerfectReductionRoos.nonempty_coefficientUnits R t d
  obtain ⟨k⟩ := PerfectReductionRoos.nonempty_koszulDeltaData R t ht d c
  obtain ⟨kT⟩ := PerfectReductionRoos.nonempty_koszulTransitionData R t ht d c k.δ
    k.δ_shifted k.δ_unshifted
  let D : (koszulRows R t).obj (roosF.obj U) ≅
      (koszulDouble R t U).flip ⋙ limitComplex R :=
    NatIso.ofComponents (fun j ↦ k.δ j.unop U) (by
      intro j l f
      obtain ⟨j⟩ := j
      obtain ⟨l⟩ := l
      have h : l ≤ j := leOfHom f.unop
      exact kT.koszul_changes l j h U)
  refine ⟨D, ?_⟩
  intro j n i a z h q
  obtain ⟨a, rfl⟩ : ∃ b : ℤ, a = b + 1 := ⟨a - 1, by omega⟩
  obtain ⟨z, rfl⟩ : ∃ b : ℤ, z = b + 1 := ⟨z - 1, by omega⟩
  cases q with
  | false =>
    change SheafOfModules.TotalTensorSigns.ι R (principalKoszul R t j) (roosF.obj U)
        i (a + 1) (z + 1) h ≫ (k.δ j U).hom.f (z + 1) ≫
        coordinate R (PerfectReductionRoos.tensorTower R (principalKoszul R t j) U)
          (z + 1) false ≫
        (Pi.π (fun n ↦ (PerfectReductionRoos.tensorTower R
          (principalKoszul R t j) U).asFunctor.obj (op n)) n).f (z + 1) =
      (1 : ℤ) • (((SheafOfModules.TotalTensorSigns.tensor R).obj
        ((principalKoszul R t j).X i)).map
          (coordinate R U (a + 1) false ≫
            (Pi.π (fun n ↦ U.asFunctor.obj (op n)) n).f (a + 1)) ≫
          SheafOfModules.TotalTensorSigns.ι R (principalKoszul R t j)
            (U.asFunctor.obj (op n)) i (a + 1) (z + 1) h)
    rw [coordinate_false_chi, coordinate_false_chi]
    simpa only [one_smul, Category.assoc] using k.δ_unshifted j U a i z h n
  | true =>
    change SheafOfModules.TotalTensorSigns.ι R (principalKoszul R t j) (roosF.obj U)
        i (a + 1) (z + 1) h ≫ (k.δ j U).hom.f (z + 1) ≫
        coordinate R (PerfectReductionRoos.tensorTower R (principalKoszul R t j) U)
          (z + 1) true ≫
        (Pi.π (fun n ↦ (PerfectReductionRoos.tensorTower R
          (principalKoszul R t j) U).asFunctor.obj (op n)) n).f (degree (z + 1) true) =
      (i.negOnePow : ℤ) • (((SheafOfModules.TotalTensorSigns.tensor R).obj
        ((principalKoszul R t j).X i)).map
          (coordinate R U (a + 1) true ≫
            (Pi.π (fun n ↦ U.asFunctor.obj (op n)) n).f (degree (a + 1) true)) ≫
          SheafOfModules.TotalTensorSigns.ι R (principalKoszul R t j)
            (U.asFunctor.obj (op n)) i (degree (a + 1) true) (degree (z + 1) true)
              (by dsimp [degree]; omega))
    have ha : degree (a + 1) true = a := by simp [degree]
    have hz : degree (z + 1) true = z := by simp [degree]
    apply (cancel_mono (((PerfectReductionRoos.tensorTower R
      (principalKoszul R t j) U).asFunctor.obj (op n)).XIsoOfEq hz).hom).mp
    simp only [Preadditive.zsmul_comp, Category.assoc]
    rw [HomologicalComplex.XIsoOfEq_hom_naturality, coordinate_true_reindex_assoc]
    erw [tensor_ι_reindex R (principalKoszul R t j) (U.asFunctor.obj (op n))
      i _ a _ z _ ha hz]
    rw [← Functor.map_comp_assoc]
    simp only [Category.assoc]
    rw [HomologicalComplex.XIsoOfEq_hom_naturality, coordinate_true_reindex_assoc]
    simpa only [Units.smul_def, Preadditive.zsmul_comp, Category.assoc] using
      k.δ_shifted j U a i z h n


set_option maxHeartbeats 1600000 in
-- Unfolding the specified total-tensor unit inclusion needs extra heartbeats.
omit [HasDerivedCategory.{w} A] [HasExactLimitsOfShape (Discrete ℕ) A] in
private theorem koszulInclusion_f (t : Section) (P : CochainComplex A ℤ) (j : ℕ)
    (a : ℤ) :
    (koszulRepresentativeAugmentation R P t j).f a =
      (λ_ (P.X a)).inv ≫ PerfectReductionRoos.koszulZeroInclusion R t j ▷ P.X a ≫
        CochainComplex.ιMapBifunctor (principalKoszul R t j) P
          (curriedTensor A) 0 a a (zero_add a) := by
  change (λ_ (P.X a)).inv ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (SheafOfModules.unit
          (SheafOfModules.derivedChangeRingIndependentCoefficients J R))).inv ▷ P.X a ≫
      CochainComplex.ιMapBifunctor _ P (curriedTensor A) 0 a a (zero_add a) ≫
      (HomologicalComplex.mapBifunctorMap
        (CochainComplex.mappingCone.inr (principalKoszulScalarComplex R t j))
        (𝟙 P) (curriedTensor A) (.up ℤ)).f a = _
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, Functor.map_id, Category.id_comp]
  simp only [PerfectReductionRoos.koszulZeroInclusion, comp_whiskerRight,
    Category.assoc]
  rfl

set_option maxHeartbeats 1600000 in
-- The coordinate argument unfolds the chosen tensor and Roos representatives.
omit [HasDerivedCategory.{w} A] [HasExactLimitsOfShape (Discrete ℕ) A] in
private theorem distribution_inclusion (t : Section)
    (U : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (D : (koszulRows R t).obj (roosF.obj U) ≅
      (koszulDouble R t U).flip ⋙ limitComplex R)
    (hD : distributionCoordinates R t U D)
    (θ : ∀ j, U.asFunctor ⟶ (koszulDouble R t U).flip.obj (op j))
    (hθ : ∀ j n, (θ j).app (op n) =
      koszulRepresentativeAugmentation R (U.asFunctor.obj (op n)) t j) (j : ℕ) :
    koszulRepresentativeAugmentation R (roosF.obj U) t j ≫ D.hom.app (op j) =
      roosF.map (koszulTowerComplexMap R (θ j)) := by
  ext a : 1
  apply coordinate_ext R _ a
  intro q
  apply product_degree_ext R _ (degree a q)
  intro n
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [koszulInclusion_f]
  dsimp only [PrincipalQuotientCompletion.transpose]
  erw [show (roosF.map (koszulTowerComplexMap R (θ j))).f a ≫
      coordinate R (koszulTowerComplex R ((koszulDouble R t U).flip.obj (op j))) a q ≫
        (Pi.π (fun n ↦ ((koszulDouble R t U).obj (op n)).obj (op j)) n).f
          (degree a q) =
      coordinate R U a q ≫
        (Pi.π (fun n ↦ U.asFunctor.obj (op n)) n).f (degree a q) ≫
        ((θ j).app (op n)).f (degree a q) from
      limit_map_coordinate R (θ j) a q n]
  rw [hθ, koszulInclusion_f]
  simp only [Category.assoc]
  have he := hD j n 0 a a (zero_add a) q
  simp only [Int.negOnePow_zero, Units.val_one, ite_self, one_smul] at he
  erw [he]
  change (λ_ _).inv ≫ _ ▷ _ ≫ _ ◁ _ ≫ _ = _
  rw [← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc]
  simp only [Category.assoc]

set_option maxHeartbeats 1600000 in
-- Converting the transposed Roos map to its product coordinates needs extra heartbeats.
omit [HasDerivedCategory.{w} A] [HasExactLimitsOfShape (Discrete ℕ) A] in
private theorem distribution_unit_square (t : Section)
    (U : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (D : (koszulRows R t).obj (roosF.obj U) ≅
      (koszulDouble R t U).flip ⋙ limitComplex R)
    (hD : distributionCoordinates R t U D)
    (θ : ∀ j, U.asFunctor ⟶ (koszulDouble R t U).flip.obj (op j))
    (etaL : roosF.obj U ⟶ doubleLimit R (koszulDouble R t U).flip)
    (hθ : ∀ j n, (θ j).app (op n) =
      koszulRepresentativeAugmentation R (U.asFunctor.obj (op n)) t j)
    (hη : ∀ k, etaL.f (k + 1) ≫
      (roosχ (koszulTowerComplex R
        ((koszulDouble R t U).flip ⋙ limitComplex R)) k).hom =
      biprod.lift 0 ((Pi.lift (fun j ↦
        roosF.map (koszulTowerComplexMap R (θ j)))).f (k + 1))) :
    rowUnit R t (roosF.obj U) ≫ ((limitComplex R).mapIso D).hom = etaL := by
  have hp : Pi.lift (koszulRepresentativeAugmentation R (roosF.obj U) t) ≫
      roosPmap (koszulTowerComplexMap R D.hom) =
        Pi.lift (fun j ↦ roosF.map (koszulTowerComplexMap R (θ j))) := by
    apply Pi.hom_ext
    intro j
    simp only [Category.assoc, roosPmap, Pi.map_π]
    erw [Pi.lift_π_assoc, Pi.lift_π]
    exact distribution_inclusion R t U D hD θ hθ j
  ext k : 1
  obtain ⟨a, rfl⟩ : ∃ a : ℤ, k = a + 1 := ⟨k - 1, by omega⟩
  apply (cancel_mono (roosχ (koszulTowerComplex R
    ((koszulDouble R t U).flip ⋙ limitComplex R)) a).hom).mp
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [hη]
  change (rowUnit R t (roosF.obj U)).f (a + 1) ≫
    (roosF.map (koszulTowerComplexMap R D.hom)).f (a + 1) ≫ _ = _
  rw [roosF_map_χ, ← Category.assoc]
  dsimp only [rowUnit]
  erw [roosAugment_χ]
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst]
    erw [biprod.lift_fst_assoc, biprod.lift_fst]
    simp only [zero_comp]
  · simp only [Category.assoc, biprod.map_snd]
    erw [biprod.lift_snd_assoc, biprod.lift_snd]
    have he := congrArg (fun z ↦ z.f (a + 1)) hp
    simp only [HomologicalComplex.comp_f] at he
    exact he

set_option maxHeartbeats 8000000 in
-- Localizing the fixed tensor and Roos representative signatures needs extra heartbeats.
/-- Finite Koszul distribution identifies universal quotient completion with the
iterated raw Koszul Roos complex, preserving its prescribed unit on every resolution.
Source: Bhatt--Scholze, Lemmas 3.4.9 and 3.5.5; Stacks Tags 06YT and 0941
(blueprint: lem-sp-koszul-quotient-completion-comparison).

Proof: Distribute each two-term finite free Koszul complex through the products
and the mapping cocone. Moving its internal degree i past the shifted Roos
coordinate contributes (-1)^i. The tensor-inclusion equations specify both
coordinates and imply naturality for every Koszul transition, giving D.
The finite free Koszul tensor functors preserve quasi-isomorphisms. Exact
countable products and the cone triangle imply that their Roos completion does
also. On a K-flat P, regularity of t makes the actual Koszul-to-quotient maps
quasi-isomorphisms; exact products and the same cone argument make
Q(quotientComparison P) invertible, defining b with its prescribed hom.
The universal left derived property of Model identifies its completion with
the localization of Koszul completion. On a resolution a:P→Roos(U), its
comparison is counit_P ≫ b.inv ≫ Q(KC(a)) ≫ Q(lim(D)); naturality of the
counit and uniqueness of derived-functor comparisons make this independent of a.
It is invertible, defining e and the displayed equation on every such resolution.
The Koszul inclusion followed by the quotient augmentation is exactly the
quotient unit. Distribution sends its two coordinates to the strict row
inclusions and zero. The hypotheses on θ and etaL therefore identify the
localized augmentation with unit ≫ e, proving the required unit equation.
This argument concerns arbitrary U and never uses torsion or its row retractions. -/
theorem koszul_quotient_completion_comparison
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (ht : Mono (globalSectionMultiplication R t))
    (U : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{r}
          (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
    (θ : ∀ j : ℕ, U.asFunctor ⟶ (koszulDouble R t U).flip.obj (op j))
    (etaL : roosF.obj U ⟶ doubleLimit R (koszulDouble R t U).flip)
    (hθ : ∀ (j n : ℕ), (θ j).app (op n) =
              koszulRepresentativeAugmentation R (U.asFunctor.obj (op n)) t j)
    (hη : ∀ k : ℤ, etaL.f (k + 1) ≫
              (roosχ (koszulTowerComplex R
                ((koszulDouble R t U).flip ⋙ limitComplex R)) k).hom =
              biprod.lift 0 ((Pi.lift (fun j : ℕ ↦
                roosF.map (koszulTowerComplexMap R (θ j)))).f (k + 1)))
    :
    ∃ (D : (koszulRows R t).obj (roosF.obj U) ≅
              (koszulDouble R t U).flip ⋙ limitComplex R),
      distributionCoordinates R t U D ∧
      ∀ M : PrincipalQuotientCompletion.Model R t,
        ∃ (e : M.completion.obj (DerivedCategory.Q.obj (roosF.obj U)) ≅
              DerivedCategory.Q.obj (doubleLimit R (koszulDouble R t U).flip)),
          M.unit.app (DerivedCategory.Q.obj (roosF.obj U)) ≫ e.hom =
            DerivedCategory.Q.map etaL ∧
            (∀ (P : CochainComplex (ringedSiteModules.{r}
                (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
              (a : P ⟶ roosF.obj U),
              CochainComplex.IsKFlatIndependentCoefficients (R := R) P → QuasiIso a →
              ∃ b : DerivedCategory.Q.obj ((koszulCompletion R t).obj P) ≅
                  DerivedCategory.Q.obj ((PrincipalQuotientCompletion.quotientRoos R t).obj P),
                b.hom = DerivedCategory.Q.map (quotientComparison R t P) ∧
                M.completion.map (DerivedCategory.Q.map a) ≫ e.hom =
                  M.counit.app P ≫ b.inv ≫
                    DerivedCategory.Q.map ((koszulCompletion R t).map a) ≫
                    DerivedCategory.Q.map ((limitComplex R).mapIso D).hom) := by
  classical
  obtain ⟨D, hD⟩ := distribution_exists R t ht U
  refine ⟨D, hD, ?_⟩
  intro M
  let Q := DerivedCategory.Q (C := A)
  let X := roosF.obj U
  let F := koszulCompletion R t ⋙ Q
  let hinv : (HomologicalComplex.quasiIso A (.up ℤ)).IsInvertedBy F :=
    fun _ _ f hf ↦ (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr
      (koszulCompletion_quasiIso R t f hf)
  let L := Localization.lift F hinv Q
  let κ : Q ⋙ L ≅ F := Localization.fac F hinv Q
  obtain ⟨c, hc⟩ := completion_comparison R t ht M
  let τ : Q ⋙ M.completion ⟶ F := Functor.whiskerLeft Q c.hom ≫ κ.hom
  let η : Q ⟶ F := Functor.whiskerLeft Q M.unit ≫ τ
  let e := c.app (Q.obj X) ≪≫ κ.app X ≪≫ Q.mapIso ((limitComplex R).mapIso D)
  refine ⟨e, ?_, ?_⟩
  · have hunit (P : CochainComplex A ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
        η.app P = Q.map (rowUnit R t P) := by
      have hq := quotientComparison_quasiIso R t ht P hP
      have : IsIso (Q.map (quotientComparison R t P)) :=
        (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hq
      apply (cancel_mono (Q.map (quotientComparison R t P))).mp
      change (M.unit.app (Q.obj P) ≫ c.hom.app (Q.obj P) ≫ κ.hom.app P) ≫
        Q.map (quotientComparison R t P) = _
      simp only [Category.assoc]
      erw [hc P, M.unit_computes]
      rw [← Q.map_comp, quotient_unit_square]
    obtain ⟨P, a, hP, _, ha, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) X
    have : IsIso (Q.map a) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr ha
    have hu : η.app X = Q.map (rowUnit R t X) := by
      apply (cancel_epi (Q.map a)).mp
      calc
        Q.map a ≫ η.app X = η.app P ≫ F.map a := η.naturality a
        _ = Q.map (rowUnit R t P) ≫ F.map a := by rw [hunit P hP]
        _ = Q.map a ≫ Q.map (rowUnit R t X) := by
          change Q.map (rowUnit R t P) ≫ Q.map ((koszulCompletion R t).map a) = _
          erw [← Q.map_comp, ← Q.map_comp]
          exact congrArg Q.map (rowUnit_natural R t a).symm
    calc
      M.unit.app (Q.obj X) ≫ e.hom =
          η.app X ≫ Q.map ((limitComplex R).mapIso D).hom := by
        simp only [e, η, τ, NatTrans.comp_app, Functor.whiskerLeft_app,
          Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
      _ = Q.map (rowUnit R t X) ≫ Q.map ((limitComplex R).mapIso D).hom := by rw [hu]
      _ = Q.map etaL := by
        rw [← Q.map_comp, distribution_unit_square R t U D hD θ etaL hθ hη]
  · intro P a hP _ha
    have hq := quotientComparison_quasiIso R t ht P hP
    have : IsIso (Q.map (quotientComparison R t P)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hq
    let b := asIso (Q.map (quotientComparison R t P))
    refine ⟨b, rfl, ?_⟩
    have hcp : τ.app P = M.counit.app P ≫ b.inv := by
      apply (Iso.eq_comp_inv b).mpr
      dsimp only [τ, NatTrans.comp_app, Functor.whiskerLeft_app]
      rw [Category.assoc]
      exact hc P
    calc
      M.completion.map (Q.map a) ≫ e.hom =
          (M.completion.map (Q.map a) ≫ τ.app X) ≫
            Q.map ((limitComplex R).mapIso D).hom := by
        simp only [e, τ, NatTrans.comp_app, Functor.whiskerLeft_app,
          Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
      _ = (τ.app P ≫ F.map a) ≫ Q.map ((limitComplex R).mapIso D).hom := by
        rw [show M.completion.map (Q.map a) ≫ τ.app X = τ.app P ≫ F.map a from
          τ.naturality a]
      _ = M.counit.app P ≫ b.inv ≫ Q.map ((koszulCompletion R t).map a) ≫
          Q.map ((limitComplex R).mapIso D).hom := by
        rw [hcp]
        simp only [F, Functor.comp_map, Category.assoc]

end CategoryTheory.RingedPowerTorsion
