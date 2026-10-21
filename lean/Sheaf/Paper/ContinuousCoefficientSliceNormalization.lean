/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q63
-/
module

public import Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientPullback
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCompletion
public import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
public import Sheaf.AlgebraicGeometry.LisseLatticeCoefficientsSized
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
import Sheaf.AlgebraicGeometry.ContinuousCoefficientLocalization
import Sheaf.AlgebraicGeometry.ContinuousCoefficientPullbackIso
import Sheaf.AlgebraicGeometry.ProEtaleScalarExtensionSliceComparison
import Sheaf.AlgebraicGeometry.ProEtaleLocalizedRingMateGraphEvaluation
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Normalized continuous coefficient restriction to a pro-etale slice

Source: Bhatt--Scholze, Definition 6.8.1, Lemma 6.8.2, paragraph before Definition
6.8.6 and Remark 6.8.15; Stacks, Tags 00VC, 00XZ, 03EL, 06YY and 0G7E
(blueprint: lem-per-continuous-coefficient-slice-normalization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ContinuousSlice

/-- Literal module restriction along composition with a site object. The scalar ring
is the literal restriction of R; both sections and morphisms are precomposed.
Source: Stacks 00XZ and 03EL
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
def modules {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    pbcModules X R ⥤ pbcModules U.left
      ((AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        U.hom U.prop).obj R) :=
  letI : (MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).IsContinuous
      (ProEt.topology U.left) (ProEt.topology X) := ProEt.isContinuous_overMap U.prop
  SheafOfModules.pushforward (F := MorphismProperty.Over.map (f := U.hom) ⊤ U.prop)
    (J := ProEt.topology U.left) (K := ProEt.topology X) (𝟙 _)

private theorem exact_moduleRestriction
    {C : Type*} [Category C] {D : Type*} [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K] [F.IsCocontinuous J K] [F.IsLeftAdjoint]
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) [IsIso φ] :
    (SheafOfModules.pushforward.{u} φ).Additive ∧
      PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ) ∧
      PreservesFiniteColimits (SheafOfModules.pushforward.{u} φ) := by
  let T := SheafOfModules.forget.{u} S ⋙ PresheafOfModules.toPresheaf S.obj
  have : PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ ⋙ T) := by
    change PreservesFiniteLimits
      ((SheafOfModules.forget.{u} R ⋙ PresheafOfModules.toPresheaf R.obj) ⋙
        (Functor.whiskeringLeft _ _ _).obj F.op)
    infer_instance
  have : PreservesFiniteLimits (SheafOfModules.pushforward.{u} φ) :=
    preservesFiniteLimits_of_reflects_of_preserves _ T
  have : (SheafOfModules.pushforward.{u} φ).IsLeftAdjoint :=
    SheafOfModules.isLeftAdjoint_pushforward_of_isIso φ
  refine ⟨?_, inferInstance, inferInstance⟩
  constructor
  intro M N f g
  apply SheafOfModules.hom_ext
  ext V m
  rfl

/-- Exactness of literal restriction, including nonnoetherian U.
Source: Stacks 00XZ, 03EL and 03CZ
(blueprint: lem-per-continuous-coefficient-slice-normalization).
Proof: the forgetful functor to module presheaves reflects finite limits, and
presheaf restriction preserves them. Composition with U is cocontinuous and left
adjoint to base change, giving the left-adjoint property of module restriction
and preservation of colimits. Additivity is checked on sections. No coefficient
flatness, boundedness or noetherian hypothesis on U is used. -/
theorem modules_exact {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    (modules U R).Additive ∧ PreservesFiniteLimits (modules U R) ∧
      PreservesFiniteColimits (modules U R) := by
  let G := MorphismProperty.Over.map (f := U.hom) ⊤ U.prop
  let : G.IsContinuous (ProEt.topology U.left) (ProEt.topology X) :=
    ProEt.isContinuous_overMap U.prop
  let : G.IsCocontinuous (ProEt.topology U.left) (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap U.prop
  let : G.IsLeftAdjoint :=
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ U.hom U.prop trivial).isLeftAdjoint
  exact exact_moduleRestriction (F := G) (𝟙 _)

/-- The additive structure supplied by exact restriction. Source: Stacks 03EL
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
instance modules_additive {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) : (modules U R).Additive :=
  (modules_exact U R).1

/-- Finite limits preserved by restriction. Source: Stacks 03EL
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
instance modules_limits {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    PreservesFiniteLimits (modules U R) := (modules_exact U R).2.1

/-- Finite colimits preserved by restriction. Source: Stacks 03EL
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
instance modules_colimits {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    PreservesFiniteColimits (modules U R) := (modules_exact U R).2.2

/-- Unbounded derived restriction is exact termwise restriction. Source: Stacks 03EL
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
def derived {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :=
  (modules U R).mapDerivedCategory

/-- The coefficient identification is the identity on continuous functions on V.
Source: Bhatt--Scholze 6.8.1; Stacks 00XZ
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
def ring {X : Scheme.{u}} (U : X.ProEt) (T : Type (u + 1))
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
      U.hom U.prop).obj (continuousCoefficientSheaf X T) ≅
      continuousCoefficientSheaf U.left T :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))

/-- Actual inverse image is normalized by its Kan coprojections and sheafification
unit, and its coefficient structural map becomes the identity on the same V.
Source: Bhatt--Scholze 6.8.1; Stacks 00VC and 00XZ
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
structure Coefficients {X : Scheme.{u}} (U : X.ProEt) where
  sets : ProEtaleObjectRestrictionComparison U (Type (u + 1))
  groups : ProEtaleObjectRestrictionComparison U AddCommGrpCat.{u + 1}
  rings : ProEtaleObjectRestrictionComparison U RingCat.{u + 1}
  commRings : ProEtaleObjectRestrictionComparison U CommRingCat.{u + 1}
  initial : ∀ V : U.left.ProEt,
    Nonempty (IsInitial (proEtaleObjectInverseImageIndexPoint U V))
  continuous : ∀ (T : Type (u + 1)) [TopologicalSpace T] [CommRing T]
      [IsTopologicalRing T],
    IsIso (continuousCoefficientPullback T U.hom) ∧
      continuousCoefficientPullback T U.hom =
        commRings.sheafIso.hom.app (continuousCoefficientSheaf X T) ≫ (ring U T).hom
  constants : ∀ (T : Type (u + 1)) [TopologicalSpace T] [CommRing T]
      [IsTopologicalRing T] (V : U.left.ProEt) (a : T),
    (ring U T).hom.hom.app (op V)
      (ContinuousMap.const V.left a) = ContinuousMap.const V.left a
  coefficient_maps : ∀ (T S : Type (u + 1)) [TopologicalSpace T] [CommRing T]
      [IsTopologicalRing T] [TopologicalSpace S] [CommRing S] [IsTopologicalRing S]
      (h : T →+* S) (hc : Continuous h),
    (proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).map
        (continuousCoefficientMap h hc X) ≫ continuousCoefficientPullback S U.hom =
      continuousCoefficientPullback T U.hom ≫ continuousCoefficientMap h hc U.left
  finite : ∀ (A : CommRingCat.{u + 1}) [Finite A],
    IsIso (proEtaleConstantInverseImageMap U.hom CommRingCat.{u + 1} A)

private theorem continuous_pullback_slice {X : Scheme.{u}} (U : X.ProEt)
    (b : ProEtaleObjectRestrictionComparison U CommRingCat.{u + 1})
    (bA : ProEtaleObjectRestrictionComparison U AddCommGrpCat.{u + 1})
    (T : Type (u + 1)) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    continuousCoefficientPullback T U.hom =
      b.sheafIso.hom.app (continuousCoefficientSheaf X T) ≫ (ring U T).hom := by
  let R := continuousCoefficientSheaf X T
  let S := continuousCoefficientSheaf U.left T
  let beta := b.sheafIso.app R ≪≫ ring U T
  have h := (proEtaleLocalizedRingMateGraphEvaluation U b bA R S beta).1
  apply ((proEtaleSheafAdjunction U.hom CommRingCat.{u + 1}).homEquiv R S).injective
  erw [continuousCoefficientPullback, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  change C(V.unop.left, T) at s
  change _ = (ring U T).hom.hom.app _
    ((b.sheafIso.hom.app R).hom.app _
      (((proEtaleSheafAdjunction U.hom CommRingCat.{u + 1}).unit.app R).hom.app V s))
  erw [h]
  rfl

private theorem coefficients_exists {X : Scheme.{u}} (U : X.ProEt) :
    Nonempty (Coefficients U) := by
  obtain ⟨h0, ⟨s⟩, ⟨a⟩, ⟨r⟩, c, e, he, hc, hM⟩ :=
    proEtaleObjectInverseImageRestriction X U (ULift.{u} ℤ)
  refine ⟨⟨s, a, r, c, h0, ?_, ?_, ?_, ?_⟩⟩
  · intro T _ _ _
    have h := continuous_pullback_slice U c a T
    refine ⟨?_, h⟩
    rw [h]
    infer_instance
  · intro T _ _ _ V x
    rfl
  · intro T S _ _ _ _ _ _ f hf
    exact continuousCoefficientPullback_naturality f hf U.hom
  · intro A _
    let Q := (Functor.const ℕᵒᵖ).obj A
    let : ∀ n : ℕᵒᵖ, Finite (Q.obj n) := fun _ ↦ inferInstanceAs (Finite A)
    exact (proEtale_profinite_coefficient_inverse_image Q).1 U.left X U.hom (op 0)

/-- The residue projections to the actual finite constant sheaves, using the canonical
constant-function comparison, not an arbitrary identification of the quotient.
Source: Bhatt--Scholze 6.8.1--6.8.2
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
def residue (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) (n : ℕ) :
    integralCoefficientSheaf l X E ⟶ (finiteCoefficientTower l X E).obj (op n) :=
  continuousCoefficientReduction l E X n ≫ (discreteContinuousCoefficientIso X).inv.app
    (finiteCoefficientRing l E n)

/-- Coefficient and quotient normalization, retaining every positive level n+1.
The finite structural maps are the constant-section maps of the actual inverse image.
Source: Bhatt--Scholze 6.8.1--6.8.2
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
structure Adic (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {X Y : Scheme.{u}} (g : Y ⟶ X) where
  integral : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
    (integralCoefficientSheaf l X E) ≅ integralCoefficientSheaf l Y E
  rational : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
    (rationalCoefficientSheaf l X E) ≅ rationalCoefficientSheaf l Y E
  integral_normalized : integralCoefficientRestrictionNormalized l E g integral.hom
  rational_normalized : rationalCoefficientRestrictionNormalized l E g rational.hom
  quotient : ∀ n : ℕ,
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      ((finiteCoefficientTower l X E).obj (op n)) ≅
        (finiteCoefficientTower l Y E).obj (op n)
  quotient_constants : ∀ n : ℕ, (quotient n).hom =
    proEtaleCoefficientInverseImageMap g (Padic.coefficientExtensionRing l E (n + 1))
  transitions : ∀ (m n : ℕ) (h : n ≤ m),
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
          (finiteCoefficientRingMap l E h)) ≫ (quotient n).hom =
      (quotient m).hom ≫ (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
        (finiteCoefficientRingMap l E h)
  projections : ∀ n : ℕ,
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map (residue l E X n) ≫
        (quotient n).hom = integral.hom ≫ residue l E Y n
  inclusion : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
      (integralRationalCoefficientMap l E X) ≫ rational.hom =
    integral.hom ≫ integralRationalCoefficientMap l E Y

private theorem constantComparison_pullback (T : Type (u + 1))
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    {Z X : Scheme.{u}} (h : Z ⟶ X) :
    (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
        (continuousCoefficientConstantComparison X T) ≫ continuousCoefficientPullback T h =
      proEtaleConstantInverseImageMap h CommRingCat.{u + 1} (CommRingCat.of T) ≫
        continuousCoefficientConstantComparison Z T := by
  let adj := proEtaleSheafAdjunction h CommRingCat.{u + 1}
  change _ ≫ (adj.homEquiv _ _).symm _ = (adj.homEquiv _ _).symm _ ≫ _
  rw [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm]
  congr 1
  apply ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of T)) _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
  unfold continuousCoefficientConstantComparison proEtaleConstantDirectImageMap
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext U
  have hz := Equiv.apply_symm_apply
    ((sheafificationAdjunction (ProEt.topology Z) CommRingCat.{u + 1}).homEquiv
      ((Functor.const Z.ProEtᵒᵖ).obj (CommRingCat.of T)) (continuousCoefficientSheaf Z T))
    (continuousCoefficientConstants Z T)
  exact (congrArg (fun f ↦ f.app ((proEtaleBaseChange h).op.obj U)) hz).symm

private theorem transportInverseIsoSquare
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B B' : C} {A' T T' : D} (q : B ≅ B') (q' : T ≅ T')
    (a : F.obj A ⟶ A') (t : F.obj B ⟶ T) (u : F.obj B' ⟶ T')
    (r : A ⟶ B') (s : A' ⟶ T')
    (hq : F.map q.hom ≫ u = t ≫ q'.hom)
    (hr : F.map r ≫ u = a ≫ s) :
    F.map (r ≫ q.inv) ≫ t = a ≫ s ≫ q'.inv := by
  apply (cancel_mono q'.hom).mp
  calc
    (F.map (r ≫ q.inv) ≫ t) ≫ q'.hom =
        F.map r ≫ F.map q.inv ≫ (t ≫ q'.hom) := by simp [Functor.map_comp]
    _ = F.map r ≫ F.map q.inv ≫ (F.map q.hom ≫ u) := by rw [hq]
    _ = F.map r ≫ u := by simp [← Functor.map_comp_assoc]
    _ = a ≫ s := hr
    _ = (a ≫ s ≫ q'.inv) ≫ q'.hom := by simp

private theorem residue_pullback (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {X Y : Scheme.{u}}
    (g : Y ⟶ X) (n : ℕ) :
    let := coefficientExtensionNormedField l E
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map (residue l E X n) ≫
        proEtaleCoefficientInverseImageMap g
          (Padic.coefficientExtensionRing l E (n + 1)) =
      continuousCoefficientPullback
          (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) g ≫
        residue l E Y n := by
  let := coefficientExtensionNormedField l E
  let A := finiteCoefficientRing l E n
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  apply transportInverseIsoSquare (proEtaleSheafInverseImage g CommRingCat.{u + 1})
    ((discreteContinuousCoefficientIso X).app A)
    ((discreteContinuousCoefficientIso Y).app A)
  · exact constantComparison_pullback A g
  · exact continuousCoefficientPullback_naturality _ _ g

private theorem adic_exists (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {X Y : Scheme.{u}}
    (g : Y ⟶ X)
    (h : let := coefficientExtensionNormedField l E
      IsIso (continuousCoefficientPullback
        (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) g) ∧
      IsIso (continuousCoefficientPullback (ULift.{u + 1, u} E) g)) :
    Nonempty (Adic l E g) := by
  classical
  let := coefficientExtensionNormedField l E
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)
  let K := ULift.{u + 1, u} E
  obtain ⟨hA, hK⟩ := h
  let := hA
  let := hK
  let Q := finiteCoefficientRingTower l E
  let : ∀ n : ℕᵒᵖ, Finite (Q.obj n) := fun n ↦ by
    let := Padic.finite_coefficientExtensionRing l E (n.unop + 1)
      (Nat.succ_le_succ (Nat.zero_le _))
    exact inferInstanceAs (Finite (ULift.{u + 1, u}
      (Padic.coefficientExtensionRing l E (n.unop + 1))))
  have hq (n : ℕ) : IsIso (proEtaleCoefficientInverseImageMap g
      (Padic.coefficientExtensionRing l E (n + 1))) :=
    (proEtale_profinite_coefficient_inverse_image Q).1 Y X g (op n)
  let := hq
  refine ⟨{
    integral := asIso (continuousCoefficientPullback A g)
    rational := asIso (continuousCoefficientPullback K g)
    integral_normalized := continuousCoefficientPullback_normalized A g
    rational_normalized := continuousCoefficientPullback_normalized K g
    quotient := fun n ↦ asIso (proEtaleCoefficientInverseImageMap g
      (Padic.coefficientExtensionRing l E (n + 1)))
    quotient_constants := fun _ ↦ rfl
    transitions := ?_
    projections := residue_pullback l E g
    inclusion := ?_ }⟩
  · intro m n hmn
    exact proEtaleConstantInverseImageMap_naturality g (finiteCoefficientRingMap l E hmn)
  · exact continuousCoefficientPullback_naturality
      (RingHom.ulift (Padic.coefficientExtensionIntegers l E).subtype)
      (continuous_uliftUp.comp (continuous_subtype_val.comp continuous_uliftDown)) g

/-- The completed and localized coefficient identifications with their canonical projections.
Source: Bhatt--Scholze 6.8.2
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
structure Completion (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) where
  integral : integralCoefficientSheaf l X E ≅ finiteCoefficientLimit l X E
  projections : ∀ n : ℕ,
    integral.hom ≫ limit.π (finiteCoefficientTower l X E) (op n) = residue l E X n
  rational : integralCoefficientLocalization l X E ≅ rationalCoefficientSheaf l X E
  fractions : integralCoefficientLocalizationNormalized l E X rational.hom

private theorem completion_exists (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    Nonempty (Completion l E X) := by
  classical
  let := coefficientExtensionNormedField l E
  let e := Functor.isoWhiskerLeft (finiteCoefficientRingTower l E)
    (discreteContinuousCoefficientIso X)
  let hc := Classical.choice (continuousCoefficientResidueCone_isLimit l E X)
  let i := hc.conePointsIsoOfNatIso (limit.isLimit (finiteCoefficientTower l X E)) e.symm
  obtain ⟨b, hb⟩ := continuousCoefficientLocalization l E X
  refine ⟨⟨i, ?_, b, hb⟩⟩
  intro n
  have h := hc.conePointsIsoOfNatIso_hom_comp
    (limit.isLimit (finiteCoefficientTower l X E)) e.symm (op n)
  exact h

/-- Finite-quotient normalization of the completed structural map.
Source: Bhatt--Scholze 6.8.2 and Remark 6.8.15
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
structure CompletedPull (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {X Y : Scheme.{u}} (g : Y ⟶ X)
    (a : Adic l E g) (bX : Completion l E X) (bY : Completion l E Y) where
  integral : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
    (finiteCoefficientLimit l X E) ≅ finiteCoefficientLimit l Y E
  normalization : integral.hom =
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map bX.integral.inv ≫
      a.integral.hom ≫ bY.integral.hom
  projections : ∀ n : ℕ,
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (limit.π (finiteCoefficientTower l X E) (op n)) ≫ (a.quotient n).hom =
      integral.hom ≫ limit.π (finiteCoefficientTower l Y E) (op n)

private theorem completedPull_exists (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {X Y : Scheme.{u}} (g : Y ⟶ X)
    (a : Adic l E g) (bX : Completion l E X) (bY : Completion l E Y) :
    Nonempty (CompletedPull l E g a bX bY) := by
  let F := proEtaleSheafInverseImage g CommRingCat.{u + 1}
  let i := F.mapIso bX.integral.symm ≪≫ a.integral ≪≫ bY.integral
  refine ⟨⟨i, rfl, ?_⟩⟩
  intro n
  have hX : bX.integral.inv ≫ residue l E X n =
      limit.π (finiteCoefficientTower l X E) (op n) := by
    rw [← bX.projections n, Iso.inv_hom_id_assoc]
  change F.map _ ≫ _ = (F.map bX.integral.inv ≫ a.integral.hom ≫
    bY.integral.hom) ≫ _
  rw [Category.assoc, Category.assoc, bY.projections n, ← a.projections n,
    ← F.map_comp_assoc, hX]

/-- Ring-isomorphism scalar extension has exact ordinary inverse image as its derived
functor, normalized by the scalar-extension counit on every complex.
Source: Stacks 03EL, 03CZ and 06YY
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
structure ExactPull {X Y : Scheme.{u}} (f : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) where
  scalar : pbcExtend c.hom ≅ pbcRestrict c.inv
  scalar_sections : ∀ (M : pbcModules Y
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))
      (V : Y.ProEtᵒᵖ) (s : S.obj.obj V) (m : M.val.obj V),
    (scalar.hom.app M).val.app V (pbcTensorSection c.hom M V s m) =
      (c.inv.hom.app V s) • m
  scalar_complex : (pbcExtend c.hom).mapHomologicalComplex (.up ℤ) ≅
    (pbcRestrict c.inv).mapHomologicalComplex (.up ℤ)
  scalar_complex_components : ∀ P (n : ℤ),
    (scalar_complex.hom.app P).f n = scalar.hom.app (P.X n)
  scalar_derived : pbcDerivedExtend c.hom ≅ (pbcRestrict c.inv).mapDerivedCategory
  scalar_normalization : ∀ P : CochainComplex
      (pbcModules Y ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)) ℤ,
    pbcComplexCounit c.hom P ≫ DerivedCategory.Q.map (scalar_complex.hom.app P) =
      scalar_derived.hom.app (DerivedCategory.Q.obj P) ≫
        (pbcRestrict c.inv).mapDerivedCategoryFactors.hom.app P
  [limits : PreservesFiniteLimits (pbcExtend c.hom)]
  ordinary : proEtaleModuleInverseImage f R ⋙ pbcExtend c.hom ≅
    proEtaleRingModulePullback f R S c
  derived : adicTowerPullback f R ⋙ pbcDerivedExtend c.hom ≅
    proEtaleRingDerivedPullback f R S c
  normalization : ∀ P : CochainComplex
      (pbcModules Y ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)) ℤ,
    IsIso (pbcComplexCounit c.hom P)

private theorem scalar_exists {Y : Scheme.{u}}
    {R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}} (c : R ≅ S) :
    ∃ e : pbcExtend c.hom ≅ pbcRestrict c.inv,
      ∀ (M : pbcModules Y R) (V : Y.ProEtᵒᵖ) (s : S.obj.obj V)
        (m : M.val.obj V),
        (e.hom.app M).val.app V (pbcTensorSection c.hom M V s m) =
          (c.inv.hom.app V s) • m := by
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0} _
  let : HasSheafify (ProEt.topology Y) AddCommGrpCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  let : (ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
      u + 1, u + 2, u + 1} _
  obtain ⟨theta, ht, _, hn⟩ :=
    SheafOfModules.exists_scalarExtensionRingIso.{u + 1, u, u + 1, 0} c
  let hobj := (pbcExtensionExistence c.hom).choose_spec.choose
  let e : pbcExtend c.hom ≅ pbcRestrict c.inv :=
    NatIso.ofComponents (fun M ↦ eqToIso (hobj M) ≪≫ theta M) (by
      intro M N f
      dsimp only [Iso.trans_hom, eqToIso.hom]
      erw [(pbcExtensionExistence c.hom).choose_spec.choose_spec.choose f]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      exact congrArg (fun k ↦ eqToHom (hobj M) ≫ k) (hn M N f))
  refine ⟨e, ?_⟩
  intro M V s m
  change ((eqToHom (hobj M) ≫ (theta M).hom).val.app V) _ = _
  have h := ht M V m s
  change (theta M).hom.val.app V
    ((eqToHom (hobj M)).val.app V
      (((eqToHom (hobj M).symm).val.app V) _)) = _
  have hcancel (x : (SheafOfModules.changeOfRings c.hom M).val.obj V) :
      (eqToHom (hobj M)).val.app V ((eqToHom (hobj M).symm).val.app V x) = x := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.val.app V) (eqToHom_trans (hobj M).symm (hobj M))) x
  rw [hcancel]
  exact h

private def restrictIdIso {Y : Scheme.{u}}
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    pbcRestrict (𝟙 R) ≅ 𝟭 (pbcModules Y R) :=
  NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk
        (fun V ↦ (ModuleCat.restrictScalarsId (R.obj.obj V)).app (M.val.obj V))
        (fun {_ _} _ ↦ by ext m; rfl))) (fun _ ↦ by ext V m; rfl)

private theorem ordinaryExtension {X Y : Scheme.{u}} (f : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    Nonempty (proEtaleModuleInverseImage f R ⋙ pbcExtend c.hom ≅
      proEtaleRingModulePullback f R S c) := by
  let I := proEtaleModuleInverseImage f R
  let hobj := (pbcExtensionExistence c.hom).choose_spec.choose
  refine ⟨NatIso.ofComponents (fun M ↦ eqToIso (hobj (I.obj M))) ?_⟩
  intro M N a
  change (pbcExtend c.hom).map (I.map a) ≫ eqToHom (hobj (I.obj N)) =
    eqToHom (hobj (I.obj M)) ≫ _
  erw [(pbcExtensionExistence c.hom).choose_spec.choose_spec.choose (I.map a)]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  rfl

private theorem exactExtensionDerived {Y : Scheme.{u}}
    {R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}} (φ : R ⟶ S)
    [PreservesFiniteLimits (pbcExtend φ)] [PreservesFiniteColimits (pbcExtend φ)] :
    ∃ d : pbcDerivedExtend φ ≅ (pbcExtend φ).mapDerivedCategory,
      ∀ P : CochainComplex (pbcModules Y R) ℤ,
        pbcComplexCounit φ P = d.hom.app (DerivedCategory.Q.obj P) ≫
          (pbcExtend φ).mapDerivedCategoryFactors.hom.app P := by
  let L := pbcExtend φ
  let D := pbcDerivedExtend φ
  let ε := pbcExtensionCounit φ
  have : D.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (pbcModules Y R) (.up ℤ)) :=
    pbcDerivedExtension_universal φ
  have : L.mapDerivedCategory.IsLeftDerivedFunctor L.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso (pbcModules Y R) (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ L.mapDerivedCategoryFactorsh
  let d := Functor.leftDerivedUnique L.mapDerivedCategory D ε
    L.mapDerivedCategoryFactorsh.hom
    (HomotopyCategory.quasiIso (pbcModules Y R) (.up ℤ))
  have hd : Functor.whiskerLeft DerivedCategory.Qh d.hom ≫
      L.mapDerivedCategoryFactorsh.hom = ε := by
    simp [d]
  refine ⟨d, ?_⟩
  intro P
  have h := congrArg (fun t ↦ t.app ((HomotopyCategory.quotient _ _).obj P)) hd
  change _ = d.hom.app _ ≫ _
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
  rw [Functor.mapDerivedCategoryFactorsh_hom_app] at h
  dsimp only [pbcComplexCounit, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv,
    Functor.mapHomotopyCategoryFactors, Functor.map_id,
    Category.id_comp, Category.comp_id] at h ⊢
  erw [D.map_id, DerivedCategory.Qh.map_id, Category.comp_id, Category.id_comp]
  erw [L.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id, Category.comp_id] at h
  erw [Category.id_comp] at h
  exact h.symm

private theorem exactPull_exists {X Y : Scheme.{u}} (f : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    Nonempty (ExactPull f R S c) := by
  obtain ⟨e, he⟩ := scalar_exists c
  let L := pbcExtend c.hom
  have : PreservesFiniteLimits L := preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteColimits L := preservesFiniteColimits_of_natIso e.symm
  obtain ⟨d, hd⟩ := exactExtensionDerived c.hom
  let I := proEtaleModuleInverseImage f R
  obtain ⟨o⟩ := ordinaryExtension f R S c
  let RI := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R
  obtain ⟨e0, _⟩ := scalar_exists (Iso.refl RI)
  obtain ⟨o0⟩ := ordinaryExtension f R RI (Iso.refl RI)
  let z := o0.symm ≪≫ Functor.isoWhiskerLeft I (e0 ≪≫ restrictIdIso RI) ≪≫
    Functor.rightUnitor I
  have : I.Additive := Functor.additive_of_iso z
  have : PreservesFiniteLimits I := preservesFiniteLimits_of_natIso z
  have : PreservesFiniteColimits I := preservesFiniteColimits_of_natIso z
  let ec := NatIso.mapHomologicalComplex e (.up ℤ)
  let ed := d ≪≫ Functor.mapDerivedCategoryNatIso e
  refine ⟨{
    scalar := e
    scalar_sections := he
    scalar_complex := ec
    scalar_complex_components := fun _ _ ↦ rfl
    scalar_derived := ed
    scalar_normalization := ?_
    ordinary := o
    derived := ?_
    normalization := ?_ }⟩
  · intro P
    change pbcComplexCounit c.hom P ≫ DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) = _
    rw [hd P, Category.assoc, ← Functor.mapDerivedCategoryNatIso_fac e P]
    simp only [ed, Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  · exact Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso z)
      (pbcDerivedExtend c.hom) ≪≫ Functor.isoWhiskerLeft I.mapDerivedCategory d ≪≫
      (Functor.mapDerivedCategoryCompIso I L).symm ≪≫ Functor.mapDerivedCategoryNatIso o
  · intro P
    rw [hd P]
    infer_instance

/-- Normalized module restriction for a coefficient ring, with exact termwise derived
restriction and the canonical unit formula on the same underlying object.
Source: Stacks 03EL and 06YY
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
structure ModuleComparison {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (b : ProEtaleObjectRestrictionComparison U CommRingCat.{u + 1}) where
  ordinary : proEtaleRingModulePullback U.hom R
      ((AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        U.hom U.prop).obj R) (b.sheafIso.app R) ≅ modules U R
  unit : ∀ (M : pbcModules X R) (V : X.ProEt) (m : M.val.obj (op V)),
    (ordinary.hom.app M).val.app (op ((proEtaleBaseChange U.hom).obj V))
      (proEtaleRingModuleUnitSection U.hom R _ (b.sheafIso.app R) M V m) =
        M.val.map (MorphismProperty.Over.homMk
          (pullback.fst V.hom U.hom) pullback.condition).op m
  complex :
    (proEtaleRingModulePullback U.hom R
      ((AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        U.hom U.prop).obj R) (b.sheafIso.app R)).mapHomologicalComplex (.up ℤ) ≅
      (modules U R).mapHomologicalComplex (.up ℤ)
  complex_components : ∀ P (n : ℤ), (complex.hom.app P).f n = ordinary.hom.app (P.X n)
  derived : proEtaleRingDerivedPullback U.hom R
      ((AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        U.hom U.prop).obj R) (b.sheafIso.app R) ≅ ContinuousSlice.derived U R
  normalization : ∀ P : CochainComplex (pbcModules X R) ℤ,
    (proEtaleRingDerivedPullbackFactors U.hom R _ (b.sheafIso.app R)).hom.app P ≫
        DerivedCategory.Q.map
          (complex.hom.app P) =
      derived.hom.app (DerivedCategory.Q.obj P) ≫
        (modules U R).mapDerivedCategoryFactors.hom.app P

private theorem module_adjunction_normalized {X Y : Scheme.{u}} (f : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    proEtaleRingModuleAdjunctionNormalized f R S c
      (proEtaleRingModuleAdjunction f R S c) := by
  intro M V m
  obtain ⟨g, hg, ht⟩ := (proEtaleRingModuleAdjunction_existsUnique f R S c).choose_spec.1
    M _ (𝟙 _)
  have h := ht (op V) m
  rw [Adjunction.homEquiv_id] at h
  rw [Adjunction.homEquiv_unit] at h
  exact h.trans (hg _ _)

private theorem moduleComparison_exists {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (b : ProEtaleObjectRestrictionComparison U CommRingCat.{u + 1})
    (bA : ProEtaleObjectRestrictionComparison U AddCommGrpCat.{u + 1}) :
    Nonempty (ModuleComparison U R b) := by
  let G := MorphismProperty.Over.map (f := U.hom) ⊤ U.prop
  let F := proEtaleBaseChange U.hom
  let : G.IsContinuous (ProEt.topology U.left) (ProEt.topology X) :=
    ProEt.isContinuous_overMap U.prop
  let : F.IsContinuous (ProEt.topology X) (ProEt.topology U.left) :=
    ProEt.isContinuous_overPullback U.hom
  let S := (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
    U.hom U.prop).obj R
  let c := b.sheafIso.app R
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ U.hom U.prop trivial
  let ψ := proEtaleRingDirectImageMap U.hom R S c
  have H1 : Functor.whiskerRight (NatTrans.op adj.counit) R.obj = ψ.hom := by
    apply NatTrans.ext
    funext V
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact ((proEtaleLocalizedRingMateGraphEvaluation U b bA R S c).1 V.unop r).symm
  let Rr := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let Sr := (sheafCompose (ProEt.topology U.left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
  let φ : Sr ⟶ (G.sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology U.left) (ProEt.topology X)).obj Rr := 𝟙 _
  let ψr : Rr ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology X) (ProEt.topology U.left)).obj Sr :=
    ⟨Functor.whiskerRight ψ.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have H1r : Functor.whiskerRight (NatTrans.op adj.counit) Rr.obj =
      ψr.hom ≫ F.op.whiskerLeft φ.hom := by
    apply NatTrans.ext
    funext V
    apply RingCat.hom_ext
    exact congrArg (fun t ↦ (t.app V).hom) H1
  have H2r : φ.hom ≫ G.op.whiskerLeft ψr.hom ≫
      Functor.whiskerRight (NatTrans.op adj.unit) Sr.obj = 𝟙 _ := by
    apply NatTrans.ext
    funext V
    apply RingCat.hom_ext
    apply RingHom.ext
    intro r
    change R.obj.map (G.map (adj.unit.app V.unop)).op
      (ψ.hom.app (op (G.obj V.unop)) r) = r
    have h := congrArg (fun t ↦ t.app (op (G.obj V.unop))) H1
    rw [← h]
    change R.obj.map (G.map (adj.unit.app V.unop)).op
      (R.obj.map (adj.counit.app (G.obj V.unop)).op r) = r
    erw [← Functor.map_comp_apply, ← op_comp, adj.left_triangle_components]
    exact ConcreteCategory.congr_hom (R.obj.map_id _) r
  let a := SheafOfModules.pushforwardPushforwardAdj.{u + 1} adj φ ψr H1r H2r
  let aa : proEtaleRingModulePullback U.hom R S c ⊣
      SheafOfModules.pushforward.{u + 1} ψr :=
    proEtaleRingModuleAdjunction U.hom R S c
  have : (SheafOfModules.pushforward.{u + 1} φ).Additive := (modules_exact U R).1
  have : PreservesFiniteLimits (SheafOfModules.pushforward.{u + 1} φ) :=
    (modules_exact U R).2.1
  have : PreservesFiniteColimits (SheafOfModules.pushforward.{u + 1} φ) :=
    (modules_exact U R).2.2
  let o := aa.leftAdjointUniq a
  let oc := NatIso.mapHomologicalComplex o (.up ℤ)
  let od := Functor.mapDerivedCategoryNatIso o
  refine ⟨{
    ordinary := o
    unit := ?_
    complex := oc
    complex_components := fun _ _ ↦ rfl
    derived := od
    normalization := ?_ }⟩
  · intro M V m
    have hu := congrArg (fun t ↦ (t.val.app (op V)) m)
      (Adjunction.unit_leftAdjointUniq_hom_app aa a M)
    have hn := module_adjunction_normalized U.hom R S c M V m
    change ((o.hom.app M).val.app (op (F.obj V)))
      (((aa.unit.app M).val.app (op V)) m) = _ at hu
    erw [hn] at hu
    exact hu
  · intro P
    exact (Functor.mapDerivedCategoryNatIso_fac o P).symm

/-- Restricting an ambient derived tensor pullback is scalar extension on the restricted
inverse image. The counit equation specifies the comparison on K-flat representatives.
Source: Stacks 03EL, 06YS, 0G7E and 06YY
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
structure Ambient {X Y : Scheme.{u}} (f : Y ⟶ X) (U : Y.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ⟶ S) where
  ordinary : pbcExtend c ⋙ modules U S ≅
    modules U ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) ⋙
      pbcExtend ((AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        U.hom U.prop).map c)
  sections : ∀ (M : pbcModules Y
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))
      (V : U.left.ProEtᵒᵖ) (s : S.obj.obj
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop)))
      (m : M.val.obj
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop))),
    (ordinary.hom.app M).val.app V (pbcTensorSection c M
        (op ((MorphismProperty.Over.map (f := U.hom) ⊤ U.prop).obj V.unop)) s m) =
      pbcTensorSection ((AlgebraicGeometry.ProEtale.localizationRestriction
        CommRingCat.{u + 1} U.hom U.prop).map c) ((modules U _).obj M) V s m
  complex : (pbcExtend c).mapHomologicalComplex (.up ℤ) ⋙
      (modules U S).mapHomologicalComplex (.up ℤ) ≅
    (modules U ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)).mapHomologicalComplex
      (.up ℤ) ⋙
      (pbcExtend ((AlgebraicGeometry.ProEtale.localizationRestriction
        CommRingCat.{u + 1} U.hom U.prop).map c)).mapHomologicalComplex (.up ℤ)
  complex_components : ∀ P (n : ℤ), (complex.hom.app P).f n = ordinary.hom.app (P.X n)
  scalar_derived : pbcDerivedExtend c ⋙ ContinuousSlice.derived U S ≅
    ContinuousSlice.derived U
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) ⋙
      pbcDerivedExtend ((AlgebraicGeometry.ProEtale.localizationRestriction
        CommRingCat.{u + 1} U.hom U.prop).map c)
  normalization : ∀ P : CochainComplex
      (pbcModules Y ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)) ℤ,
    (ContinuousSlice.derived U S).map (pbcComplexCounit c P) ≫
        (modules U S).mapDerivedCategoryFactors.hom.app
          (((pbcExtend c).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (complex.hom.app P) =
      scalar_derived.hom.app (DerivedCategory.Q.obj P) ≫
        (pbcDerivedExtend ((AlgebraicGeometry.ProEtale.localizationRestriction
          CommRingCat.{u + 1} U.hom U.prop).map c)).map
          ((modules U _).mapDerivedCategoryFactors.hom.app P) ≫
        pbcComplexCounit ((AlgebraicGeometry.ProEtale.localizationRestriction
          CommRingCat.{u + 1} U.hom U.prop).map c)
          (((modules U _).mapHomologicalComplex (.up ℤ)).obj P)

private theorem ambient_exists {X Y : Scheme.{u}} (f : Y ⟶ X) (U : Y.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ⟶ S) :
    Nonempty (Ambient f U R S c) := by
  obtain ⟨a⟩ := proEtaleScalarExtensionSliceComparison U
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) S c
  exact ⟨{
    ordinary := a.ordinary
    sections := a.sections
    complex := a.complex
    complex_components := a.complex_components
    scalar_derived := a.scalar_derived
    normalization := a.normalization }⟩

/-- The ambient formula after the actual geometric inverse image. This is obtained by
whiskering the counit-normalized scalar comparison, so it is fixed on representatives.
Source: Stacks 06YY and 03EL
(blueprint: lem-per-continuous-coefficient-slice-normalization). -/
def Ambient.pullback {X Y : Scheme.{u}} {f : Y ⟶ X} {U : Y.ProEt}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    {c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ⟶ S}
    (a : Ambient f U R S c) :=
  Functor.isoWhiskerLeft (adicTowerPullback f R) a.scalar_derived

/-- The complete slice normalization assertion. Geometric finiteness hypotheses are
used only for identifying completed coefficients and for the etale/immersion corollary.
Source: Bhatt--Scholze 6.8.1, 6.8.2, 6.8.6 and 6.8.15
(blueprint: lem-per-continuous-coefficient-slice-normalization).

Proof, following all seven steps of the node:
1. weaklyEtale_localization identifies coverings and literal restriction; U need not
be noetherian. 2. proEtaleObjectInverseImageRestriction identifies the distinguished
initial index and the Kan coprojection, and its sheafification unit is invertible.
3. At that index continuousCoefficientPullback is identity on functions. Postcomposition
commutes with precomposition, preserving A to E, residues and constants. The finite
constant-section theorem identifies residue sheaves; uniqueness gives every transition.
4. The normalized completion and localization comparisons identify B_X and B_X[1/varpi]
with A_X and E_X. The projections restrict sectionwise, not by a general assertion that
inverse image commutes with infinite limits. 5. localization_inverseImage_exact gives
exactness. For an isomorphism c, b tensor m maps to c inverse(b)m, inverse m maps to
1 tensor m, so scalar extension is exact and all complexes compute its derived functor.
6. An etale map is weakly etale (its diagonal is open, hence flat); use the slice result.
For an immersion use continuousCoefficientImmersionRestriction instead.
7. Resolve by flat-term K-flat complexes. KFlatRingedToposPullback preserves these under
inverse image and restriction. LocalizedSiteTensorRestriction sends each sheafified pure
tensor to the identical tensor, so its degreewise maps commute with differentials and
coefficient maps. RingedTopoiDerivedPullback makes the derived comparison independent of
the chosen resolution. Apply this for both the integral and rational rings. -/
theorem continuous_coefficient_slice_normalization (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    (∀ (X : Scheme.{u}) (U : X.ProEt), ∃ b : Coefficients U,
      ∃ a : Adic l E U.hom,
      Nonempty (ExactPull U.hom _ _ a.integral) ∧
      Nonempty (ExactPull U.hom _ _ a.rational) ∧
      ∀ R : Sheaf (ProEt.topology X) CommRingCat.{u + 1},
        Nonempty (ModuleComparison U R b.commRings)) ∧
    (∀ (X : Scheme.{u}) [IsNoetherian X]
      (_hd : ∃ n : ℕ, topologicalKrullDim X ≤ n)
      (_hi : ∀ x : X, IsUnit (l : X.presheaf.stalk x)),
      Nonempty (Completion l E X)) ∧
    (∀ (X Y : Scheme.{u}) [IsNoetherian X] [IsNoetherian Y]
      (_hdX : ∃ n : ℕ, topologicalKrullDim X ≤ n)
      (_hdY : ∃ n : ℕ, topologicalKrullDim Y ≤ n)
      (_hiX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
      (_hiY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) (g : Y ⟶ X),
      (Etale g ∨ IsImmersion g) →
      ∃ a : Adic l E g,
        Nonempty (ExactPull g _ _ a.integral) ∧
        Nonempty (ExactPull g _ _ a.rational) ∧
        ∀ (bX : Completion l E X) (bY : Completion l E Y),
          Nonempty (CompletedPull l E g a bX bY)) ∧
    (∀ (X Y : Scheme.{u}) (f : Y ⟶ X) (U : Y.ProEt)
      (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (integralCoefficientSheaf l X E) ⟶ integralCoefficientSheaf l Y E),
      integralCoefficientRestrictionNormalized l E f c → Nonempty (Ambient f U _ _ c)) ∧
    (∀ (X Y : Scheme.{u}) (f : Y ⟶ X) (U : Y.ProEt)
      (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (rationalCoefficientSheaf l X E) ⟶ rationalCoefficientSheaf l Y E),
      rationalCoefficientRestrictionNormalized l E f c → Nonempty (Ambient f U _ _ c)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X U
    obtain ⟨b⟩ := coefficients_exists U
    let := coefficientExtensionNormedField l E
    let A := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)
    let K := ULift.{u + 1, u} E
    obtain ⟨a⟩ := adic_exists l E U.hom ⟨(b.continuous A).1, (b.continuous K).1⟩
    exact ⟨b, a, exactPull_exists U.hom _ _ a.integral,
      exactPull_exists U.hom _ _ a.rational,
      fun R ↦ moduleComparison_exists U R b.commRings b.groups⟩
  · intro X _ _ _
    exact completion_exists l E X
  · intro X Y _ _ _ _ _ _ g hg
    have h : let := coefficientExtensionNormedField l E
        IsIso (continuousCoefficientPullback
          (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) g) ∧
        IsIso (continuousCoefficientPullback (ULift.{u + 1, u} E) g) := by
      let := coefficientExtensionNormedField l E
      rcases hg with hg | hg
      · let := hg
        obtain ⟨b⟩ := coefficients_exists (ProEt.mk g)
        exact ⟨(b.continuous _).1, (b.continuous _).1⟩
      · let := hg
        exact continuousCoefficientPullback_isIso l E X g
    obtain ⟨a⟩ := adic_exists l E g h
    exact ⟨a, exactPull_exists g _ _ a.integral, exactPull_exists g _ _ a.rational,
      fun bX bY ↦ completedPull_exists l E g a bX bY⟩
  · intro X Y f U c _
    exact ambient_exists f U _ _ c
  · intro X Y f U c _
    exact ambient_exists f U _ _ c

end AlgebraicGeometry.Scheme.ContinuousSlice
