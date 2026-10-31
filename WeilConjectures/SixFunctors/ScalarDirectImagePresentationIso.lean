/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixDirectImage
public import WeilConjectures.SixFunctors.ListedScalarCoefficientMaps
import all WeilConjectures.SixFunctors.ScalarSixCtf
import all WeilConjectures.SixFunctors.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ScalarDirectImageElementaryCases
import WeilConjectures.SixFunctors.ListedCoefficientCtf
import WeilConjectures.SixFunctorsBasics.FiniteCoefficientSmallCarrierComparison
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-! # Direct-image comparison under changes of coefficient presentation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard
  Functor.leftDerivedFunctor

attribute [local implicit_reducible] CommMon.toMon
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory
  AlgebraicGeometry.ProEtale.sheafBraidedCategory
  AlgebraicGeometry.ProEtale.sheafSymmetricCategory
  Mod.monoidalCategory Monoidal.induced

private instance presentationRing_comm (Λ : ScalarSixRing.{u}) : IsCommMonObj Λ.X :=
  Λ.comm

private instance presentationCoefficient_comm (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    IsCommMonObj (condensedRingObj Λ.X X) :=
  isCommMonObj_condensedRingObj Λ.X X

private instance presentationMap_isMonHom {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') :
    IsMonHom a.hom.hom := a.hom.isMonHom_hom

private noncomputable instance presentationModulesClosed
    (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    MonoidalClosed (ModuleRingedComparison.internalModules Λ.X X) := by
  have h : IsCommMonObj (condensedRingObj Λ.X X) :=
    isCommMonObj_condensedRingObj Λ.X X
  exact @Mod.monoidalClosed _ _ _ _ _ _ _ _ _ h

private noncomputable instance presentationModulesSymmetric
    (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    SymmetricCategory (ModuleRingedComparison.internalModules Λ.X X) := by
  have h : IsCommMonObj (condensedRingObj Λ.X X) :=
    isCommMonObj_condensedRingObj Λ.X X
  exact @Mod.symmetricCategory _ _ _ _ _ _ _ _ _ h


private instance presentationModulesFlat
    (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    Abelian.HasFunctorialFlatResolution (ModuleRingedComparison.internalModules Λ.X X) := by
  have h : IsCommMonObj (condensedRingObj Λ.X X) :=
    isCommMonObj_condensedRingObj Λ.X X
  exact @Mod.hasFunctorialFlatResolution _ _ _ _ _ _ _ _ _ h inferInstance

private instance presentationDerivedTensor (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    (DerivedCategory.Qh (C := ModuleRingedComparison.internalModules Λ.X X)
      ).HasDerivedMonoidalCategory
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
  DerivedCategory.hasDerivedMonoidalCategory _


private theorem scalarSixChange_equivalence {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') [IsIso a] (X : Scheme.{u}) :
    (scalarSixChange a X).IsEquivalence := by
  have : IsCommMonObj Λ.X := Λ.comm
  have : IsCommMonObj Λ'.X := Λ'.comm
  have ha : IsIso a.hom.hom := inferInstance
  have hφ : IsIso (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X) := by
    change IsIso ((upperStarFromPoint X).map a.hom.hom)
    infer_instance
  let : (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).isEquivalence_functor
  exact (scalarSixScalarAdjunction a X).isEquivalence_left_of_isEquivalence_right

private theorem scalarDirectImageMate_isIso_of_iso {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') [IsIso a] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (scalarDirectImageMate a f) := by
  let := scalarSixChange_equivalence a X
  let := scalarSixChange_equivalence a Y
  have : IsIso (TwoSquare.mk (scalarSixChange a Y) (RootCoordinateFace.upper Λ.X f)
      (RootCoordinateFace.upper Λ'.X f) (scalarSixChange a X)
      (scalarDirectImagePullbackData.theta a f).inv).natTrans :=
    inferInstanceAs (IsIso (scalarDirectImagePullbackData.theta a f).inv)
  exact isIso_mateEquiv_of_isEquivalence
    (RootCoordinateFace.adjunction Λ.X f) (RootCoordinateFace.adjunction Λ'.X f)
    (TwoSquare.mk _ _ _ _ (scalarDirectImagePullbackData.theta a f).inv)

set_option maxHeartbeats 2000000 in
-- Compare the coefficient-adjunction presentations without expanding resolutions.
private theorem scalarCtf_admissible (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ.X)
    (hΛ' : IsLocalizingAdmissibleCoefficient ell Λ'.X)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    ∀ K : ConstantModelConstructibleFiniteTor Λ.X X.left,
      constantModelBoundedConstructible Λ'.X X.left ((scalarSixChange a X.left).obj K.obj) ∧
        DerivedCategory.finiteTorAmplitude _ ((scalarSixChange a X.left).obj K.obj) := by
  have generation (K : ConstantModelConstructibleFiniteTor Λ.X X.left) :
      ∃ n : ℕ, (((sfbPerfectScalarGenerator Λ X).shiftClosure ℤ).extensionProductIter n
        ).retractClosure K.obj := by
    rcases hΛ with hfinite | hother
    · obtain ⟨A, hA, tA, dA, rA, hf, hn, ⟨e⟩⟩ := hfinite
      let := hA
      let := tA
      let := dA
      let := rA
      let := hf
      exact sfbFiniteScalarGeneration A e X K
    · exact sfbNonfiniteScalarGeneration ell hother k X K
  have models (S : Scheme.{u}) (i : S ⟶ X.left) (hi : IsImmersion i)
      (P : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S))
      (hP : IsLocallyPerfectScalarModel Λ.X S P) :
      IsLocallyPerfectScalarModel Λ'.X S ((scalarSixChange a S).obj P) ∧
      constantModelBoundedConstructible Λ'.X X.left
        ((sfbLocallyClosedDerivedExtension Λ' i hi).obj ((scalarSixChange a S).obj P)) ∧
      DerivedCategory.finiteTorAmplitude _
        ((sfbLocallyClosedDerivedExtension Λ' i hi).obj ((scalarSixChange a S).obj P)) := by
    have hp := scalarSix_locallyPerfect a S P hP
    exact ⟨hp, sfbPerfectLocallyClosedExtension ell Λ' hΛ' k X S i hi _ hp⟩
  let F := scalarSixChange a X.left
  let Q := constantModelBoundedConstructible Λ'.X X.left ⊓
    DerivedCategory.finiteTorAmplitude (ModuleRingedComparison.internalModules Λ'.X X.left)
  obtain ⟨ht, hr⟩ := sfbAdmissibleConstructibleThickness ell Λ' hΛ' k X
  have : (constantModelBoundedConstructible Λ'.X X.left).IsTriangulated := ht
  have : (constantModelBoundedConstructible Λ'.X X.left).IsStableUnderRetracts := hr
  have htor := constantModelConstructibleFiniteTor_wellDefined Λ'.X X.left
  have : (DerivedCategory.finiteTorAmplitude
      (ModuleRingedComparison.internalModules Λ'.X X.left)).IsTriangulated :=
    htor.2.2.2.2.2.2.2.1
  have : (DerivedCategory.finiteTorAmplitude
      (ModuleRingedComparison.internalModules Λ'.X X.left)).IsStableUnderRetracts :=
    htor.2.2.2.2.2.2.2.2
  have : Q.IsTriangulated := inferInstance
  have : Q.IsStableUnderRetracts := ⟨fun r h ↦
    ⟨(constantModelBoundedConstructible Λ'.X X.left).prop_of_retract r h.1,
      (DerivedCategory.finiteTorAmplitude _).prop_of_retract r h.2⟩⟩
  let adj : F ⊣ (Mod.comap
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X.left)).mapDerivedCategory :=
    scalarSixScalarAdjunction a X.left
  let : F.CommShift ℤ := adj.leftAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_rightAdjoint ℤ
  have : F.IsTriangulated := adj.isTriangulated_leftAdjoint
  let R := Q.inverseImage F
  have : R.IsTriangulated := inferInstance
  have : R.IsStableUnderRetracts :=
    ⟨fun r h ↦ Q.prop_of_retract (r.map F) h⟩
  have generators : sfbPerfectScalarGenerator Λ X ≤ R := by
    rintro K ⟨S, i, hi, P, hP, ⟨e⟩⟩
    obtain ⟨c⟩ := sfbCanonicalExtensionScalarComparison a ell k X S i hi P
    exact Q.prop_of_iso (F.mapIso e ≪≫ c).symm (models S i hi P hP).2
  intro K
  obtain ⟨n, hn⟩ := generation K
  exact scalarSix_finiteClosure_le (sfbPerfectScalarGenerator Λ X) R generators n K.obj hn

private theorem scalarDirectImageMate_comp_isIso
    {Λ Λ' Λ'' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'')
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X))
    [IsIso ((scalarDirectImageMate a f).app K)]
    [IsIso ((scalarDirectImageMate b f).app ((scalarSixChange a X).obj K))] :
    IsIso ((scalarDirectImageMate (a ≫ b) f).app K) := by
  have heq := (scalarDirectImageMateCoherence a f (𝟙 Y)).2.2.2.2 Λ'' b K
  have hcomp : IsIso
      ((scalarSixTower a b Y).hom.app ((RootCoordinateFace.lower Λ.X f).obj K) ≫
        (scalarDirectImageMate (a ≫ b) f).app K) := by
    rw [heq]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((scalarSixTower a b Y).hom.app ((RootCoordinateFace.lower Λ.X f).obj K)) _

set_option maxHeartbeats 2000000 in
-- Compare the coefficient-adjunction presentations without expanding resolutions.
private theorem scalarDirectImageMate_iso_conjugate
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {Λ Λ' Γ Γ' : ScalarSixRing.{u}} (e : Γ ≅ Λ) (e' : Λ' ≅ Γ') (b : Λ ⟶ Λ')
    (hΓ : IsLocalizingAdmissibleCoefficient ell Γ.X)
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ.X)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    (hb : ∀ K : ConstantModelConstructibleFiniteTor Λ.X X.left,
      IsIso ((scalarDirectImageMate b f.left).app K.obj))
    (K : ConstantModelConstructibleFiniteTor Γ.X X.left) :
    IsIso ((scalarDirectImageMate (e.hom ≫ b ≫ e'.hom) f.left).app K.obj) := by
  have hK := scalarCtf_admissible ell k e.hom hΓ hΛ X K
  let := scalarDirectImageMate_isIso_of_iso e.hom f.left
  let := scalarDirectImageMate_isIso_of_iso e'.hom f.left
  let := hb ⟨_, hK⟩
  let := scalarDirectImageMate_comp_isIso b e'.hom f.left
    ((scalarSixChange e.hom X.left).obj K.obj)
  exact scalarDirectImageMate_comp_isIso e.hom (b ≫ e'.hom) f.left K.obj

set_option maxHeartbeats 5000000 in
-- Compare the coefficient-adjunction presentations without expanding resolutions.
/-- The normalized direct-image mate is invertible for every listed scalar map,
including arbitrary isomorphic coefficient presentations.
Source: scalar-six direct-image proof, coefficient cases and formal properties
(blueprint: lem-sfb-scalar-direct-image-presentation-iso).

Proof: apply the six native elementary comparison cases after comparing finite
small carriers with their lifted native carriers. Scalar extension along a ring
isomorphism is an equivalence, since its right adjoint is restriction along an
isomorphism. The mate-of-equivalences lemma therefore covers both presentation
arrows. For composites use scalarDirectImageMateCoherence and preservation of
Dctf. For presentation transport first extend along the source isomorphism,
apply the inductive comparison, and extend along the target isomorphism. The
same scalar-tower equation identifies this pasted map with the stipulated mate.
Preservation across the source isomorphism follows from the finite perfect
scalar generation theorem and the canonical extension comparison. -/
theorem scalarDirectImagePresentationIso
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (ha : IsListedScalarCoefficientMap ell a)
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) :
    ∀ K : ConstantModelConstructibleFiniteTor Λ.X X.left,
      IsIso ((scalarDirectImageMate a f.left).app K.obj) := by
  obtain ⟨hfin, hint, hfield, hloc, hclosure, hintfin, hid⟩ :=
    scalarDirectImageElementaryCases ell k f
  induction ha with
  | @finite A B _ _ _ _ _ _ _ _ _ _ n m hA hB φ hφ =>
    intro K
    let AU := ULift.{u} A
    let BU := ULift.{u} B
    let eA := finiteCoefficientCarrierIso AU A ULift.ringEquiv
    let eB := finiteCoefficientCarrierIso BU B ULift.ringEquiv
    let b := eA.hom ≫ scalarSixContinuousMap φ hφ ≫ eB.inv
    let ψ : AU →+* BU :=
      ULift.ringEquiv.symm.toRingHom.comp (φ.comp ULift.ringEquiv.toRingHom)
    have hnA : ∃ n : ℕ, ∀ x : AU, (ell ^ n) • x = 0 := by
      refine ⟨n, fun x ↦ ?_⟩
      apply ULift.ext
      change (ell ^ n) • x.down = (0 : A)
      simp only [nsmul_eq_mul, Nat.cast_pow, hA, zero_mul]
    have hnB : ∃ n : ℕ, ∀ x : BU, (ell ^ n) • x = 0 := by
      refine ⟨m, fun x ↦ ?_⟩
      apply ULift.ext
      change (ell ^ m) • x.down = (0 : B)
      simp only [nsmul_eq_mul, Nat.cast_pow, hB, zero_mul]
    have hb : ListedCoefficientMap ell b :=
      .finite AU BU hnA hnB ψ b (by intros; rfl)
    obtain ⟨hAU, hBU, _⟩ := listedCoefficientCtf ell b hb
    have hA' := scalarSix_admissible_iso ell eA.symm hAU
    have h := scalarDirectImageMate_iso_conjugate ell k eA.symm eB b hA' hAU f
      (fun L ↦ hfin AU BU hnA hnB ψ b (by intros; rfl) L.obj L.property) K
    have he : eA.symm.hom ≫ b ≫ eB.hom = scalarSixContinuousMap φ hφ := by
      dsimp only [b, Iso.symm_hom]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    rw [he] at h
    exact h
  | integral h =>
    intro K
    exact hint _ _ h _ (by rfl) K.obj K.property
  | field h =>
    intro K
    exact hfield _ _ h _ rfl K.obj K.property
  | localization E =>
    intro K
    exact hloc E _ rfl K.obj K.property
  | algebraicClosure E =>
    intro K
    exact hclosure E _ rfl K.obj K.property
  | @integralFinite E A _ _ _ _ _ n hA φ hφ =>
    intro K
    let AU := ULift.{u} A
    let eA := finiteCoefficientCarrierIso AU A ULift.ringEquiv
    let b := scalarSixContinuousMap φ hφ ≫ eA.inv
    let ψ : PadicAlgCl.integers ell E.1 →+* AU :=
      ULift.ringEquiv.symm.toRingHom.comp φ
    have hnA : ∃ n : ℕ, ∀ x : AU, (ell ^ n) • x = 0 := by
      refine ⟨n, fun x ↦ ?_⟩
      apply ULift.ext
      change (ell ^ n) • x.down = (0 : A)
      simp only [nsmul_eq_mul, Nat.cast_pow, hA, zero_mul]
    let : TopologicalSpace AU := ⊥
    let : DiscreteTopology AU := ⟨rfl⟩
    have hψ : Continuous ψ := by
      have hUp : Continuous (ULift.up : A → AU) := continuous_of_discreteTopology
      exact hUp.comp hφ
    have hb : IsIntegralFiniteScalarMap ell E AU b := ⟨ψ, hψ, by intros; rfl⟩
    let : IsIso ((scalarDirectImageMate b f.left).app K.obj) :=
      hintfin E AU hnA b hb K.obj K.property
    let := scalarDirectImageMate_isIso_of_iso eA.hom f.left
    have h := scalarDirectImageMate_comp_isIso b eA.hom f.left K.obj
    have he : b ≫ eA.hom = scalarSixContinuousMap φ hφ := by
      dsimp only [b]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [he] at h
    exact h
  | comp ha hb iha ihb =>
    intro K
    let := iha K
    let := ihb ⟨_, (scalarSixCtf ell k _ ha X).2.2 K⟩
    exact scalarDirectImageMate_comp_isIso _ _ f.left K.obj
  | iso e e' ha iha =>
    intro K
    obtain ⟨hΛ, hΛ'⟩ := scalarSix_listed_admissible ell ha
    have hΓ := scalarSix_admissible_iso ell e hΛ
    exact scalarDirectImageMate_iso_conjugate ell k e e' _ hΓ hΛ f iha K

end AlgebraicGeometry.ProEtale.CondensedRing

-- validation retry 2026-10-30
