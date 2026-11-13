/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedTensor
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Over
import all WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.AlgebraicGeometry.Finite.FiniteTensorConstructibleCohomology

/-!
# Derived tensor on the finite-Tor constructible subcategory

The two derived inputs are expressed by arbitrary cochain representatives `K` and `M`.
The tensor is the recorded `derivedTensor`, using any K-flat resolution `f : P ⟶ K`.
Its defining quasi-isomorphism and K-flatness conditions specify the computation,
without placing any additional condition on the derived inputs.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

set_option synthInstance.maxSize 2048 in
/-- Tensoring a bounded constructible complex by a finite-Tor constructible complex
preserves bounded constructibility. If both inputs have Tor intervals, the output
is finite-Tor constructible with the sum interval. -/
theorem finiteCoefficient_tensor_ctf
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    (K M P : CochainComplex (proEtaleRingModules X
      (proEtaleConstantRing X (Padic.coefficientExtensionRing l E n))) ℤ)
    (f : P ⟶ K) (hf : QuasiIso f)
    (hP : CochainComplex.IsAcyclicTensorKFlat.{u + 1, u}
      (R := proEtaleConstantRing X (Padic.coefficientExtensionRing l E n)) P)
    (a b : ℤ)
    (_hK : WeilConjectures.finiteTorConstructible l E n hn X (DerivedCategory.Q.obj K))
    (_hKa : HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E n)
      (DerivedCategory.Q.obj K) a b)
    (_hM : intrinsicFiniteTorsionConstructible l E n hn X (DerivedCategory.Q.obj M)) :
    intrinsicFiniteTorsionConstructible l E n hn X
      (derivedTensor X (Padic.coefficientExtensionRing l E n) K M P f hf hP) ∧
    ∀ c d : ℤ,
      WeilConjectures.finiteTorConstructible l E n hn X (DerivedCategory.Q.obj M) →
      HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E n)
        (DerivedCategory.Q.obj M) c d →
      WeilConjectures.finiteTorConstructible l E n hn X
        (derivedTensor X (Padic.coefficientExtensionRing l E n) K M P f hf hP) ∧
      HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E n)
        (derivedTensor X (Padic.coefficientExtensionRing l E n) K M P f hf hP)
        (a + c) (b + d) := by
  classical
  let A := Padic.coefficientExtensionRing l E n
  let R := proEtaleConstantRing X A
  let C := proEtaleRingModules X R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.monoidalClosed_kfg (R := R)
  have := SheafOfModules.monoidalPreadditive_kfg R
  have := SheafOfModules.isGrothendieckAbelian_kfg R
  have := SheafOfModules.hasFunctorialFlatResolution_kfg R
  have : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} C
  let := HasDerivedCategory.standard C
  have := DerivedCategory.hasDerivedMonoidalCategory C
  let : MonoidalCategory (DerivedCategory C) := inferInstance
  have hk (P : CochainComplex C ℤ)
      (hP : CochainComplex.IsAcyclicTensorKFlat (R := R) P) :
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P := by
    rw [← HomotopyCategory.kFlat_quotient_obj_iff,
      HomotopyCategory.kFlat_iff_preserves_acyclic]
    intro N hN
    obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
    have hright : HomotopyCategory.subcategoryAcyclic C
        (MonoidalCategory.tensorObj ((HomotopyCategory.quotient C (.up ℤ)).obj N)
          ((HomotopyCategory.quotient C (.up ℤ)).obj P)) := by
      exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (hP N hN)
    exact ⟨(HomotopyCategory.subcategoryAcyclic C).prop_of_iso (β_ _ _) hright, hright⟩
  have heq (L M P : CochainComplex C ℤ) (f : P ⟶ L) (hf : QuasiIso f)
      (hP : CochainComplex.IsAcyclicTensorKFlat (R := R) P) :
      Nonempty (MonoidalCategory.tensorObj (DerivedCategory.Q.obj L) (DerivedCategory.Q.obj M) ≅
        derivedTensor X A L M P f hf hP) := by
    have : IsIso (DerivedCategory.Q.map f) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso C f).2 hf
    exact ⟨MonoidalCategory.tensorIso (asIso (DerivedCategory.Q.map f)).symm (Iso.refl _) ≪≫
      DerivedCategory.QObjTensorQObjIsoOfKFlatLeft P M (hk P hP)⟩
  have hamp (Z : DerivedCategory C) (a b : ℤ) (hab : a ≤ b) :
      HasProEtaleTorAmplitude X A Z a b ↔ DerivedCategory.torAmplitudeIn C a b Z := by
    constructor
    · intro h M
      have : (DerivedCategory.Q (C := C)).EssSurj :=
        Localization.essSurj _ (HomologicalComplex.quasiIso _ (.up ℤ))
      let L := (DerivedCategory.Q (C := C)).objPreimage Z
      let e := (DerivedCategory.Q (C := C)).objObjPreimageIso Z
      obtain ⟨P, f, hP, _, hf, _⟩ := CochainComplex.exists_isKFlatResolutionGeneral L
      obtain ⟨eq⟩ := heq L ((HomologicalComplex.single C (.up ℤ) 0).obj M) P f hf hP
      let eq' := MonoidalCategory.tensorIso e.symm
        ((DerivedCategory.singleFunctorIsoCompQ C 0).app M) ≪≫ eq
      rw [DerivedCategory.homologyConcentratedIn_iff]
      refine ⟨(DerivedCategory.isGE_iff _ a).2 ?_, (DerivedCategory.isLE_iff _ b).2 ?_⟩
      · intro i hi
        exact (h.2 L P ⟨e⟩ f hf hP M i (.inl hi)).of_iso
          ((DerivedCategory.homologyFunctor C i).mapIso eq')
      · intro i hi
        exact (h.2 L P ⟨e⟩ f hf hP M i (.inr hi)).of_iso
          ((DerivedCategory.homologyFunctor C i).mapIso eq')
    · intro h
      refine ⟨hab, ?_⟩
      rintro L P ⟨e⟩ f hf hP M i hi
      obtain ⟨eq⟩ := heq L ((HomologicalComplex.single C (.up ℤ) 0).obj M) P f hf hP
      let eq' := MonoidalCategory.tensorIso e.symm
        ((DerivedCategory.singleFunctorIsoCompQ C 0).app M) ≪≫ eq
      have hz : IsZero ((DerivedCategory.homologyFunctor C i).obj
          (MonoidalCategory.tensorObj Z ((DerivedCategory.singleFunctor C 0).obj M))) := by
        obtain ⟨hge, hle⟩ := (DerivedCategory.homologyConcentratedIn_iff _ _ _).1 (h M)
        rcases hi with hi | hi
        · exact (DerivedCategory.isGE_iff _ a).1 hge i hi
        · exact (DerivedCategory.isLE_iff _ b).1 hle i hi
      exact hz.of_iso ((DerivedCategory.homologyFunctor C i).mapIso eq'.symm)
  obtain ⟨e⟩ := heq K M P f hf hP
  have hKa := (hamp _ a b _hKa.1).1 _hKa
  have hunit : IsUnit (l : D.k) := by
    let := Fintype.ofFinite D.k₀
    let : Fact D.p.Prime := ⟨D.prime⟩
    have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
        (D.card_base.trans D.cardinality_eq))
    have : CharP D.k D.p :=
      charP_of_injective_algebraMap (algebraMap D.k₀ D.k).injective D.p
    exact (CharP.isUnit_natCast_iff (R := D.k) D.prime).2
      (fun h ↦ _hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 h).symm)
  let residueMap (x : X) : D.k →+* X.residueField x :=
    ((Scheme.ΓSpecIso (.of D.k)).inv ≫
      (X ↘ Spec (.of D.k)).appTop ≫ X.Γevaluation x).hom
  let : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
    (map_natCast (residueMap x) l) ▸ (hunit.map (residueMap x)).invertible
  have hbounded : intrinsicFiniteTorsionConstructible l E n hn X
      (derivedTensor X A K M P f hf hP) := by
    refine ⟨?_, fun i ↦ finiteTensor_constructible_cohomology l E n hn X K M P f hf hP
      _hK.1 _hM i⟩
    obtain ⟨c, hc⟩ := _hM.1.bddBelow
    obtain ⟨d, hd⟩ := _hM.1.bddAbove
    have hM : DerivedCategory.homologyConcentratedIn c d (DerivedCategory.Q.obj M) := by
      refine ⟨(DerivedCategory.isGE_iff _ c).2 ?_, (DerivedCategory.isLE_iff _ d).2 ?_⟩
      · intro i hi
        by_contra hz
        exact (not_le_of_gt hi) (hc hz)
      · intro i hi
        by_contra hz
        exact (not_le_of_gt hi) (hd hz)
    have : (DerivedCategory.Q.obj M).IsGE c := hM.1
    have : (DerivedCategory.Q.obj M).IsLE d := hM.2
    have hT := And.intro
      (DerivedCategory.isGE_tensor_of_torAmplitudeIn hKa (DerivedCategory.Q.obj M) c)
      (DerivedCategory.isLE_tensor_of_torAmplitudeIn hKa (DerivedCategory.Q.obj M) d)
    apply (Set.finite_Icc (a + c) (b + d)).subset
    intro i hi
    refine ⟨?_, ?_⟩
    · by_contra h
      exact hi ((DerivedCategory.isGE_iff _ _).1 hT.1 i (by omega) |>.of_iso
        ((DerivedCategory.homologyFunctor C i).mapIso e.symm))
    · by_contra h
      exact hi ((DerivedCategory.isLE_iff _ _).1 hT.2 i (by omega) |>.of_iso
        ((DerivedCategory.homologyFunctor C i).mapIso e.symm))
  refine ⟨hbounded, ?_⟩
  intro c d hM hMa
  have hMa' := (hamp _ c d hMa.1).1 hMa
  have hT : DerivedCategory.torAmplitudeIn C (a + c) (b + d)
      (MonoidalCategory.tensorObj (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M)) := by
    intro F
    have := (hMa' F).1
    have := (hMa' F).2
    have := DerivedCategory.isGE_tensor_of_torAmplitudeIn hKa
      (MonoidalCategory.tensorObj (DerivedCategory.Q.obj M)
        ((DerivedCategory.singleFunctor C 0).obj F)) c
    have := DerivedCategory.isLE_tensor_of_torAmplitudeIn hKa
      (MonoidalCategory.tensorObj (DerivedCategory.Q.obj M)
        ((DerivedCategory.singleFunctor C 0).obj F)) d
    exact ⟨DerivedCategory.TStructure.t.isGE_of_iso
        (MonoidalCategory.associator (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj M) _).symm (a + c),
      DerivedCategory.TStructure.t.isLE_of_iso
        (MonoidalCategory.associator (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj M) _).symm (b + d)⟩
  have hTor := (hamp _ (a + c) (b + d) (add_le_add _hKa.1 hMa.1)).2
    ((DerivedCategory.torAmplitudeIn C (a + c) (b + d)).prop_of_iso e hT)
  exact ⟨⟨hbounded, a + c, b + d, hTor⟩, hTor⟩

end AlgebraicGeometry.Scheme
