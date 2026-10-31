/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ListedScalarCoefficientMaps
import WeilConjectures.SixFunctorsBasics.FiniteCoefficientSmallCarrierComparison

/-! # Primitive listed coefficient maps and scalar-six presentations

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-scalar-six/det-prop-scalar-six-ctf.md, Clause (3), listed scalar-map presentation
normalization used in the proof of scalar extension preservation
(blueprint: lem-sfb-listed-coefficient-presentation-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem nilpotent_small_carrier {A : Type u} [CommRing A]
    {T : Type} [CommRing T] (ell : ℕ) (r : A ≃+* T)
    (hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0) :
    ∃ n : ℕ, (ell : T) ^ n = 0 := by
  obtain ⟨n, hn⟩ := hA
  refine ⟨n, ?_⟩
  simpa [nsmul_eq_mul] using congrArg r (hn 1)

private theorem comparisonMap_eq {T T' : Type} [CommRing T] [CommRing T']
    [TopologicalSpace T] [IsTopologicalRing T]
    [TopologicalSpace T'] [IsTopologicalRing T']
    (f : T →+* T') (hf : Continuous f) :
    finiteCoefficientComparisonMap.{u} f hf = scalarSixContinuousMap f hf := by
  ext S s
  rfl

/-- Each of the six primitive constructors of `ListedCoefficientMap` yields the
same actual arrow in `IsListedScalarCoefficientMap`; no flatness is required.

Proof: (i) use `lem-sfb-finite-coefficient-small-carrier-comparison` to replace
both finite carriers by small discrete rings. Conjugate the ring map by their
ring equivalences. Evaluating ell-power annihilation at 1 yields nilpotence of
ell in each small ring. The section formula gives the commuting comparison
square, so the finite and iso constructors apply. (ii) Unfold the two integral
inclusions: both postcompose by the same inclusion of valuation subrings; the
scalar-tower witnesses are proofs of the same proposition. (iii) The field
endpoints and stipulated map are the scalar-six field generator. (iv) The
localization endpoints and map are exactly `scalarSixIntegralToField`.
(v) The finite-subextension-to-closure map is exactly the closure generator,
with finite-subextension-valued sections. (vi) The integral endpoint is the
same continuous-function ring in both presentations. Replace the finite target
by its small discrete carrier using the same comparison lemma. Conjugating the
continuous ring map on the target remains continuous, and evaluating the
annihilation hypothesis at 1 gives the scalar constructor's nilpotence
condition. Its mixed-source section equation and the iso constructor identify
the given arrow itself with this generator after the presentation change.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-scalar-six/_section.md, coefficient list (1)--(3), and
sk-prop-scalar-six/det-prop-scalar-six-ctf.md, Clause (3)
(blueprint: lem-sfb-listed-coefficient-presentation-transport). -/
theorem listedCoefficientPresentationTransport (ell : ℕ) [Fact ell.Prime] :
    (∀ (A B : Type u) [CommRing A] [CommRing B] [Finite A] [Finite B]
      (_hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
      (_hB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0)
      (φ : A →+* B)
      (a : (⟨cartesianFinitePointRing A⟩ : ScalarSixRing.{u}) ⟶
        ⟨cartesianFinitePointRing B⟩)
      (_ha : ∀ (P : Profinite.{u}) (s : (cartesianFinitePointRing A).obj.obj (op P)) (x : P),
        ((a.hom.hom.hom.app (op P)) s).down x = φ (s.down x)),
      IsListedScalarCoefficientMap ell a) ∧
    (∀ (E F : PadicAlgCl.FiniteIntermediateField ell) (h : E ≤ F)
      (a : (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u}) ⟶
        ⟨Profinite.padicIntegersRingObj ell F.1⟩)
      (_ha : a.hom.hom = finiteCoefficientIntegersPointMap ell h),
      IsListedScalarCoefficientMap ell a) ∧
    (∀ (E F : PadicAlgCl.FiniteIntermediateField ell) (h : E ≤ F)
      (a : (⟨Profinite.continuousMapRingObj E.1⟩ : ScalarSixRing.{u}) ⟶
        ⟨Profinite.continuousMapRingObj F.1⟩)
      (_ha : a.hom.hom = Profinite.padicSubfieldRingObjMap ell h),
      IsListedScalarCoefficientMap ell a) ∧
    (∀ (E : PadicAlgCl.FiniteIntermediateField ell)
      (a : (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u}) ⟶
        ⟨Profinite.continuousMapRingObj E.1⟩)
      (_ha : a.hom.hom = (sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing ell E.1)),
      IsListedScalarCoefficientMap ell a) ∧
    (∀ (E : PadicAlgCl.FiniteIntermediateField ell)
      (a : (⟨Profinite.continuousMapRingObj E.1⟩ : ScalarSixRing.{u}) ⟶
        ⟨Profinite.padicAlgClRingObj ell⟩)
      (_ha : a.hom.hom = Profinite.padicSubfieldRingObjToPadicAlgCl ell E),
      IsListedScalarCoefficientMap ell a) ∧
    (∀ (E : PadicAlgCl.FiniteIntermediateField ell)
      (A : Type u) [CommRing A] [Finite A]
      (_hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
      (a : (⟨Profinite.padicIntegersRingObj ell E.1⟩ : ScalarSixRing.{u}) ⟶
        ⟨cartesianFinitePointRing A⟩)
      (_ha : IsIntegralFiniteScalarMap ell E A a), IsListedScalarCoefficientMap ell a) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A B _ _ _ _ hA hB φ a ha
    obtain ⟨A₀, instA₀, finA₀, ⟨rA⟩⟩ := finiteCoefficientSmallCarrierComparison.1 A
    obtain ⟨B₀, instB₀, finB₀, ⟨rB⟩⟩ := finiteCoefficientSmallCarrierComparison.1 B
    let := instA₀
    let := instB₀
    let := finA₀
    let := finB₀
    let : TopologicalSpace A₀ := ⊥
    let : TopologicalSpace B₀ := ⊥
    let : DiscreteTopology A₀ := discreteTopology_bot A₀
    let : DiscreteTopology B₀ := discreteTopology_bot B₀
    obtain ⟨n, hn⟩ := nilpotent_small_carrier ell rA hA
    obtain ⟨m, hm⟩ := nilpotent_small_carrier ell rB hB
    let eA := finiteCoefficientCarrierIso A A₀ rA
    let eB := finiteCoefficientCarrierIso B B₀ rB
    let f := rB.toRingHom.comp (φ.comp rA.symm.toRingHom)
    have hsquare := (finiteCoefficientSmallCarrierComparison.2 A A₀ rA).2.2.1
      B B₀ rB eB (finiteCoefficientSmallCarrierComparison.2 B B₀ rB).1 φ a ha
    rw [comparisonMap_eq] at hsquare
    have heq : a = eA.hom ≫ scalarSixContinuousMap f continuous_of_discreteTopology ≫
        eB.inv := by
      rw [← Category.assoc, ← hsquare]
      simp
    rw [heq]
    exact IsListedScalarCoefficientMap.iso eA eB.symm
      (IsListedScalarCoefficientMap.finite n m hn hm f continuous_of_discreteTopology)
  · intro E F h a ha
    have heq : a = latticeIntegralMap ell h := by
      apply CommMon.hom_ext
      exact ha
    rw [heq]
    exact IsListedScalarCoefficientMap.integral h
  · intro E F h a ha
    have heq : a = (⟨⟨Profinite.padicSubfieldRingObjMap ell h⟩⟩ :
        scalarSixFieldRing ell E ⟶ scalarSixFieldRing ell F) := by
      apply CommMon.hom_ext
      exact ha
    rw [heq]
    exact IsListedScalarCoefficientMap.field h
  · intro E a ha
    have heq : a = scalarSixIntegralToField ell E := by
      apply CommMon.hom_ext
      exact ha
    rw [heq]
    exact IsListedScalarCoefficientMap.localization E
  · intro E a ha
    have heq : a = (⟨⟨Profinite.padicSubfieldRingObjToPadicAlgCl ell E⟩⟩ :
        scalarSixFieldRing ell E ⟶ latticeClosureRing ell) := by
      apply CommMon.hom_ext
      exact ha
    rw [heq]
    exact IsListedScalarCoefficientMap.algebraicClosure E
  · intro E A _ _ hA a ha
    let : TopologicalSpace A := ⊥
    let : DiscreteTopology A := discreteTopology_bot A
    obtain ⟨A₀, instA₀, finA₀, ⟨rA⟩⟩ := finiteCoefficientSmallCarrierComparison.1 A
    let := instA₀
    let := finA₀
    let : TopologicalSpace A₀ := ⊥
    let : DiscreteTopology A₀ := discreteTopology_bot A₀
    obtain ⟨n, hn⟩ := nilpotent_small_carrier ell rA hA
    obtain ⟨φ, hφ, hsection⟩ := ha
    let eA := finiteCoefficientCarrierIso A A₀ rA
    have hsquare := (finiteCoefficientSmallCarrierComparison.2 A A₀ rA).2.2.2
      (PadicAlgCl.integers ell E.1) φ hφ a hsection
    unfold finiteCoefficientComparisonMixedMap at hsquare
    rw [comparisonMap_eq] at hsquare
    have heq : a = scalarSixContinuousMap (rA.toRingHom.comp φ)
        ((continuous_of_discreteTopology (f := rA)).comp hφ) ≫ eA.inv := by
      rw [← hsquare]
      simp
    rw [heq]
    simpa using IsListedScalarCoefficientMap.iso (Iso.refl _) eA.symm
      (IsListedScalarCoefficientMap.integralFinite E n hn (rA.toRingHom.comp φ)
        ((continuous_of_discreteTopology (f := rA)).comp hφ))

end AlgebraicGeometry.ProEtale.CondensedRing
