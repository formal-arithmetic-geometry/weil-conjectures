/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution

import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.Module
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import WeilConjectures.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-!
# Finite Tor amplitude and perfectness over the finite coefficient ring

Source: blueprint `sec-smooth-purity/sk-prop-sf-trace-perfectness`, node
`lem-trf-finite-tor-amplitude-perfect`; Stacks Project, Tags 0652, 066E, 0658, and 00NZ.
(blueprint: lem-trf-finite-tor-amplitude-perfect).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- A bounded complex with finite cohomology over `A_{E,n}` has finite Tor amplitude
if and only if it is perfect, if and only if it has a bounded finite-free representative.
The Tor condition tests all ordinary modules in degree zero, with one ordered interval.

Source: blueprint `sec-smooth-purity/sk-prop-sf-trace-perfectness`, node
`lem-trf-finite-tor-amplitude-perfect`; Stacks Project, Tags 0652, 066E, 0658, 00NZ, and 064K
(blueprint: lem-trf-finite-tor-amplitude-perfect).

Proof plan:
1. The coefficient ring is finite and local. Its ideals are finite sets, hence finitely
   generated, so it is Noetherian (`def-weil-pbc-noetherian-ring`). The given finite
   cohomology is finitely generated (`def-weil-finitely-generated-module`), and boundedness
   provides an upper cohomology bound. No finiteness of the terms is required.
2. Apply `lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion` to obtain
   pseudo-coherence, hence a bounded-above finite-free model by
   `def-pc-ring-pseudo-coherent-complex`. Free modules are projective by
   `def-weil-pbc-projective-module`.
3. With finite Tor amplitude, `lem-pc-ring-pseudo-coherent-finite-tor-perfect` gives a
   bounded finite-projective model. This is precisely the perfect category in
   `def-trf-categorical-trace`, rendered by the shared `IsPerfectRingComplex` predicate.
4. For any perfect model, its finite-projective terms are flat by
   `lem-weil-pbc-projective-module-flat`, hence free over the local ring by
   `lem-weil-pbc-finite-flat-local-free`. Transport the differentials along finite-basis
   isomorphisms to obtain a bounded finite-free model representing the same object.
5. Such a bounded finite-free model is K-flat by `lem-pc-module-bounded-flat-kflat` and
   `def-pc-module-kflat-complex`. By `lem-pc-source-kflat-module-tensor-model`, tensoring
   with any ordinary module in degree zero computes derived tensor termwise. Its terms
   vanish outside the same interval, so the cohomology does too. For a zero model choose
   the interval `[0, 0]`; no flatness of the testing module is assumed.
6. A bounded finite-free model is also finite-projective, hence perfect. Combining these
   implications gives the two displayed equivalences, without identifying all bounded
   finite-cohomology objects with perfect ones. -/
theorem finiteTorAmplitude_iff_perfect_iff_finiteFree
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    [HasDerivedCategory.{w} (ModuleCat.{u} (Padic.coefficientExtensionRing l E n))]
    (C : DerivedCategory (ModuleCat.{u} (Padic.coefficientExtensionRing l E n)))
    (hbounded : TStructure.t.bounded C)
    (hfinite : ∀ i : ℤ,
      Module.Finite (Padic.coefficientExtensionRing l E n)
        ((homologyFunctor (ModuleCat.{u} (Padic.coefficientExtensionRing l E n)) i).obj C)) :
    ((∃ a b : ℤ, a ≤ b ∧
        torAmplitudeIn (ModuleCat.{u} (Padic.coefficientExtensionRing l E n)) a b C) ↔
      IsPerfectRingComplex C) ∧
    (IsPerfectRingComplex C ↔
      ∃ (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionRing l E n)) ℤ)
        (a b : ℤ),
        P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
          (∀ i : ℤ,
            Module.Free (Padic.coefficientExtensionRing l E n) (P.X i) ∧
            Module.Finite (Padic.coefficientExtensionRing l E n) (P.X i)) ∧
          Nonempty (C ≅ Q.obj P)) := by
  classical
  let R := Padic.coefficientExtensionRing l E n
  have : Finite R := Padic.finite_coefficientExtensionRing l E n hn
  have : IsNoetherianRing R := inferInstance
  have hdata := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have hlocal : IsLocalRing (Padic.coefficientExtensionIntegers l E) := hdata.2.2.2.1
  have hmax : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := hdata.2.2.2.2.1
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E :=
    hdata.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hproper : Padic.coefficientExtensionIdeal l E n ≠ ⊤ := by
    change Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) ^ n ≠ ⊤
    rw [hgen]
    intro htop
    have hle : Padic.coefficientExtensionMaximalIdeal l E ^ n ≤
        Padic.coefficientExtensionMaximalIdeal l E :=
      Ideal.pow_le_self (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
    exact hmax.ne_top (top_le_iff.mp (htop ▸ hle))
  have : Nontrivial R := Ideal.Quotient.nontrivial_iff.mpr hproper
  have : IsLocalRing R := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)) Ideal.Quotient.mk_surjective
  have hpc : IsPseudoCoherent C := by
    apply (isPseudoCoherent_iff_boundedAbove_finite_homology R C).2
    refine ⟨?_, hfinite⟩
    obtain ⟨b, hb⟩ := hbounded.2
    have : C.IsLE b := hb
    exact ⟨b, fun i hi ↦ isZero_of_isLE C b i hi⟩
  have hfree : IsPerfectRingComplex C ↔
      ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ),
        P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
          (∀ i : ℤ, Module.Free R (P.X i) ∧ Module.Finite R (P.X i)) ∧
          Nonempty (C ≅ Q.obj P) := by
    constructor
    · rintro ⟨P, a, b, ha, hb, hP, e⟩
      refine ⟨P, a, b, ha, hb, fun i ↦ ?_, e⟩
      have := (hP i).1
      have := (hP i).2
      exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩
    · rintro ⟨P, a, b, ha, hb, hP, e⟩
      refine ⟨P, a, b, ha, hb, fun i ↦ ?_, e⟩
      have := (hP i).1
      exact ⟨inferInstance, (hP i).2⟩
  refine ⟨⟨?_, ?_⟩, hfree⟩
  · intro hTor
    obtain ⟨P, ⟨a, b, hb⟩, hfin, hproj, ⟨e⟩⟩ :=
      isPerfect_of_pseudoCoherent_finiteTorAmplitude C hpc hTor
    refine ⟨P, a, b, ?_, ?_, fun i ↦ ⟨hproj i, hfin i⟩, ⟨e.symm⟩⟩
    · exact (P.isStrictlyGE_iff a).2 (fun i hi ↦ hb i (Or.inl hi))
    · exact (P.isStrictlyLE_iff b).2 (fun i hi ↦ hb i (Or.inr hi))
  · intro hperfect
    obtain ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩ := hperfect
    have hflat (i : ℤ) : ObjectProperty.flat (P.X i) := by
      have := (hP i).1
      exact (ModuleCat.flat_iff_flat _).2 inferInstance
    refine ⟨min a b, b, min_le_right _ _, ?_⟩
    exact (torAmplitudeIn _ (min a b) b).prop_of_iso e.symm
      ((torAmplitudeIn_Q_obj_of_flat P a b hflat).mono (min_le_left _ _) le_rfl)

end DerivedCategory
