module

public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution

import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Sheaf.Algebra.Homology.ProjectiveHomEvaluationModel
import Sheaf.CategoryTheory.DerivedCategory.BoundedFiniteTorPerfect
import Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import WeilConjectures.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.PointSectionsTorAmplitude
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr

/-! # Finite free models of finite-coefficient point sections

Source: main-20261015 blueprint, thm-pod-point-perfectness.proof.md, Step 1;
Stacks Project, Tags 07A4, 0658 and 0A66.
(blueprint: lem-sf-point-tor-amplitude-realization).

The coefficient lift is the size convention of pointFiniteFibre. Internal Hom in
D(A) is its existing derived closed internal Hom, the ordinary-module presentation
of derived internal Hom on the one-object ringed site. The signed model uses the
existing moduleHomComplex, rather than an independently chosen differential.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

open DerivedCategory

private theorem dual_coordinates (R : Type u) [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (M : ModuleCat.{u} R) :
    let A₀ := (CochainComplex.singleFunctor _ 0).obj M
    ∃ α : ∀ i : ℤ, (CochainComplex.moduleHomComplex P A₀).X i ≃ₗ[R]
        (P.X (-i) →ₗ[R] A₀.X 0),
      (∀ (i : ℤ) (f : (CochainComplex.moduleHomComplex P A₀).X i),
        α i f = (f.v (-i) 0 (neg_add_cancel i)).hom) ∧
      (∀ (i : ℤ) (f : (CochainComplex.moduleHomComplex P A₀).X i),
        α (i + 1) ((CochainComplex.moduleHomComplex P A₀).d i (i + 1) f) =
          (i + 1).negOnePow • (α i f).comp (P.d (-(i + 1)) (-i)).hom) := by
  classical
  let A₀ := (CochainComplex.singleFunctor _ 0).obj M
  let π (i : ℤ) : (CochainComplex.moduleHomComplex P A₀).X i →ₗ[R]
      (P.X (-i) →ₗ[R] A₀.X 0) :=
    { toFun := fun f ↦ (f.v (-i) 0 (neg_add_cancel i)).hom
      map_add' := fun f g ↦ rfl
      map_smul' := fun r f ↦ rfl }
  have hπ (i : ℤ) : Function.Bijective (π i) := by
    constructor
    · intro f g h
      apply CochainComplex.HomComplex.Cochain.ext
      intro p q hpq
      by_cases hq : q = 0
      · rcases hq with rfl
        have hp : p = -i := by omega
        rcases hp with rfl
        change (f.v (-i) 0 (neg_add_cancel i)).hom =
          (g.v (-i) 0 (neg_add_cancel i)).hom at h
        exact ModuleCat.hom_ext h
      · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M q hq).eq_of_tgt _ _
    · intro f
      refine ⟨CochainComplex.HomComplex.Cochain.single (ModuleCat.ofHom f) i, ?_⟩
      change ((CochainComplex.HomComplex.Cochain.single (ModuleCat.ofHom f) i).v
        (-i) 0 (neg_add_cancel i)).hom = f
      rw [CochainComplex.HomComplex.Cochain.single_v]
      rfl
  let α (i : ℤ) := LinearEquiv.ofBijective (π i) (hπ i)
  refine ⟨α, fun _ _ ↦ rfl, ?_⟩
  intro i f
  change ((CochainComplex.HomComplex.δ i (i + 1) f).v (-(i + 1)) 0
    (neg_add_cancel _)).hom = _
  rw [CochainComplex.HomComplex.δ_v i (i + 1) rfl f (-(i + 1)) 0
    (neg_add_cancel _) (-1) (-i) rfl (by omega)]
  simp only [CochainComplex.singleFunctor_obj_d, comp_zero, zero_add]
  rfl

private theorem finite_cohomology_of_model (R : Type u) [CommRing R] [Finite R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hzero : ∀ i : ℤ, i < a ∨ b < i → IsZero (P.X i))
    (hfinite : ∀ i : ℤ, Module.Finite R (P.X i))
    (C : DerivedCategory (ModuleCat.{u} R)) (e : C ≅ DerivedCategory.Q.obj P) :
    DerivedCategory.pointFiniteCohomology R C := by
  classical
  have : P.IsStrictlyGE a := (P.isStrictlyGE_iff a).2 (fun i hi ↦ hzero i (Or.inl hi))
  have : P.IsStrictlyLE b := (P.isStrictlyLE_iff b).2 (fun i hi ↦ hzero i (Or.inr hi))
  constructor
  · refine ⟨Finset.Icc a b, fun i hi ↦ ?_⟩
    have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        (DerivedCategory.Q.obj P)) := by
      have hout : i < a ∨ b < i := by simpa only [Finset.mem_Icc, not_and_or,
        not_le] using hi
      rcases hout with h | h
      · exact DerivedCategory.isZero_of_isGE (DerivedCategory.Q.obj P) a i h
      · exact DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj P) b i h
    exact hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso e)
  · intro i
    have := hfinite i
    have : Finite (P.X i) := Module.finite_of_finite R
    have : Finite (P.cycles i) := Finite.of_injective (P.iCycles i)
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
    have : Finite (P.homology i) := Finite.of_surjective (P.homologyπ i)
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)
    let h := (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app P
    exact Finite.of_equiv (P.homology i) h.toLinearEquiv.toEquiv.symm

private theorem perfect_of_free_model (R : Type u) [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (hzero : ∀ i : ℤ, i < a ∨ b < i → IsZero (P.X i))
    (hfree : ∀ i : ℤ, Module.Free R (P.X i) ∧ Module.Finite R (P.X i))
    (C : DerivedCategory (ModuleCat.{u} R)) (e : C ≅ DerivedCategory.Q.obj P) :
    DerivedCategory.IsPerfectRingComplex C := by
  refine ⟨P, a, b, ?_, ?_, fun i ↦ ?_, ⟨e⟩⟩
  · exact (P.isStrictlyGE_iff a).2 (fun i hi ↦ hzero i (Or.inl hi))
  · exact (P.isStrictlyLE_iff b).2 (fun i hi ↦ hzero i (Or.inr hi))
  · have := (hfree i).1
    exact ⟨inferInstance, (hfree i).2⟩

/-- Finite-coefficient point sections retain the specified Tor interval, admit a finite
free model in that interval, and have the signed dual model with the reversed interval.
The universally quantified C is identified with the recorded fibre; it is just the
notation C = Fib_s N in the source. The target A[0] in each internal Hom is the
ordinary module A concentrated in degree zero.

Source: main-20261015 blueprint, thm-pod-point-perfectness.proof.md, Step 1;
Stacks Project, Tags 07A4, 0658 and 0A66.
(blueprint: lem-sf-point-tor-amplitude-realization).

Proof:
1. The integer ring of E is a DVR with finite residue field. Its positive-power
quotient A is finite and local, and hence Noetherian: every ideal is generated by
its finite underlying set. Point-sections finiteness gives finite cohomology of C.
2. Test the sheaf Tor hypothesis against the constant sheaf of an arbitrary A-module
M, with no finiteness or flatness restriction. Its stalk at id_s is M; the ringed
point evaluation model identifies this stalk with final-object sections and compares
the derived tensor with C tensor M. Exact sections commute with cohomology, so the
sheaf vanishing gives ordinary-module Tor vanishing outside the same interval.
3. Finite cohomology and finite Tor amplitude first give some bounded finite-free
model Q. Apply the exact-interval finite-Tor perfectness theorem to Q, whose terms
are finite, over the Noetherian local ring A. This gives P supported in [a,b].
4. Free terms are projective. The bounded-above projective Hom evaluation model
computes RHom(C,A) by moduleHomComplex P A[0]. Projection onto the sole nonzero
target degree identifies degree i with Hom(P^(-i),A). Its differential is
(-1)^(i+1) times precomposition with d_P. A finite basis of P^(-i) gives the dual
basis, so this dual model is finite free and supported in [-b,-a].
5. The two bounded finite-free models give perfectness. Finite free terms are flat;
the bounded-flat tensor model against any module gives the dual Tor interval.
Over the finite ring A the dual terms, cycles and their quotients are finite sets,
so all dual cohomology is finite. Zero ranks and a=b are included.
-/
theorem point_tor_amplitude_realization
    (F : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (hn : 1 ≤ n) (a b : ℤ) (_hab : a ≤ b)
    (N : (intrinsicFiniteTorsionConstructible l E n hn (Spec (.of F.k))).FullSubcategory)
    (_hTor : HasProEtaleTorAmplitude (Spec (.of F.k))
      (Padic.coefficientExtensionRing l E n) N.obj a b) :
    ∀ C : DerivedCategory
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))),
      C = ((pointFiniteFibre F l hl E n hn).obj N).obj →
      DerivedCategory.pointFiniteCohomology
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) C ∧
        DerivedCategory.torAmplitudeIn
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) a b C ∧
        ∃ P : CochainComplex
            (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) ℤ,
          (∀ i : ℤ, i < a ∨ b < i → IsZero (P.X i)) ∧
          (∀ i : ℤ,
            Module.Free (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) (P.X i) ∧
            Module.Finite (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) (P.X i)) ∧
          Nonempty (C ≅ DerivedCategory.Q.obj P) ∧
          ∀ A₀ : CochainComplex
              (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) ℤ,
            A₀ = (CochainComplex.singleFunctor _ 0).obj
              (ModuleCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
                (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) →
            Nonempty ((ihom C).obj (DerivedCategory.Q.obj A₀) ≅
              DerivedCategory.Q.obj (CochainComplex.moduleHomComplex P A₀)) ∧
            (∃ α : ∀ i : ℤ,
                (CochainComplex.moduleHomComplex P A₀).X i ≃ₗ[
                  ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)]
                  (P.X (-i) →ₗ[ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)]
                    A₀.X 0),
              (∀ (i : ℤ) (f : (CochainComplex.moduleHomComplex P A₀).X i),
                α i f = (f.v (-i) 0 (neg_add_cancel i)).hom) ∧
              (∀ (i : ℤ) (f : (CochainComplex.moduleHomComplex P A₀).X i),
                α (i + 1) ((CochainComplex.moduleHomComplex P A₀).d i (i + 1) f) =
                  (i + 1).negOnePow • (α i f).comp (P.d (-(i + 1)) (-i)).hom)) ∧
            DerivedCategory.IsPerfectRingComplex C ∧
            DerivedCategory.IsPerfectRingComplex ((ihom C).obj (DerivedCategory.Q.obj A₀)) ∧
            DerivedCategory.pointFiniteCohomology
              (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
              ((ihom C).obj (DerivedCategory.Q.obj A₀)) ∧
            DerivedCategory.torAmplitudeIn
              (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))
              (-b) (-a) ((ihom C).obj (DerivedCategory.Q.obj A₀)) := by
  classical
  intro C hC
  have hfin : DerivedCategory.pointFiniteCohomology
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) C := by
    subst C
    exact ((pointFiniteFibre F l hl E n hn).obj N).property
  have : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  have hTor := point_sections_torAmplitude F (Padic.coefficientExtensionRing l E n) N.obj a b _hTor
  change DerivedCategory.torAmplitudeIn _ a b
    (((pointFiniteFibre F l hl E n hn).obj N).obj) at hTor
  rw [← hC] at hTor
  let R := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)
  have : Finite R := inferInstance
  have : IsNoetherianRing R := inferInstance
  have hdata := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have : IsLocalRing (Padic.coefficientExtensionIntegers l E) := hdata.2.2.2.1
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
  have : Nontrivial (Padic.coefficientExtensionRing l E n) :=
    Ideal.Quotient.nontrivial_iff.mpr hproper
  have : IsLocalRing (Padic.coefficientExtensionRing l E n) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n))
      Ideal.Quotient.mk_surjective
  have : IsLocalRing R := (ULift.ringEquiv.symm).isLocalRing
  have hconc := DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hTor
  have : C.IsLE b := hconc.2
  have hpc : DerivedCategory.IsPseudoCoherent.{u + 1, u + 1, u + 1} (A := R) C := by
    apply (isPseudoCoherent_iff_boundedAbove_finite_homology.{u + 1, 0, u + 1} R C).2
    refine ⟨⟨b, fun i hi ↦ DerivedCategory.isZero_of_isLE C b i hi⟩, fun i ↦ ?_⟩
    have := hfin.2 i
    infer_instance
  obtain ⟨Q, ⟨c, d, hQzero⟩, hQfin, _, ⟨eQ⟩⟩ :=
    DerivedCategory.isPerfect_of_pseudoCoherent_finiteTorAmplitude.{u + 1, u + 1} C hpc
      ⟨a, b, _hab, hTor⟩
  obtain ⟨P, hPzero, hPfree, ⟨eP⟩⟩ :=
    (DerivedCategory.exists_bounded_finite_projective_model_of_torAmplitudeIn R Q
      ⟨c, d, (Q.isStrictlyGE_iff c).2 (fun i hi ↦ hQzero i (Or.inl hi)),
        (Q.isStrictlyLE_iff d).2 (fun i hi ↦ hQzero i (Or.inr hi)), hQfin⟩ a b _hab
      ((DerivedCategory.torAmplitudeIn _ a b).prop_of_iso eQ.symm hTor)).2.2
      inferInstance
  let e : C ≅ DerivedCategory.Q.obj P := eQ.symm ≪≫ eP.symm
  refine ⟨hfin, hTor, P, hPzero, hPfree, ⟨e⟩, ?_⟩
  intro A₀ hA₀
  subst A₀
  let A₀ := (CochainComplex.singleFunctor (ModuleCat.{u + 1} R) 0).obj (ModuleCat.of R R)
  obtain ⟨α, hα, hdα⟩ := dual_coordinates R P (ModuleCat.of R R)
  have hproj (i : ℤ) : Module.Projective R (P.X i) := by
    have := (hPfree i).1
    infer_instance
  obtain ⟨_, _, _, _, δ, _⟩ := CochainComplex.projective_hom_evaluation_model R
  let eD : (ihom C).obj (DerivedCategory.Q.obj A₀) ≅
      DerivedCategory.Q.obj (CochainComplex.moduleHomComplex P A₀) :=
    (asIso ((MonoidalClosed.pre e.symm.hom).app _)) ≪≫
      (δ P ⟨b, fun i hi ↦ hPzero i (Or.inr hi)⟩ hproj A₀).symm
  let D := CochainComplex.moduleHomComplex P A₀
  let s : A₀.X 0 ≃ₗ[R] R :=
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)).toLinearEquiv
  let β (i : ℤ) : D.X i ≃ₗ[R] Module.Dual R (P.X (-i)) :=
    (α i).trans (LinearEquiv.congrRight s)
  have hDzero (i : ℤ) (hi : i < -b ∨ -a < i) : IsZero (D.X i) := by
    have : Subsingleton (P.X (-i)) :=
      ModuleCat.subsingleton_of_isZero (hPzero (-i) (by omega))
    exact ModuleCat.isZero_iff_subsingleton.2
      ((β i).toEquiv.injective.subsingleton)
  have hDfree (i : ℤ) : Module.Free R (D.X i) ∧ Module.Finite R (D.X i) := by
    have := (hPfree (-i)).1
    have := (hPfree (-i)).2
    exact ⟨Module.Free.of_equiv (β i).symm, Module.Finite.equiv (β i).symm⟩
  have : D.IsStrictlyGE (-b) := (D.isStrictlyGE_iff (-b)).2
    (fun i hi ↦ hDzero i (Or.inl hi))
  have : D.IsStrictlyLE (-a) := (D.isStrictlyLE_iff (-a)).2
    (fun i hi ↦ hDzero i (Or.inr hi))
  refine ⟨⟨eD⟩, ⟨α, hα, hdα⟩, perfect_of_free_model R P a b hPzero hPfree C e,
    perfect_of_free_model R D (-b) (-a) hDzero hDfree _ eD,
    finite_cohomology_of_model R D (-b) (-a) hDzero (fun i ↦ (hDfree i).2) _ eD, ?_⟩
  apply (DerivedCategory.torAmplitudeIn _ (-b) (-a)).prop_of_iso eD.symm
  apply DerivedCategory.torAmplitudeIn_Q_obj_of_flat D (-b) (-a)
  intro i
  have := (hDfree i).1
  exact (ModuleCat.flat_iff_flat _).2 inferInstance

end WeilConjectures
