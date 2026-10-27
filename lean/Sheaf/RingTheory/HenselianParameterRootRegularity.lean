/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.RingTheory.PthRootAlgebraLocal
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.FiniteLocalHenselian

/-! # Henselian regular parameter-root algebras

Source: ILO, Travaux de Gabber, IX Proposition 2.1(i), proof, printed p.133;
Stacks Tags 04GG, 04GH, 00GK, 00FN, 00OK, 00KU, 00NP.
(blueprint: lem-sfb-henselian-parameter-root-regularity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

namespace Algebra

/-- The class of the specified variable in the existing simultaneous root quotient.
The definition `pthRootAlgebra` accepts every natural exponent, not just primes.
Source: ILO IX Proposition 2.1(i), proof, p.133
(blueprint: lem-sfb-henselian-parameter-root-regularity). -/
def parameterRootCoordinate {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) (i : Fin r) : pthRootAlgebra n r R t :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

-- Normal form: X^e maps to (∏ tᵢ^(eᵢ/n)) times the basis vector at (eᵢ mod n).
private def rootRemainder {r n : ℕ} (hn : 0 < n) (e : Fin r →₀ ℕ) : Fin r → Fin n :=
  fun i ↦ ⟨e i % n, Nat.mod_lt _ hn⟩

private def rootFactor {R : Type u} [CommRing R] {r : ℕ} (t : Fin r → R)
    (n : ℕ) (e : Fin r →₀ ℕ) : R := ∏ i, t i ^ (e i / n)

private def rootNormalForm {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) (hn : 0 < n) :
    MvPolynomial (Fin r) R →ₗ[R] ((Fin r → Fin n) →₀ R) :=
  (Finsupp.lsum R fun e ↦
    LinearMap.smulRight (LinearMap.id : R →ₗ[R] R)
      (Finsupp.single (rootRemainder hn e) (rootFactor t n e))).comp
        (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

private theorem rootNormalForm_monomial {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) (hn : 0 < n) (e : Fin r →₀ ℕ) (c : R) :
    rootNormalForm t hn (MvPolynomial.monomial e c) =
      Finsupp.single (rootRemainder hn e) (c * rootFactor t n e) := by
  simp [rootNormalForm, MvPolynomial.monomial,
    Finsupp.smul_single, smul_eq_mul]

private theorem rootRemainder_shift {r n : ℕ} (hn : 0 < n)
    (e : Fin r →₀ ℕ) (i : Fin r) :
    rootRemainder hn (e + Finsupp.single i n) = rootRemainder hn e := by
  ext j
  by_cases h : i = j
  · subst j
    simp [rootRemainder]
  · simp [rootRemainder, Ne.symm h]

private theorem rootFactor_shift {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) (hn : 0 < n) (e : Fin r →₀ ℕ) (i : Fin r) :
    rootFactor t n (e + Finsupp.single i n) = rootFactor t n e * t i := by
  classical
  simp only [rootFactor]
  rw [show t i = ∏ j : Fin r, if i = j then t j else 1 by simp,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : i = j
  · subst j
    simp [Nat.add_div_right _ hn, pow_succ]
  · simp [h]

private theorem rootNormalForm_relation {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) (hn : 0 < n) (f : MvPolynomial (Fin r) R) (i : Fin r) :
    rootNormalForm t hn (f * (MvPolynomial.X i ^ n - MvPolynomial.C (t i))) = 0 := by
  classical
  rw [f.as_sum, Finset.sum_mul, map_sum]
  apply Finset.sum_eq_zero
  intro e _
  rw [mul_sub, map_sub, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul,
    show MvPolynomial.monomial e (MvPolynomial.coeff e f) * MvPolynomial.C (t i) =
      MvPolynomial.monomial e (t i * MvPolynomial.coeff e f) by
        rw [mul_comm, MvPolynomial.C_mul_monomial],
    mul_one, rootNormalForm_monomial,
    rootNormalForm_monomial, rootRemainder_shift hn, rootFactor_shift t hn]
  simp [mul_assoc, mul_comm, mul_left_comm]

-- Vanishing on all polynomial multiples gives vanishing on the relation ideal.
private theorem rootNormalForm_kills {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) (hn : 0 < n) :
    ∀ f ∈ Ideal.span (Set.range (fun i : Fin r ↦
      (MvPolynomial.X i : MvPolynomial (Fin r) R) ^ n - MvPolynomial.C (t i))),
      rootNormalForm t hn f = 0 := by
  intro f hf
  have H : ∀ a : MvPolynomial (Fin r) R, rootNormalForm t hn (a * f) = 0 := by
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact fun a ↦ rootNormalForm_relation t hn a i
    | zero => simp
    | add x y _ _ hx hy => simp [mul_add, hx, hy]
    | smul a x _ hx => simpa [smul_eq_mul, ← mul_assoc] using fun b ↦ hx (b * a)
  simpa using H 1

/-- The specified root satisfies its defining power relation.
Source: ILO IX Proposition 2.1(i), proof, p.133; polynomial quotient relations.
(blueprint: lem-sfb-henselian-parameter-root-regularity). -/
theorem rootCoordinate_pow {R : Type u} [CommRing R] {r : ℕ}
    (t : Fin r → R) (n : ℕ) (i : Fin r) :
    parameterRootCoordinate t n i ^ n = algebraMap R _ (t i) := by
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩ :
    (MvPolynomial.X i : MvPolynomial (Fin r) R) ^ n - MvPolynomial.C (t i) ∈
      Ideal.span (Set.range (fun j : Fin r ↦ MvPolynomial.X j ^ n - MvPolynomial.C (t j))))
  change parameterRootCoordinate t n i ^ n - algebraMap R _ (t i) = 0 at h
  exact sub_eq_zero.mp h

private theorem rootMonomial_reduce {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) (hn : 0 < n) (e : Fin r →₀ ℕ) (c : R) :
    (Ideal.Quotient.mk _ (MvPolynomial.monomial e c) : pthRootAlgebra n r R t) =
      (c * rootFactor t n e) •
        ∏ i, parameterRootCoordinate t n i ^ (rootRemainder hn e i).val := by
  classical
  let q : MvPolynomial (Fin r) R →+* pthRootAlgebra n r R t := Ideal.Quotient.mk _
  change q (MvPolynomial.monomial e c) = _
  rw [MvPolynomial.monomial_eq, map_mul]
  change algebraMap R _ c * q (∏ i ∈ e.support, MvPolynomial.X i ^ e i) = _
  rw [map_prod]
  have hall : (∏ i ∈ e.support, q (MvPolynomial.X i ^ e i)) =
      ∏ i : Fin r, q (MvPolynomial.X i ^ e i) := by
    apply Finset.prod_subset (Finset.subset_univ _)
    intro i _ hi
    simp [Finsupp.notMem_support_iff.mp hi]
  rw [hall]
  simp only [map_pow]
  have hred (i : Fin r) : q (MvPolynomial.X i) ^ e i =
      algebraMap R _ (t i ^ (e i / n)) * q (MvPolynomial.X i) ^ (e i % n) := by
    conv_lhs => rw [← Nat.div_add_mod (e i) n]
    rw [pow_add, pow_mul, show q (MvPolynomial.X i) ^ n = algebraMap R _ (t i) from
      rootCoordinate_pow t n i, ← map_pow]
  simp_rw [hred]
  rw [Finset.prod_mul_distrib, ← map_prod]
  simp only [Algebra.smul_def, map_mul, rootFactor, rootRemainder,
    parameterRootCoordinate, q, mul_assoc]

private theorem rootNormalForm_bounded {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) (hn : 0 < n) (a : Fin r → Fin n) :
    rootNormalForm t hn (∏ i : Fin r, MvPolynomial.X i ^ (a i).val) =
      Finsupp.single a 1 := by
  classical
  let e : Fin r →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i ↦ (a i).val)
  have he (i : Fin r) : e i = (a i).val := by simp [e]
  have hp : (∏ i : Fin r, (MvPolynomial.X i : MvPolynomial (Fin r) R) ^ (a i).val) =
      MvPolynomial.monomial e 1 := by
    rw [← MvPolynomial.prod_X_pow_eq_monomial]
    symm
    apply Finset.prod_subset (Finset.subset_univ _)
    intro i _ hi
    simp [Finsupp.notMem_support_iff.mp hi]
  rw [hp, rootNormalForm_monomial]
  have hr : rootRemainder hn e = a := by
    ext i
    simp [rootRemainder, he, Nat.mod_eq_of_lt (a i).isLt]
  simp [hr, rootFactor, he, Nat.div_eq_of_lt (a _).isLt]

-- The quotient normal form is a left inverse on the bounded monomials.
/-- The bounded root monomials form a basis over any commutative coefficient ring.
Source: ILO IX Proposition 2.1(i), proof, p.133; polynomial quotient relations.
(blueprint: lem-sfb-henselian-parameter-root-regularity). -/
theorem root_basis {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) (hn : 0 < n) :
    ∃ b : Module.Basis (Fin r → Fin n) R (pthRootAlgebra n r R t),
      ∀ a, b a = ∏ i, parameterRootCoordinate t n i ^ (a i).val := by
  classical
  let B := pthRootAlgebra n r R t
  let m : (Fin r → Fin n) → B := fun a ↦ ∏ i, parameterRootCoordinate t n i ^ (a i).val
  let I : Ideal (MvPolynomial (Fin r) R) := Ideal.span (Set.range (fun i : Fin r ↦
    MvPolynomial.X i ^ n - MvPolynomial.C (t i)))
  let ρ : B →ₗ[R] ((Fin r → Fin n) →₀ R) :=
    (I.restrictScalars R).liftQ (rootNormalForm t hn) (rootNormalForm_kills t hn)
  have hρ (a : Fin r → Fin n) : ρ (m a) = Finsupp.single a 1 := by
    change ρ (∏ i, Ideal.Quotient.mk I (MvPolynomial.X i) ^ (a i).val) = _
    simp_rw [← map_pow]
    rw [← map_prod]
    exact rootNormalForm_bounded t hn a
  have hli : LinearIndependent R m := by
    apply LinearIndependent.of_comp ρ
    simpa only [Function.comp_def, hρ, Finsupp.coe_basisSingleOne] using
      (Finsupp.basisSingleOne : Module.Basis (Fin r → Fin n) R _).linearIndependent
  have hspan : ⊤ ≤ Submodule.span R (Set.range m) := by
    intro x _
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [f.as_sum, map_sum]
    apply Submodule.sum_mem
    intro e _
    rw [rootMonomial_reduce t hn]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨rootRemainder hn e, rfl⟩)
  exact ⟨Module.Basis.mk hli hspan, fun a ↦ Module.Basis.mk_apply _ _ a⟩

private theorem rootAlgebraMap_injective {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) (hn : 0 < n) :
    Function.Injective (algebraMap R (pthRootAlgebra n r R t)) := by
  obtain ⟨b, hb⟩ := root_basis t hn
  let z : Fin r → Fin n := fun _ ↦ ⟨0, hn⟩
  have hz : b z = 1 := by simp [hb, z]
  intro x y h
  have h' : x • b z = y • b z := by simpa [hz, Algebra.smul_def] using h
  have hh := congrArg (fun v ↦ b.repr v z) h'
  simpa using hh

private theorem root_algebra_noVariables {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) (hn : 0 < n) (hr : r = 0) :
    Function.Bijective (algebraMap R (pthRootAlgebra n r R t)) := by
  refine ⟨rootAlgebraMap_injective t hn, ?_⟩
  subst r
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨MvPolynomial.constantCoeff f, ?_⟩
  have hf : MvPolynomial.C (MvPolynomial.constantCoeff f) = f := by
    exact (MvPolynomial.eq_C_of_isEmpty f).symm
  change Ideal.Quotient.mk _ (MvPolynomial.C (MvPolynomial.constantCoeff f)) = _
  rw [hf]

/-- Evaluate the simultaneous root quotient at a family satisfying the power relations.
Source: ILO IX Proposition 2.1(i), proof, p.133; polynomial quotient relations.
(blueprint: lem-sfb-henselian-parameter-root-regularity). -/
def rootEval {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) {S : Type u} [CommRing S] (f : R →+* S)
    (x : Fin r → S) (hx : ∀ i, x i ^ n = f (t i)) :
    pthRootAlgebra n r R t →+* S :=
  Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom f x) (by
    change Ideal.span _ ≤ RingHom.ker (MvPolynomial.eval₂Hom f x)
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change MvPolynomial.eval₂Hom f x _ = 0
    simp only [map_sub, map_pow,
      MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C, sub_eq_zero]
    exact hx i)

/-- Root evaluation restricts to the prescribed map on coefficients.
Source: ILO IX Proposition 2.1(i), proof, p.133; polynomial quotient relations.
(blueprint: lem-sfb-henselian-parameter-root-regularity). -/
theorem rootEval_scalar {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) {S : Type u} [CommRing S] (f : R →+* S)
    (x : Fin r → S) (hx : ∀ i, x i ^ n = f (t i)) (a : R) :
    rootEval t f x hx (algebraMap R _ a) = f a := by
  change MvPolynomial.eval₂Hom f x (MvPolynomial.C a) = f a
  simp

/-- Root evaluation takes each specified coordinate to its prescribed value.
Source: ILO IX Proposition 2.1(i), proof, p.133; polynomial quotient relations.
(blueprint: lem-sfb-henselian-parameter-root-regularity). -/
theorem rootEval_coordinate {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) {S : Type u} [CommRing S] (f : R →+* S)
    (x : Fin r → S) (hx : ∀ i, x i ^ n = f (t i)) (i : Fin r) :
    rootEval t f x hx (parameterRootCoordinate t n i) = x i := by
  change MvPolynomial.eval₂Hom f x (MvPolynomial.X i) = x i
  simp

private theorem root_quotient_scalar_surjective {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) (J : Ideal (pthRootAlgebra n r R t))
    (hx : ∀ i, parameterRootCoordinate t n i ∈ J) :
    Function.Surjective ((Ideal.Quotient.mk J).comp (algebraMap R _)) := by
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨a, rfl⟩
  | add f g hf hg =>
    obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hg
    refine ⟨a + b, ?_⟩
    simpa only [map_add] using congrArg₂ (· + ·) ha hb
  | mul_X f i hf =>
    refine ⟨0, ?_⟩
    simp only [map_zero, map_mul]
    rw [show Ideal.Quotient.mk J (Ideal.Quotient.mk _ (MvPolynomial.X i)) = 0 from
      Ideal.Quotient.eq_zero_iff_mem.mpr (hx i), mul_zero]

private theorem root_local {R : Type u} [CommRing R] [IsLocalRing R] {r n : ℕ}
    (t : Fin r → R) (ht : ∀ i, t i ∈ IsLocalRing.maximalIdeal R) (hn : 0 < n)
    [Module.Finite R (pthRootAlgebra n r R t)] :
    ∃ _hlocal : IsLocalRing (pthRootAlgebra n r R t),
      IsLocalRing.maximalIdeal (pthRootAlgebra n r R t) =
        (IsLocalRing.maximalIdeal R).map (algebraMap R _) ⊔
          Ideal.span (Set.range (parameterRootCoordinate t n)) := by
  classical
  let B := pthRootAlgebra n r R t
  let J : Ideal B := (IsLocalRing.maximalIdeal R).map (algebraMap R _) ⊔
    Ideal.span (Set.range (parameterRootCoordinate t n))
  let g : B →+* IsLocalRing.ResidueField R :=
    rootEval t (IsLocalRing.residue R) (fun _ ↦ 0) (fun i ↦ by
      rw [zero_pow hn.ne']
      exact (Ideal.Quotient.eq_zero_iff_mem.mpr (ht i)).symm)
  have hg (a : R) : g (algebraMap R B a) = IsLocalRing.residue R a :=
    rootEval_scalar ..
  have hgx (i : Fin r) : g (parameterRootCoordinate t n i) = 0 :=
    rootEval_coordinate ..
  have hgs : Function.Surjective g := by
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨algebraMap R B a, hg a⟩
  have hJker : J ≤ RingHom.ker g := by
    apply sup_le
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      change g (algebraMap R B a) = 0
      rw [hg]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
    · apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hgx i
  have hxJ (i : Fin r) : parameterRootCoordinate t n i ∈ J :=
    (le_sup_right : Ideal.span _ ≤ J) (Ideal.subset_span ⟨i, rfl⟩)
  have hkerJ : RingHom.ker g ≤ J := by
    intro z hz
    obtain ⟨a, ha⟩ := root_quotient_scalar_surjective t J hxJ (Ideal.Quotient.mk J z)
    have hza : z - algebraMap R B a ∈ J := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [map_sub, sub_eq_zero, RingHom.comp_apply] using ha.symm
    have hga : g (algebraMap R B a) = 0 := by
      have h := hJker hza
      change g (z - algebraMap R B a) = 0 at h
      change g z = 0 at hz
      simpa [map_sub, hz] using h
    have ham : a ∈ IsLocalRing.maximalIdeal R :=
      Ideal.Quotient.eq_zero_iff_mem.mp ((hg a).symm.trans hga)
    have haJ : algebraMap R B a ∈ J :=
      (le_sup_left : (IsLocalRing.maximalIdeal R).map (algebraMap R B) ≤ J)
        (Ideal.mem_map_of_mem _ ham)
    simpa using J.add_mem hza haJ
  have hJ : J.IsMaximal := by
    rw [le_antisymm hJker hkerJ]
    exact RingHom.ker_isMaximal_of_surjective g hgs
  have huniq (M : Ideal B) (hM : M.IsMaximal) : M = J := by
    have : M.IsMaximal := hM
    have hc : M.comap (algebraMap R B) = IsLocalRing.maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M)
    have hm : (IsLocalRing.maximalIdeal R).map (algebraMap R B) ≤ M := by
      rw [Ideal.map_le_iff_le_comap, hc]
    have hx (i : Fin r) : parameterRootCoordinate t n i ∈ M := by
      apply Ideal.IsPrime.mem_of_pow_mem (inferInstance : M.IsPrime) n
      rw [rootCoordinate_pow]
      exact hm (Ideal.mem_map_of_mem _ (ht i))
    have hJM : J ≤ M := sup_le hm (Ideal.span_le.mpr (by
      rintro _ ⟨i, rfl⟩
      exact hx i))
    exact (hJ.eq_of_le hM.ne_top hJM).symm
  have hl : IsLocalRing B := IsLocalRing.of_unique_max_ideal ⟨J, hJ, huniq⟩
  exact ⟨hl, (IsLocalRing.eq_maximalIdeal hJ).symm⟩

private theorem root_residue_equiv {R : Type u} [CommRing R] [IsLocalRing R]
    {r n : ℕ} (t : Fin r → R) [IsLocalRing (pthRootAlgebra n r R t)]
    (hm : IsLocalRing.maximalIdeal (pthRootAlgebra n r R t) =
      (IsLocalRing.maximalIdeal R).map (algebraMap R _) ⊔
        Ideal.span (Set.range (parameterRootCoordinate t n))) :
    ∃ e : IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField (pthRootAlgebra n r R t),
      ∀ a : R, e (IsLocalRing.residue R a) = IsLocalRing.residue _ (algebraMap R _ a) := by
  let B := pthRootAlgebra n r R t
  let f : R →+* IsLocalRing.ResidueField B :=
    (IsLocalRing.residue B).comp (algebraMap R B)
  have hf : ∀ a ∈ IsLocalRing.maximalIdeal R, f a = 0 := by
    intro a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [hm]
    exact (le_sup_left : (IsLocalRing.maximalIdeal R).map (algebraMap R B) ≤ _)
      (Ideal.mem_map_of_mem _ ha)
  let g : IsLocalRing.ResidueField R →+* IsLocalRing.ResidueField B :=
    Ideal.Quotient.lift _ f hf
  have hsurj : Function.Surjective f := root_quotient_scalar_surjective t _ (by
    intro i
    rw [hm]
    exact (le_sup_right :
      Ideal.span (Set.range (parameterRootCoordinate t n)) ≤ _) (Ideal.subset_span ⟨i, rfl⟩))
  have hgs : Function.Surjective g := by
    intro x
    obtain ⟨a, rfl⟩ := hsurj x
    exact ⟨IsLocalRing.residue R a, rfl⟩
  exact ⟨RingEquiv.ofBijective g ⟨RingHom.injective g, hgs⟩, fun _ ↦ rfl⟩

/-- Maps from the root quotient agree if they agree on coefficients and coordinates.
Source: ILO IX Proposition 2.1(i), proof, p.133; polynomial quotient relations.
(blueprint: lem-sfb-henselian-parameter-root-regularity). -/
theorem rootHom_ext {R : Type u} [CommRing R] {r n : ℕ}
    (t : Fin r → R) {S : Type u} [CommRing S]
    (f g : pthRootAlgebra n r R t →+* S)
    (hc : ∀ a : R, f (algebraMap R _ a) = g (algebraMap R _ a))
    (hx : ∀ i, f (parameterRootCoordinate t n i) = g (parameterRootCoordinate t n i)) :
    f = g := by
  apply Ideal.Quotient.ringHom_ext
  exact MvPolynomial.ringHom_ext hc hx

private theorem root_closed_fibre {R : Type u} [CommRing R] [IsLocalRing R] {r n : ℕ}
    (t : Fin r → R) (ht : ∀ i, t i ∈ IsLocalRing.maximalIdeal R) (_hn : 0 < n) :
    ∃ e : (pthRootAlgebra n r R t ⧸
        (IsLocalRing.maximalIdeal R).map (algebraMap R _)) ≃ₐ[R]
        pthRootAlgebra n r (IsLocalRing.ResidueField R) (fun _ ↦ 0),
      ∀ i, e (Ideal.Quotient.mk _ (parameterRootCoordinate t n i)) =
        parameterRootCoordinate (fun _ : Fin r ↦ (0 : IsLocalRing.ResidueField R)) n i := by
  let B := pthRootAlgebra n r R t
  let k := IsLocalRing.ResidueField R
  let C := pthRootAlgebra n r k (fun _ ↦ 0)
  let J := (IsLocalRing.maximalIdeal R).map (algebraMap R B)
  let F := B ⧸ J
  let q : B →+* F := Ideal.Quotient.mk J
  let c : R →+* F := q.comp (algebraMap R B)
  have hc : ∀ a ∈ IsLocalRing.maximalIdeal R, c a = 0 := by
    intro a ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha)
  let ck : k →+* F := Ideal.Quotient.lift _ c hc
  have hck (a : R) : ck (IsLocalRing.residue R a) = c a := rfl
  let f : B →+* C := rootEval t ((algebraMap k C).comp (IsLocalRing.residue R))
    (parameterRootCoordinate (fun _ : Fin r ↦ (0 : k)) n) (fun i ↦ by
      rw [rootCoordinate_pow, map_zero, RingHom.comp_apply,
        show IsLocalRing.residue R (t i) = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr (ht i),
        map_zero])
  have hf (a : R) : f (algebraMap R B a) = algebraMap k C (IsLocalRing.residue R a) :=
    rootEval_scalar ..
  have hfx (i : Fin r) : f (parameterRootCoordinate t n i) =
      parameterRootCoordinate (fun _ : Fin r ↦ (0 : k)) n i := rootEval_coordinate ..
  have hfJ : ∀ a ∈ J, f a = 0 := by
    change J ≤ RingHom.ker f
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change f (algebraMap R B a) = 0
    rw [hf, show IsLocalRing.residue R a = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr ha,
      map_zero]
  let g : F →+* C := Ideal.Quotient.lift J f hfJ
  have hgq (a : B) : g (q a) = f a := rfl
  have hqx (i : Fin r) : q (parameterRootCoordinate t n i) ^ n = ck 0 := by
    rw [← map_pow, rootCoordinate_pow, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ (ht i))
  let h : C →+* F := rootEval (fun _ : Fin r ↦ (0 : k)) ck
    (fun i ↦ q (parameterRootCoordinate t n i)) hqx
  have hhc (a : k) : h (algebraMap k C a) = ck a := rootEval_scalar ..
  have hhx (i : Fin r) : h (parameterRootCoordinate (fun _ : Fin r ↦ (0 : k)) n i) =
      q (parameterRootCoordinate t n i) := rootEval_coordinate ..
  have hgh : g.comp h = RingHom.id C := by
    apply rootHom_ext (fun _ : Fin r ↦ (0 : k))
    · intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      change g (h (algebraMap k C (IsLocalRing.residue R a))) = _
      rw [hhc, hck]
      exact hf a
    · intro i
      change g (h (parameterRootCoordinate (fun _ : Fin r ↦ (0 : k)) n i)) = _
      rw [hhx, hgq, hfx]
      rfl
  have hhg : h.comp g = RingHom.id F := by
    apply Ideal.Quotient.ringHom_ext
    apply rootHom_ext t
    · intro a
      change h (g (q (algebraMap R B a))) = q (algebraMap R B a)
      rw [hgq, hf, hhc, hck]
      rfl
    · intro i
      change h (g (q (parameterRootCoordinate t n i))) = q (parameterRootCoordinate t n i)
      rw [hgq, hfx, hhx]
  let e : F ≃+* C := RingEquiv.ofRingHom g h hgh hhg
  have he (a : R) : e (algebraMap R F a) = algebraMap R C a := hf a
  exact ⟨AlgEquiv.ofRingEquiv he, hfx⟩

private theorem root_parameter_span {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (d : ℕ) (t : Fin d → R)
    (ht : IsLocalRing.IsRegularSystemOfParameters (List.ofFn t))
    (r : ℕ) (hr : r ≤ d) (n : ℕ) (hn : 0 < n) :
    Ideal.span {x | x ∈ List.ofFn (parameterRootCoordinate (t ∘ Fin.castLE hr) n) ++
      ((List.ofFn t).drop r).map (algebraMap R _)} =
      (IsLocalRing.maximalIdeal R).map (algebraMap R _) ⊔
        Ideal.span (Set.range (parameterRootCoordinate (t ∘ Fin.castLE hr) n)) := by
  classical
  let B := pthRootAlgebra n r R (t ∘ Fin.castLE hr)
  let x := parameterRootCoordinate (t ∘ Fin.castLE hr) n
  let l := List.ofFn x ++ ((List.ofFn t).drop r).map (algebraMap R B)
  let J : Ideal B := (IsLocalRing.maximalIdeal R).map (algebraMap R B) ⊔
    Ideal.span (Set.range x)
  have hti (i : Fin d) : t i ∈ IsLocalRing.maximalIdeal R := by
    rw [← ht.1]
    exact Ideal.subset_span (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hx (i : Fin r) : x i ∈ Ideal.span {y | y ∈ l} :=
    Ideal.subset_span (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
  have hrest (i : Fin d) (hi : r ≤ i.val) :
      algebraMap R B (t i) ∈ Ideal.span {y | y ∈ l} := by
    apply Ideal.subset_span
    apply List.mem_append_right
    apply List.mem_map.mpr
    refine ⟨t i, ?_, rfl⟩
    rw [List.mem_iff_getElem]
    refine ⟨i.val - r, by simp; omega, ?_⟩
    simp [Nat.add_sub_of_le hi]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
      exact (le_sup_right : Ideal.span (Set.range x) ≤ J) (Ideal.subset_span ⟨i, rfl⟩)
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
      have ha' : a ∈ IsLocalRing.maximalIdeal R := by
        rw [← ht.1]
        exact Ideal.subset_span (List.mem_of_mem_drop ha)
      exact (le_sup_left : (IsLocalRing.maximalIdeal R).map (algebraMap R B) ≤ J)
        (Ideal.mem_map_of_mem _ ha')
  · apply sup_le
    · rw [← ht.1, Ideal.map_span]
      apply Ideal.span_le.mpr
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      by_cases hi : i.val < r
      · let j : Fin r := ⟨i.val, hi⟩
        have hj : Fin.castLE hr j = i := Fin.ext rfl
        have hp : x j ^ n = algebraMap R B (t i) := by
          simpa only [x, Function.comp_apply, hj] using
            rootCoordinate_pow (t ∘ Fin.castLE hr) n j
        rw [← hp]
        exact Ideal.pow_mem_of_mem _ (hx j) n hn
      · exact hrest i (Nat.le_of_not_gt hi)
    · apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hx i

private theorem regular_of_parameters {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (l : List R)
    (hl : Ideal.span {x | x ∈ l} = IsLocalRing.maximalIdeal R)
    (hd : (l.length : WithBot ℕ∞) = ringKrullDim R) : IsRegularLocalRing R := by
  classical
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [← hl, ← hd]
  have hs : (Ideal.span {x | x ∈ l}).spanFinrank ≤ l.toFinset.card := by
    have h := Submodule.spanFinrank_span_le_ncard_of_finite (R := R) l.finite_toSet
    have hc : {x | x ∈ l}.ncard = l.toFinset.card := by
      rw [← List.coe_toFinset, Set.ncard_coe_finset]
    rw [hc] at h
    exact h
  exact_mod_cast hs.trans l.toFinset_card_le

/-- Adjoining roots of the first parameters preserves henselian regular locality,
with the displayed monomial basis, closed fibre, residue map, and new parameters.
Source: ILO IX Proposition 2.1(i), proof, printed p.133; the arbitrary-exponent
algebra argument uses Stacks Tags 04GG, 04GH, 00GK, 00FN, 00OK, 00KU, 00NP.
(blueprint: lem-sfb-henselian-parameter-root-regularity).

Proof: (1) For an exponent vector e, write e_i = n q_i + a_i with a_i < n.
Send the monomial c X^e to the coefficient c ∏ t_i^q_i at index a. This R-linear
normal form kills every polynomial multiple of X_i^n-t_i, since adding n to e_i
preserves a_i and multiplies the coefficient by t_i. It therefore descends to B.
The quotient relations express every polynomial class as a sum of bounded
monomials. The normal form sends each such monomial to its distinct coordinate
vector, proving linear independence and the displayed basis. The basis vector
at zero is 1, so its coordinate detects scalars and proves injectivity.
(2) The finite basis gives module finiteness, hence integrality and Noetherianity.
(3) Put J=mB+(x_i). Evaluation at zero into k is surjective, kills J, and has
kernel exactly J: modulo J every class is a scalar, and a scalar vanishes in k
exactly when it lies in m. Thus J is maximal. Every maximal ideal of B contracts
to m by integrality, so contains mB; primality and x_i^n=t_i imply that it also
contains every x_i. Hence J is the unique maximal ideal, proving locality.
(4) The quotient B/J is generated by scalars, so the induced field map k→B/J
is surjective and therefore an isomorphism. Evaluation in both directions,
first reducing coefficients modulo m and then descending the coefficient map
k→B/mB, identifies B/mB with k[X_i]/(X_i^n), fixing all root coordinates.
(5) Integral injectivity gives dim B=dim R=d. Substitute t_i=x_i^n in the
original maximal-ideal generators. The resulting list of x_i and the remaining
t_i generates J and has length d. Its spanFinrank is at most its length, so the
regular-local criterion proves regularity and the displayed parameter system.
(6) Regular local rings are domains. Finite local algebras over henselian rings
are henselian. Pull separable polynomials back along the residue isomorphism,
split them over k, and transport the splitting to prove strict henselianity.
When r=0, every polynomial is constant, proving that the coefficient map is
bijective. The argument uses neither division by n nor roots of unity. -/
theorem henselian_parameter_root_regularity
    (R : Type u) [CommRing R] [HenselianLocalRing R] [IsRegularLocalRing R]
    (d : ℕ) (t : Fin d → R)
    (ht : IsLocalRing.IsRegularSystemOfParameters (List.ofFn t))
    (r : ℕ) (hr : r ≤ d) (n : ℕ) (hn : 0 < n) :
    ∃ b : Module.Basis (Fin r → Fin n) R (pthRootAlgebra n r R (t ∘ Fin.castLE hr)),
      (∀ a, b a = ∏ i, parameterRootCoordinate (t ∘ Fin.castLE hr) n i ^ (a i).val) ∧
      Module.Finite R (pthRootAlgebra n r R (t ∘ Fin.castLE hr)) ∧
      Function.Injective (algebraMap R (pthRootAlgebra n r R (t ∘ Fin.castLE hr))) ∧
      Algebra.IsIntegral R (pthRootAlgebra n r R (t ∘ Fin.castLE hr)) ∧
      ∃ (_hreg : IsRegularLocalRing (pthRootAlgebra n r R (t ∘ Fin.castLE hr)))
        (_hhen : HenselianLocalRing (pthRootAlgebra n r R (t ∘ Fin.castLE hr))),
        IsDomain (pthRootAlgebra n r R (t ∘ Fin.castLE hr)) ∧
        ringKrullDim (pthRootAlgebra n r R (t ∘ Fin.castLE hr)) = (d : WithBot ℕ∞) ∧
        IsLocalRing.maximalIdeal (pthRootAlgebra n r R (t ∘ Fin.castLE hr)) =
          (IsLocalRing.maximalIdeal R).map (algebraMap R _) ⊔
            Ideal.span (Set.range (parameterRootCoordinate (t ∘ Fin.castLE hr) n)) ∧
        IsLocalRing.IsRegularSystemOfParameters
          (List.ofFn (parameterRootCoordinate (t ∘ Fin.castLE hr) n) ++
            ((List.ofFn t).drop r).map (algebraMap R _)) ∧
        (∃ e : (pthRootAlgebra n r R (t ∘ Fin.castLE hr) ⧸
            (IsLocalRing.maximalIdeal R).map (algebraMap R _)) ≃ₐ[R]
            pthRootAlgebra n r (IsLocalRing.ResidueField R) (fun _ ↦ 0),
          ∀ i, e (Ideal.Quotient.mk _ (parameterRootCoordinate (t ∘ Fin.castLE hr) n i)) =
            parameterRootCoordinate (fun _ : Fin r ↦ (0 : IsLocalRing.ResidueField R)) n i) ∧
        (∃ e : IsLocalRing.ResidueField R ≃+*
            IsLocalRing.ResidueField (pthRootAlgebra n r R (t ∘ Fin.castLE hr)),
          ∀ a : R, e (IsLocalRing.residue R a) =
            IsLocalRing.residue _ (algebraMap R _ a)) ∧
        (IsStrictlyHenselianLocalRing R →
          IsStrictlyHenselianLocalRing (pthRootAlgebra n r R (t ∘ Fin.castLE hr))) ∧
        (r = 0 → Function.Bijective
          (algebraMap R (pthRootAlgebra n r R (t ∘ Fin.castLE hr)))) := by
  classical
  let s := t ∘ Fin.castLE hr
  let B := pthRootAlgebra n r R s
  obtain ⟨b, hb⟩ := root_basis s hn
  have hfinite : Module.Finite R B := Module.Finite.of_basis b
  have hinj : Function.Injective (algebraMap R B) := rootAlgebraMap_injective s hn
  have : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective R B).mpr hinj
  have hdim : ringKrullDim B = (d : WithBot ℕ∞) := by
    rw [ringKrullDim_eq_of_isIntegral R B, ← ht.2]
    simp
  have hs (i : Fin r) : s i ∈ IsLocalRing.maximalIdeal R := by
    rw [← ht.1]
    exact Ideal.subset_span (List.mem_ofFn.mpr ⟨Fin.castLE hr i, rfl⟩)
  obtain ⟨hlocal, hm⟩ := root_local s hs hn
  let l := List.ofFn (parameterRootCoordinate s n) ++
    ((List.ofFn t).drop r).map (algebraMap R B)
  have hspan : Ideal.span {x | x ∈ l} = IsLocalRing.maximalIdeal B :=
    (root_parameter_span d t ht r hr n hn).trans hm.symm
  have hlength : (l.length : WithBot ℕ∞) = ringKrullDim B := by
    rw [hdim]
    have hlen : l.length = d := by simp [l]; omega
    rw [hlen]
  have hreg : IsRegularLocalRing B := regular_of_parameters l hspan hlength
  have hhen : HenselianLocalRing B := HenselianLocalRing.finite_local_henselian R B
  obtain ⟨eres, heres⟩ := root_residue_equiv s hm
  refine ⟨b, hb, hfinite, hinj, inferInstance, hreg, hhen, inferInstance, hdim, hm,
    ⟨hspan, hlength⟩, root_closed_fibre s hs hn, ⟨eres, heres⟩, ?_,
    root_algebra_noVariables s hn⟩
  intro hstrict
  have : IsSepClosed (IsLocalRing.ResidueField B) := ⟨fun p hp ↦ by
    have hh := (IsSepClosed.splits_of_separable
      (p.map eres.symm.toRingHom) (hp.map (f := eres.symm.toRingHom))).map eres.toRingHom
    rw [Polynomial.map_map, show eres.toRingHom.comp eres.symm.toRingHom =
      RingHom.id _ from RingEquiv.comp_symm eres, Polynomial.map_id] at hh
    exact hh⟩
  exact ⟨inferInstance⟩

end Algebra

