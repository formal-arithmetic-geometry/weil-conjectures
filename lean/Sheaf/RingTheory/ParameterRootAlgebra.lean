/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.RingTheory.PthRootAlgebraLocal
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.RingTheory.AlgebraTower
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Explicit simultaneous-root algebras

Source: monic division (Stacks 00G3, 04GG) and polynomial quotient universal properties.
The constructions work over arbitrary commutative rings.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
namespace Algebra.ParameterRoot

variable {R : Type u} [CommRing R] {r : ℕ} (t : Fin r → R) (n : ℕ)

abbrev Ring := pthRootAlgebra n r R t

abbrev root (i : Fin r) : Ring t n := Ideal.Quotient.mk _ (MvPolynomial.X i)

@[simp] theorem root_pow (i : Fin r) : root t n i ^ n = algebraMap R (Ring t n) (t i) := by
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span ⟨i, rfl⟩ : MvPolynomial.X i ^ n - MvPolynomial.C (t i) ∈
      Ideal.span (Set.range (fun j : Fin r ↦
        MvPolynomial.X j ^ n - MvPolynomial.C (t j))))
  change Ideal.Quotient.mk _ (MvPolynomial.X i) ^ n =
    Ideal.Quotient.mk _ (MvPolynomial.C (t i))
  simpa only [map_sub, map_pow, sub_eq_zero] using h

def lift {S : Type v} [CommRing S] [Algebra R S]
    (x : Fin r → S) (hx : ∀ i, x i ^ n = algebraMap R S (t i)) : Ring t n →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval x) (by
    have hle : Ideal.span (Set.range (fun j : Fin r ↦
        MvPolynomial.X j ^ n - MvPolynomial.C (t j))) ≤
        RingHom.ker (MvPolynomial.aeval x).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      simpa using sub_eq_zero.mpr (hx i)
    exact fun a ha ↦ hle ha)

@[simp] theorem lift_root {S : Type v} [CommRing S] [Algebra R S]
    (x : Fin r → S) (hx : ∀ i, x i ^ n = algebraMap R S (t i)) (i : Fin r) :
    lift t n x hx (root t n i) = x i := by
  simp [lift, root, Ideal.Quotient.lift_mk]

@[ext] theorem hom_ext {S : Type v} [CommRing S] [Algebra R S]
    {f g : Ring t n →ₐ[R] S} (h : ∀ i, f (root t n i) = g (root t n i)) : f = g := by
  apply Ideal.Quotient.algHom_ext R
  apply MvPolynomial.algHom_ext
  exact h

/-- Adjoin the first root after adjoining the remaining roots. -/
def succEquiv (t : Fin (r + 1) → R) :
    Ring t n ≃ₐ[R]
      AdjoinRoot (Polynomial.X ^ n -
        Polynomial.C (algebraMap R (Ring (fun i ↦ t i.succ) n) (t 0))) := by
  let A := Ring (fun i ↦ t i.succ) n
  let P : Polynomial A := Polynomial.X ^ n - Polynomial.C (algebraMap R A (t 0))
  let j : A →ₐ[R] Ring t n := lift (fun i ↦ t i.succ) n
    (fun i ↦ root t n i.succ) (fun i ↦ root_pow t n i.succ)
  let f : Ring t n →ₐ[R] AdjoinRoot P := lift t n
    (Fin.cases (AdjoinRoot.root P) (fun i ↦ algebraMap A _ (root _ n i))) (by
      intro i
      refine Fin.cases ?_ (fun k ↦ ?_) i
      · change AdjoinRoot.root P ^ n = algebraMap R (AdjoinRoot P) (t 0)
        rw [IsScalarTower.algebraMap_apply R A (AdjoinRoot P),
          AdjoinRoot.algebraMap_eq]
        have h := AdjoinRoot.eval₂_root P
        simpa [P, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
          Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero] using h
      · change algebraMap A (AdjoinRoot P) (root _ n k) ^ n = _
        rw [← map_pow, root_pow, ← IsScalarTower.algebraMap_apply])
  let g : AdjoinRoot P →ₐ[R] Ring t n := AdjoinRoot.liftAlgHom P j (root t n 0) (by
    simp [P, root_pow])
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply AdjoinRoot.algHom_ext'
    · apply hom_ext
      intro i
      change f (g (AdjoinRoot.of P (root _ n i))) = AdjoinRoot.of P (root _ n i)
      rw [show g (AdjoinRoot.of P (root _ n i)) = j (root _ n i) from
        AdjoinRoot.liftAlgHom_of P j _ _ (root _ n i)]
      rw [show j (root (fun i ↦ t i.succ) n i) = root t n i.succ from
        lift_root (fun i ↦ t i.succ) n _ _ i]
      simp only [f, lift_root, Fin.cases_succ, AdjoinRoot.algebraMap_eq]
    · change f (g (AdjoinRoot.root P)) = AdjoinRoot.root P
      simp only [g, AdjoinRoot.liftAlgHom_root, f, lift_root, Fin.cases_zero]
  · apply hom_ext
    intro i
    change g (f (root t n i)) = root t n i
    refine Fin.cases ?_ (fun k ↦ ?_) i
    · simp only [f, lift_root, Fin.cases_zero, g, AdjoinRoot.liftAlgHom_root]
    · simp only [f, lift_root, Fin.cases_succ, AdjoinRoot.algebraMap_eq,
        g, AdjoinRoot.liftAlgHom_of]
      exact lift_root (fun i ↦ t i.succ) n _ _ k

/-- With no variables the coefficient map is an isomorphism. -/
def emptyEquiv (t : Fin 0 → R) : Ring t n ≃ₐ[R] R := by
  have h : Ideal.span (Set.range (fun j : Fin 0 ↦
      MvPolynomial.X j ^ n - MvPolynomial.C (t j))) = ⊥ := by simp
  exact (Ideal.quotientEquivAlgOfEq R h).trans
    ((AlgEquiv.quotientBot R _).trans (MvPolynomial.isEmptyAlgEquiv R (Fin 0)))

/-- The monomial basis for an arbitrary simultaneous monic root quotient. -/
theorem exists_basis (hn : 0 < n) :
    ∃ b : Module.Basis (Fin r → Fin n) R (Ring t n),
      ∀ e, b e = ∏ i, root t n i ^ (e i).val := by
  classical
  by_cases hR : Subsingleton R
  · let := hR
    exact ⟨Module.Basis.ofEquivFun
      (LinearEquiv.ofSubsingleton (R := R) (Ring t n) ((Fin r → Fin n) → R)),
      fun _ ↦ Subsingleton.elim _ _⟩
  let : Nontrivial R := not_subsingleton_iff_nontrivial.mp hR
  have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  induction r with
  | zero =>
    let e := emptyEquiv n t
    refine ⟨(Module.Basis.singleton (Fin 0 → Fin n) R).map e.symm.toLinearEquiv, ?_⟩
    intro d
    simp
  | succ r ih =>
    let t' : Fin r → R := fun i ↦ t i.succ
    let A := Ring t' n
    obtain ⟨b, hb⟩ := ih t'
    let P : Polynomial A := Polynomial.X ^ n - Polynomial.C (algebraMap R A (t 0))
    have hP : P.Monic := Polynomial.monic_X_pow_sub_C _ (ne_of_gt hn)
    have hdeg : P.natDegree = n := by
      have : Nontrivial A := b.repr.toEquiv.nontrivial
      exact Polynomial.natDegree_X_pow_sub_C
    let c : Module.Basis (Fin n) A (AdjoinRoot P) :=
      (AdjoinRoot.powerBasis' hP).basis.reindex (finCongr hdeg)
    have hc (i : Fin n) : c i = AdjoinRoot.root P ^ i.val := by
      simp [c, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow,
        AdjoinRoot.powerBasis'_gen]
    let e : (Fin r → Fin n) × Fin n ≃ (Fin (r + 1) → Fin n) :=
      { toFun := fun d ↦ Fin.cons d.2 d.1
        invFun := fun d ↦ (fun i ↦ d i.succ, d 0)
        left_inv := fun _ ↦ rfl
        right_inv := fun d ↦ by funext i; exact Fin.cases rfl (fun _ ↦ rfl) i }
    let E := succEquiv n t
    refine ⟨((b.smulTower c).reindex e).map E.symm.toLinearEquiv, ?_⟩
    intro d
    apply E.injective
    simp only [Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply,
      Module.Basis.reindex_apply,
      Module.Basis.smulTower_apply, e, Equiv.coe_fn_symm_mk, hc, hb]
    rw [Fin.prod_univ_succ, map_mul, map_pow]
    have h0 : E (root t n 0) = AdjoinRoot.root P := by
      simp [E, succEquiv, AlgEquiv.ofAlgHom_apply, P, A, t']
    have hs (i : Fin r) : E (root t n i.succ) =
        algebraMap A (AdjoinRoot P) (root t' n i) := by
      simp [E, succEquiv, AlgEquiv.ofAlgHom_apply, P, A, t']
    rw [h0, map_prod]
    simp_rw [map_pow, hs]
    rw [Algebra.smul_def, map_prod, AlgEquiv.apply_symm_apply]
    simp_rw [map_pow]
    exact mul_comm _ _

/-- Positive degree gives a faithfully flat finite free algebra, including over zero rings. -/
theorem finite_faithfullyFlat (hn : 0 < n) :
    Module.Finite R (Ring t n) ∧ Module.FaithfullyFlat R (Ring t n) := by
  obtain ⟨b, _⟩ := exists_basis t n hn
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact ⟨Module.Finite.of_basis b, Module.FaithfullyFlat.of_linearEquiv R _ b.repr⟩

/-- Evaluation identifies the first root level with the coefficient ring. -/
def oneEquiv : Ring t 1 ≃ₐ[R] R := by
  let f := lift t 1 t (by simp)
  refine AlgEquiv.ofAlgHom f (Algebra.ofId R (Ring t 1)) ?_ ?_
  · ext
  · apply hom_ext
    intro i
    change algebraMap R (Ring t 1) (f (root t 1 i)) = root t 1 i
    rw [lift_root]
    simpa using (root_pow t 1 i).symm

/-- Divisibility induces the canonical power substitution. -/
def transition (m : ℕ) (h : n ∣ m) : Ring t n →ₐ[R] Ring t m :=
  lift t n (fun i ↦ root t m i ^ (m / n)) (fun i ↦ by
    rw [← pow_mul, Nat.div_mul_cancel h, root_pow])

@[simp] theorem transition_root (m : ℕ) (h : n ∣ m) (i : Fin r) :
    transition t n m h (root t n i) = root t m i ^ (m / n) := lift_root ..

@[simp] theorem transition_self (hn : 0 < n) :
    transition t n n (dvd_refl n) = AlgHom.id R _ := by
  apply hom_ext
  intro i
  simp [Nat.div_self hn]

theorem transition_comp (m l : ℕ) (h : n ∣ m) (h' : m ∣ l) :
    (transition t m l h').comp (transition t n m h) = transition t n l (h.trans h') := by
  apply hom_ext
  intro i
  simp only [AlgHom.comp_apply, transition_root, map_pow, ← pow_mul]
  congr 1
  exact Nat.div_mul_div h' h

/-- Adjoining refinement roots gives the larger simultaneous-root quotient. -/
def refineEquiv (m : ℕ) (h : n ∣ m) :
    Ring (root t n) (m / n) ≃+* Ring t m := by
  let A := Ring t n
  let B := Ring (root t n) (m / n)
  let tr := transition t n m h
  letI : Algebra A (Ring t m) := tr.toRingHom.toAlgebra
  let f : B →ₐ[A] Ring t m := lift (root t n) (m / n)
    (root t m) (fun i ↦ (transition_root t n m h i).symm)
  let g : Ring t m →ₐ[R] B := lift t m (root (root t n) (m / n)) (fun i ↦ by
    calc
      root (root t n) (m / n) i ^ m =
          (root (root t n) (m / n) i ^ (m / n)) ^ n := by
        rw [← pow_mul, Nat.div_mul_cancel h]
      _ = (algebraMap A B (root t n i)) ^ n := by rw [root_pow (root t n)]
      _ = algebraMap R B (t i) := by
        rw [← map_pow, root_pow t, ← IsScalarTower.algebraMap_apply])
  have hg (a : A) : g (tr a) = algebraMap A B a := by
    have he : g.comp tr = IsScalarTower.toAlgHom R A B := by
      apply hom_ext
      intro i
      change g (transition t n m h (root t n i)) = algebraMap A B (root t n i)
      rw [transition_root, map_pow]
      rw [show g (root t m i) = root (root t n) (m / n) i from lift_root t m _ _ i]
      exact root_pow (root t n) (m / n) i
    exact DFunLike.congr_fun he a
  refine RingEquiv.ofRingHom f.toRingHom g.toRingHom ?_ ?_
  · apply RingHom.ext
    intro a
    have he : (f.restrictScalars R).comp g = AlgHom.id R (Ring t m) := by
      apply hom_ext
      intro i
      change f (g (root t m i)) = root t m i
      rw [show g (root t m i) = root (root t n) (m / n) i from lift_root t m _ _ i]
      exact lift_root (root t n) (m / n) _ _ i
    exact DFunLike.congr_fun he a
  · apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      change g (f (algebraMap A B a)) = algebraMap A B a
      rw [f.commutes]
      exact hg a
    · intro i
      change g (f (root (root t n) (m / n) i)) = root (root t n) (m / n) i
      rw [show f (root (root t n) (m / n) i) = root t m i from
        lift_root (root t n) (m / n) _ _ i]
      exact lift_root t m _ _ i

@[simp] theorem refineEquiv_root (m : ℕ) (h : n ∣ m) (i : Fin r) :
    refineEquiv t n m h (root (root t n) (m / n) i) = root t m i := by
  simp [refineEquiv, RingEquiv.ofRingHom, lift_root]

@[simp] theorem refineEquiv_algebraMap (m : ℕ) (h : n ∣ m) (a : Ring t n) :
    refineEquiv t n m h (algebraMap _ _ a) = transition t n m h a := by
  let : Algebra (Ring t n) (Ring t m) := (transition t n m h).toRingHom.toAlgebra
  exact (lift (root t n) (m / n) (root t m)
    (fun i ↦ (transition_root t n m h i).symm)).commutes a

/-- A refinement basis is the monomial basis over the preceding level. -/
theorem exists_transition_basis (m : ℕ) (h : n ∣ m) (hq : 0 < m / n) :
    ∃ b : @Module.Basis (Fin r → Fin (m / n)) (Ring t n) (Ring t m) _ _
        (@Algebra.toModule _ _ _ _ (transition t n m h).toRingHom.toAlgebra),
      ∀ d, b d = ∏ i, root t m i ^ (d i).val := by
  let : Algebra (Ring t n) (Ring t m) := (transition t n m h).toRingHom.toAlgebra
  let e : Ring (root t n) (m / n) ≃ₐ[Ring t n] Ring t m :=
    { refineEquiv t n m h with commutes' := refineEquiv_algebraMap t n m h }
  obtain ⟨b, hb⟩ := exists_basis (root t n) (m / n) hq
  refine ⟨b.map e.toLinearEquiv, fun d ↦ ?_⟩
  simp only [Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply, hb, map_prod, map_pow]
  exact Finset.prod_congr rfl fun i _ ↦ congrArg (fun x ↦ x ^ (d i).val)
    (refineEquiv_root t n m h i)

/-- Ring homomorphisms out of the quotient are determined by coefficients and roots. -/
theorem ringHom_ext {S : Type v} [CommRing S] {f g : Ring t n →+* S}
    (hc : f.comp (algebraMap R _) = g.comp (algebraMap R _))
    (hx : ∀ i, f (root t n i) = g (root t n i)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · exact fun a ↦ RingHom.congr_fun hc a
  · exact hx

/-- The quotient evaluation with arbitrary coefficient homomorphism. -/
def ringLift {S : Type v} [CommRing S] (f : R →+* S)
    (x : Fin r → S) (hx : ∀ i, x i ^ n = f (t i)) : Ring t n →+* S := by
  let : Algebra R S := f.toAlgebra
  exact (lift t n x hx).toRingHom

@[simp] theorem ringLift_root {S : Type v} [CommRing S] (f : R →+* S)
    (x : Fin r → S) (hx : ∀ i, x i ^ n = f (t i)) (i : Fin r) :
    ringLift t n f x hx (root t n i) = x i := by
  let : Algebra R S := f.toAlgebra
  exact lift_root t n x hx i

@[simp] theorem ringLift_algebraMap {S : Type v} [CommRing S] (f : R →+* S)
    (x : Fin r → S) (hx : ∀ i, x i ^ n = f (t i)) (a : R) :
    ringLift t n f x hx (algebraMap R _ a) = f a := by
  let : Algebra R S := f.toAlgebra
  exact (lift t n x hx).commutes a

end Algebra.ParameterRoot
