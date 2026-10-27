module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# An inverse-derivative presentation of a unit binomial

Source: Stacks Project, Tag 03PL (`lemma-kummer-sequence`), affine calculation, and
Tag 00UB (`definition-standard-etale`). The explicit certificate and quotient maps are the
agent-extracted algebra calculation (blueprint: lem-sfb-unit-binomial-derivative-presentation).
-/

@[expose] public section

universe u

namespace Polynomial.UnitBinomial

variable (R : Type u) [CommRing R] (n : ℕ) (u : Rˣ)

/-- The polynomial `T^n - u` in the affine calculation of Stacks, Tag 03PL.
(blueprint: lem-sfb-unit-binomial-derivative-presentation) -/
noncomputable def polynomial : Polynomial R :=
  Polynomial.X ^ n - Polynomial.C (u : R)

/-- The quotient `B = R[T]/(T^n-u)`, with Mathlib's quotient algebra structure.
Source: Stacks, Tag 03PL (blueprint: lem-sfb-unit-binomial-derivative-presentation). -/
abbrev RootAlgebra :=
  Polynomial R ⧸ Ideal.span {polynomial R n u}

/-- The quotient `C = R[T,Y]/(f,Yf'-1)`. Variable `0` is `T` and variable `1` is `Y`;
`Polynomial.aeval` embeds a polynomial in `T` into the two-variable polynomial ring.
Source: Stacks, Tags 03PL and 00UB, explicit inverse-derivative presentation
(blueprint: lem-sfb-unit-binomial-derivative-presentation). -/
abbrev DerivativePresentation :=
  MvPolynomial (Fin 2) R ⧸
    Ideal.span
      ({Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) (polynomial R n u),
       MvPolynomial.X (1 : Fin 2) *
         Polynomial.aeval (MvPolynomial.X (0 : Fin 2))
           (Polynomial.derivative (polynomial R n u)) - 1} : Set (MvPolynomial (Fin 2) R))

/-- The class `t` of `T` in `B`. Source: Stacks, Tag 03PL
(blueprint: lem-sfb-unit-binomial-derivative-presentation). -/
noncomputable def root : RootAlgebra R n u :=
  Ideal.Quotient.mkₐ R (Ideal.span {polynomial R n u}) Polynomial.X

/-- The classes of the two variables in `C`: `generator ... 0 = x`, `generator ... 1 = y`.
Source: Stacks, Tags 03PL and 00UB, explicit inverse-derivative presentation
(blueprint: lem-sfb-unit-binomial-derivative-presentation). -/
noncomputable def generator (i : Fin 2) : DerivativePresentation R n u :=
  Ideal.Quotient.mkₐ R _ (MvPolynomial.X i)

/-- The explicit candidate `v * t^(n-1)` for the inverse of `t`, where `v` is the image
of `u⁻¹`. Source: Stacks, Tag 03PL, explicit affine calculation
(blueprint: lem-sfb-unit-binomial-derivative-presentation). -/
noncomputable def rootInverse : RootAlgebra R n u :=
  algebraMap R (RootAlgebra R n u) (↑(u⁻¹) : R) * root R n u ^ (n - 1)

/-- The derivative-inverse certificate `h = ā * (v * t^(n-1))^(n-1)`.
Source: Stacks, Tag 03PL, explicit affine calculation
(blueprint: lem-sfb-unit-binomial-derivative-presentation). -/
noncomputable def inverseDerivative (a : R) : RootAlgebra R n u :=
  algebraMap R (RootAlgebra R n u) a * rootInverse R n u ^ (n - 1)

/-- The explicit derivative certificate and mutually inverse `R`-algebra maps for a unit
binomial. The maps preserve the structure maps because they are `R`-algebra homomorphisms.
No nontriviality hypothesis is imposed; `n = 1` is included.

Source: Stacks, Tag 03PL (`lemma-kummer-sequence`), affine calculation, and Tag 00UB
(`definition-standard-etale`); explicit agent-extracted quotient calculation
(blueprint: lem-sfb-unit-binomial-derivative-presentation).

Proof plan:
1. The quotient relation gives `t^n = ū`. Put `s = v*t^(n-1)`. Since `n ≥ 1`,
   `t*s = v*t^n = v*ū = 1` (def-weil-pbc-algebra-hom-quotient).
2. Formal differentiation gives `f' = n*T^(n-1)` (def-weil-polynomial-ring).
   The image of `a*n = 1` gives `f'(t)*h = (n*ā)*(t*s)^(n-1) = 1`.
3. Evaluate `R[T,Y]` at `(t,h)` (def-weil-pbc-mv-polynomial-ring). Both `f` and
   `Y*f'-1` vanish, hence evaluation factors through their ideal to give `α`.
4. Evaluation at `x` kills `f` in `C`, so descends to `β`, with `β(t) = x`.
5. The composite `α.comp β` fixes `t` and constants, hence every polynomial class.
   For `d = f'(x)` and `k = β(h)`, one has `d*k = 1` and `y*d = 1`.
   Thus `y = y*(d*k) = (y*d)*k = k`; the other composite fixes both generators
   and constants, hence every two-variable polynomial class. These factorizations
   use def-weil-pbc-algebra-hom-quotient and def-weil-pbc-mv-polynomial-ring.
6. Both maps are over `R`, so identify the structure maps. For `n = 1`,
   `s = v`, `h = ā = 1`, and `f' = 1`. In the zero ring all equations still hold.
-/
theorem derivative_presentation (a : R) (hn : 1 ≤ n) (ha : a * (n : R) = 1) :
    root R n u ^ n = algebraMap R (RootAlgebra R n u) (u : R) ∧
    root R n u * rootInverse R n u = 1 ∧
    Polynomial.aeval (root R n u) (Polynomial.derivative (polynomial R n u)) *
      inverseDerivative R n u a = 1 ∧
    ∃ (α : DerivativePresentation R n u →ₐ[R] RootAlgebra R n u)
      (β : RootAlgebra R n u →ₐ[R] DerivativePresentation R n u),
      α (generator R n u 0) = root R n u ∧
      α (generator R n u 1) = inverseDerivative R n u a ∧
      β (root R n u) = generator R n u 0 ∧
      α.comp β = AlgHom.id R (RootAlgebra R n u) ∧
      β.comp α = AlgHom.id R (DerivativePresentation R n u) := by
  let B := RootAlgebra R n u
  let C := DerivativePresentation R n u
  let f := polynomial R n u
  let I := Ideal.span {f}
  let F : MvPolynomial (Fin 2) R := Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) f
  let D : MvPolynomial (Fin 2) R :=
    Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) (Polynomial.derivative f)
  let J := Ideal.span ({F, MvPolynomial.X (1 : Fin 2) * D - 1} :
    Set (MvPolynomial (Fin 2) R))
  let qB : Polynomial R →ₐ[R] B := Ideal.Quotient.mkₐ R I
  let qC : MvPolynomial (Fin 2) R →ₐ[R] C := Ideal.Quotient.mkₐ R J
  let t := root R n u
  let x := generator R n u 0
  let y := generator R n u 1
  let h := inverseDerivative R n u a
  have evalB (p : Polynomial R) : Polynomial.aeval t p = qB p := by
    exact Polynomial.aeval_algHom_apply qB Polynomial.X p |>.trans
      (by rw [Polynomial.aeval_X_left_apply])
  have ht : t ^ n = algebraMap R B (u : R) := by
    have hf : qB f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton f))
    rw [← evalB] at hf
    simpa [f, polynomial, sub_eq_zero] using hf
  have hs : t * rootInverse R n u = 1 := by
    calc
      t * rootInverse R n u =
          algebraMap R B (↑(u⁻¹) : R) * t ^ n := by
        dsimp [rootInverse, t]
        rw [← mul_assoc, mul_comm (root R n u), mul_assoc,
          ← pow_succ', Nat.sub_add_cancel hn]
      _ = 1 := by rw [ht, ← map_mul]; simp
  have hd : Polynomial.aeval t (Polynomial.derivative f) * h = 1 := by
    have han : (n : B) * algebraMap R B a = 1 := by
      simpa [map_mul, mul_comm] using congrArg (algebraMap R B) ha
    calc
      Polynomial.aeval t (Polynomial.derivative f) * h =
          ((n : B) * algebraMap R B a) * (t * rootInverse R n u) ^ (n - 1) := by
        simp only [f, polynomial, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
          Polynomial.derivative_C, sub_zero, map_mul,
          Polynomial.aeval_X_pow, map_natCast]
        dsimp [h, inverseDerivative, t]
        rw [mul_pow]
        ring
      _ = 1 := by rw [han, hs]; simp
  have evalC (p : Polynomial R) :
      Polynomial.aeval x p = qC (Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) p) :=
    Polynomial.aeval_algHom_apply qC _ p
  have hx : Polynomial.aeval x f = 0 := by
    rw [evalC]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp [F]))
  have hy : y * Polynomial.aeval x (Polynomial.derivative f) = 1 := by
    apply sub_eq_zero.mp
    have hz : qC (MvPolynomial.X (1 : Fin 2) * D - 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    have hqy : qC (MvPolynomial.X (1 : Fin 2)) = y := rfl
    simpa only [map_sub, map_mul, map_one, D, ← evalC, hqy] using hz
  let E : MvPolynomial (Fin 2) R →ₐ[R] B :=
    MvPolynomial.aeval (fun i ↦ if i = 0 then t else h)
  have evalE (p : Polynomial R) :
      E (Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) p) = Polynomial.aeval t p := by
    simpa [E] using
      (Polynomial.aeval_algHom_apply E (MvPolynomial.X (0 : Fin 2)) p).symm
  have hE : ∀ p ∈ J, E p = 0 := by
    change J ≤ RingHom.ker E.toRingHom
    apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · change E F = 0
      rw [evalE]
      simpa [f, polynomial] using sub_eq_zero.mpr ht
    · rw [Set.mem_singleton_iff] at hp
      subst p
      change E (MvPolynomial.X (1 : Fin 2) * D - 1) = 0
      simp only [map_sub, map_mul, map_one, D, evalE]
      rw [show E (MvPolynomial.X (1 : Fin 2)) = h by simp [E],
        mul_comm, hd, sub_self]
  let α : C →ₐ[R] B := Ideal.Quotient.liftₐ J E hE
  have hα (p : MvPolynomial (Fin 2) R) : α (qC p) = E p :=
    AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp J E hE) p
  have hβ : ∀ p ∈ I, Polynomial.aeval x p = 0 := by
    change I ≤ RingHom.ker (Polynomial.aeval x).toRingHom
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)
  let β : B →ₐ[R] C := Ideal.Quotient.liftₐ I (Polynomial.aeval x) hβ
  have hβq (p : Polynomial R) : β (qB p) = Polynomial.aeval x p :=
    AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp I (Polynomial.aeval x) hβ) p
  have hαx : α x = t := by
    change α (qC (MvPolynomial.X 0)) = t
    rw [hα]; simp [E]
  have hαy : α y = h := by
    change α (qC (MvPolynomial.X 1)) = h
    rw [hα]; simp [E]
  have hβt : β t = x := by
    change β (qB Polynomial.X) = x
    rw [hβq, Polynomial.aeval_X]
  have hβαy : β h = y := by
    have hdk : Polynomial.aeval x (Polynomial.derivative f) * β h = 1 := by
      have he := congrArg β hd
      rw [map_mul, map_one, ← Polynomial.aeval_algHom_apply, hβt] at he
      exact he
    calc
      β h = (y * Polynomial.aeval x (Polynomial.derivative f)) * β h := by rw [hy, one_mul]
      _ = y := by rw [mul_assoc, hdk, mul_one]
  refine ⟨ht, hs, hd, α, β, hαx, hαy, hβt, ?_, ?_⟩
  · apply Ideal.Quotient.algHom_ext
    apply Polynomial.algHom_ext
    change α (β t) = t
    rw [hβt, hαx]
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    change β (α (generator R n u i)) = generator R n u i
    fin_cases i
    · exact congrArg β hαx |>.trans hβt
    · exact congrArg β hαy |>.trans hβαy

end Polynomial.UnitBinomial
