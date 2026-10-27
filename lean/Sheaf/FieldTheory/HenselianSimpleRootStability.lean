module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Constructions
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Sheaf.FieldTheory.SimpleRootPerturbationNormalization
import Sheaf.RingTheory.HenselianResidueXRoot

/-!
# Stability of simple roots over a henselian valued field

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, XX 4.4, printed p.374,
and Stacks Project, Tag 04GG (blueprint: lem-per-henselian-simple-root-stability).

The theorem states the root-perturbation form of the henselian simple-root
principle for an arbitrary-rank nontrivial valuation; no completeness assumption
is made.
-/

@[expose] public section

universe u v

open Polynomial
open scoped Topology

namespace AddValuation

/-- In a henselian valued field, a simple root persists under sufficiently small
coefficient perturbations in the valuation topology.

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, XX 4.4, printed p.374,
and Stacks Project, Tag 04GG (blueprint: lem-per-henselian-simple-root-stability).
Here `Γ` includes the value `⊤` at zero; its finite elements form the ordered
additive value group. The topology hypothesis specifies exactly the ambient-value
balls of the node, even when the image of the valuation is not cofinal in `Γ`.
The valuation subring consists of the elements with additive valuation at least zero.

Proof:
1. In the discrete case the coefficient space is discrete because `Fin n` is
   finite. Take the singleton containing `c`, retaining the original simple root.
2. Otherwise apply `exists_open_coefficients_residue_X`. Its finite valuation
   estimates give an open `V`, nonzero `s,t`, and integral polynomials `H` with
   residue `X` and the identity `g(a+sX)=tH(X)`. The image under `z ↦ a+sz`
   of the maximal ideal is contained in `U`. This step does not use henselianity.
3. Apply `HenselianLocalRing.exists_simple_root_of_map_eq_X` to `H`. That theorem
   uses a monic reciprocal polynomial and Mathlib's monic Hensel lifting, and
   gives `z` in the maximal ideal with `H(z)=0` and `H'(z)` a unit.
4. Set `b=a+sz`. Evaluation of the polynomial identity gives `g(b)=0`.
   Its derivative gives `s*g'(b)=t*H'(z)`. The right side is nonzero because
   `t` is nonzero and the image of a unit in the field is nonzero, so `g'(b)≠0`.
   The maximal-ideal inclusion gives `b ∈ U`.
-/
theorem exists_open_coefficients_simple_root
    (F : Type u) [Field F] (Γ : Type v) [LinearOrderedAddCommGroupWithTop Γ]
    (v : AddValuation F Γ) [v.toValuation.IsNontrivial]
    [HenselianLocalRing v.toValuation.valuationSubring] [TopologicalSpace F]
    (hvaltop : ∀ x : F, (𝓝 x).HasBasis (fun γ : Γ ↦ γ ≠ ⊤)
      (fun γ ↦ {y : F | γ < v (y - x)}))
    (n : ℕ) (hn : 1 ≤ n) (c : Fin n → F) (a : F)
    (ha : (X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ)).IsRoot a)
    (hda : (X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ)).derivative.eval a ≠ 0) :
    ∀ U : Set F, IsOpen U → a ∈ U →
      ∃ V : Set (Fin n → F), IsOpen V ∧ c ∈ V ∧
        ∀ d : Fin n → F, d ∈ V → ∃ b : F,
          b ∈ U ∧ (X ^ n + ∑ i : Fin n, C (d i) * X ^ (i : ℕ)).IsRoot b ∧
          (X ^ n + ∑ i : Fin n, C (d i) * X ^ (i : ℕ)).derivative.eval b ≠ 0 := by
  classical
  intro U hU haU
  by_cases hdis : DiscreteTopology F
  · have : DiscreteTopology F := hdis
    refine ⟨{c}, isOpen_discrete _, Set.mem_singleton c, ?_⟩
    intro d hd
    have hdc : d = c := Set.mem_singleton_iff.mp hd
    subst d
    exact ⟨a, haU, ha, hda⟩
  obtain ⟨V, hV, hcV, s, t, _hs, ht, hsmall, hnorm⟩ :=
    exists_open_coefficients_residue_X F Γ v hvaltop hdis n hn c a ha hda U hU haU
  refine ⟨V, hV, hcV, ?_⟩
  intro d hd
  let g : F[X] := X ^ n + ∑ i : Fin n, C (d i) * X ^ (i : ℕ)
  obtain ⟨H, hH, hpoly⟩ := hnorm d hd
  change g.comp (C a + C s * X) =
    C t * H.map v.toValuation.valuationSubring.subtype at hpoly
  obtain ⟨z, hzm, hz, hz'⟩ := HenselianLocalRing.exists_simple_root_of_map_eq_X
    v.toValuation.valuationSubring H hH
  refine ⟨a + s * (z : F), hsmall z hzm, ?_, ?_⟩
  · have heval := congrArg (Polynomial.eval (z : F)) hpoly
    have hzF : (H.map v.toValuation.valuationSubring.subtype).eval (z : F) = 0 := by
      change (H.map v.toValuation.valuationSubring.subtype).eval
        (v.toValuation.valuationSubring.subtype z) = 0
      rw [eval_map_apply, hz.eq_zero]
      exact v.toValuation.valuationSubring.subtype.map_zero
    change g.IsRoot (a + s * (z : F))
    simpa only [IsRoot, eval_comp, eval_add, eval_C, eval_mul, eval_X, hzF,
      mul_zero] using heval
  · have hder := congrArg (fun p : F[X] ↦ p.derivative.eval (z : F)) hpoly
    have hzF' : (H.map v.toValuation.valuationSubring.subtype).derivative.eval
        (z : F) ≠ 0 := by
      rw [derivative_map]
      change (H.derivative.map v.toValuation.valuationSubring.subtype).eval
        (v.toValuation.valuationSubring.subtype z) ≠ 0
      rw [eval_map_apply]
      exact (isUnit_iff_ne_zero.mp (hz'.map v.toValuation.valuationSubring.subtype))
    have heq : s * g.derivative.eval (a + s * (z : F)) =
        t * (H.map v.toValuation.valuationSubring.subtype).derivative.eval (z : F) := by
      simpa only [derivative_comp, derivative_C_mul, derivative_add, derivative_C,
        derivative_X, mul_one, zero_add, eval_mul, eval_C, eval_comp, eval_add,
        eval_X] using hder
    intro hzero
    rw [hzero, mul_zero] at heq
    exact (mul_ne_zero ht hzF') heq.symm

end AddValuation
