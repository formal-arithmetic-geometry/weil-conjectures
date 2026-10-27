module

public import Sheaf.Algebra.Lie.ChevalleyAdmissibleRepresentation
public import Mathlib.Algebra.Lie.CartanSubalgebra
public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Data.List.OfFn

/-!
# The integral nonopposite Chevalley exponential commutator

Source: Milne, Algebraic Groups (2017), Theorem 23.71, pp. 508--509 (bracket
normalization), and equation (153), p. 510 (the exponential on an admissible lattice).
The two-root identity and its integral proof are the agent-written calculation in
(blueprint: lem-sfb-chevalley-nonopposite-exponential-commutator).

The constants precede the representation, its lattice, and the coefficient ring.
The ordered list records each positive root bidegree together with its unique root index.
The identity is quantified over all commutative rings, in particular the universal
polynomial ring in two variables over the integers. Thus it asserts the integral
polynomial identity, including its specializations to rings with torsion and nilpotents.
Scalar extension is written `A ⊗[ℤ] Λ`, canonically the same module as `Λ ⊗[ℤ] A`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w z

namespace LieAlgebra

open scoped TensorProduct

/-- The finite exponential of an operator preserving an admissible lattice in all divided
powers, with coefficients extended to an arbitrary commutative ring.
Source: Milne, Algebraic Groups (2017), equation (153), p. 510
(blueprint: lem-sfb-chevalley-nonopposite-exponential-commutator).

The truncation uses the rational dimension: for a nilpotent endomorphism all powers from
that dimension onward vanish. For a zero-dimensional space the empty sum is the unique
endomorphism, which is also the identity. This construction uses actual restricted linear
maps and their scalar extensions; it makes no choice of matrices or lattice basis. -/
noncomputable def admissibleRootExponential
    {W : Type w} [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (T : Module.End ℚ W) (Λ : Submodule ℤ W)
    (hstable : ∀ (m : ℕ) (w : W), w ∈ Λ →
      ((Nat.factorial m : ℚ)⁻¹ • T ^ m) w ∈ Λ)
    (A : Type z) [CommRing A] (a : A) : Module.End A (A ⊗[ℤ] Λ) :=
  ∑ m ∈ Finset.range (Module.finrank ℚ W),
    a ^ m • ((((Nat.factorial m : ℚ)⁻¹ • T ^ m).restrictScalars ℤ).restrict
      (hstable m)).baseChange A

/-- The commutator of two distinct, nonopposite Chevalley root exponentials is an ordered
product of higher-root exponentials with integer coefficients independent of the
representation and the coefficient ring.
Source: Milne, Algebraic Groups (2017), Theorem 23.71, pp. 508--509, and (153), p. 510;
the missing two-root calculation is agent-written
(blueprint: lem-sfb-chevalley-nonopposite-exponential-commutator).

Proof plan:
1. Apply `lem-sfb-chevalley-string-central-parity` to order the roots as (a,b), with
   divided adjoint string Y_k = (ad e_a)^k(e_b)/k!, integral coefficients c_k, and integral
   central half-bracket corrections C_d. Pass their identities through the representation.
   The brackets of the Y_k commute with every Y_k and with one another.
2. In rational endomorphism-valued formal series, expand iterated commutators using
   Pascal's identity. Comparing coefficients gives
   E_a(s) rho(e_b) E_a(-s) = sum_k s^k rho(Y_k).
   The binomial theorem gives E_a(s) E_a(-s) = 1. Conjugating each power of rho(e_b)
   yields E_a(s) E_b(t) E_a(-s) E_b(-t)
   = exp(t sum_k s^k rho(Y_k)) E_b(-t).
3. Apply `lem-sfb-formal-class-two-exponential` to the list
   ts Y_1, ts^2 Y_2, ..., ts^q Y_q, t Y_0. With Y_d = 0 for d > q put
   D_d = -C_d + [Y_0,Y_d]. The correction is sum_d s^d t^2 rho(D_d).
   It is central relative to the string, so move it past E_b(-t) and cancel E_b(t).
4. Each D_d is an integer multiple of e_(2b+da), or zero when this is not a root:
   this follows from the integral C_d, the integral c_d, and the Chevalley bracket table.
   The D_d commute mutually. Split their correction exponential by the class-two formula.
   This gives integral factors in b+ka and 2b+da, fixed before choosing a representation.
5. Arrange these factors in the prescribed order. Central factors move freely. For two
   string factors the class-two formula gives exp X exp Y = exp Y exp X exp([X,Y]);
   the extra factor is central and has an integral coefficient and the required bidegree.
   Adjacent swaps decrease the finite inversion count. Collect factors at the same root
   by adding parameters. If the chosen orientation is reversed, invert the product and
   interchange s,t, using K_ba = K_ab^(-1), then repeat the swaps. Insert zero coefficients
   at unused bidegrees. This also handles q = 0 and the empty ordered set.
6. In an integer basis of the full finite free lattice, divided powers have integer
   matrices and vanish beyond the rational dimension. Thus the displayed expressions
   are matrix polynomials over ℤ[s,t]. Their difference vanishes in rational formal
   series by the previous steps. The coefficientwise inclusion ℤ[s,t] into ℚ[[s,t]]
   is injective, so it vanishes integrally. Evaluate in any commutative ring A.
   A zero-rank lattice has no entries to check. No faithfulness, weight-generation,
   or algebraic-group reductivity is used. -/
theorem chevalley_nonopposite_exponential_commutator
    (L : Type u) [LieRing L] [LieAlgebra ℚ L] [FiniteDimensional ℚ L]
    [HasTrivialRadical ℚ L] (H : LieSubalgebra ℚ L) [H.IsCartanSubalgebra]
    [LieModule.IsTriangularizable ℚ H L]
    (I : Type v) [Finite I] (P : RootPairing I ℚ (Module.Dual ℚ H) H)
    [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (heval : ∀ (f : Module.Dual ℚ H) (h : H), P.toLinearMap f h = f h)
    (Δ : P.Base) (e : I → L)
    (he : ∀ i : I, e i ≠ 0 ∧ ∀ h : H, ⁅(h : L), e i⁆ = P.root i h • e i)
    (hopp : ∀ i : I, ⁅e i, e (P.reflectionPerm i i)⁆ = (P.coroot i : L))
    (hadd : ∀ i j k : I, P.root i + P.root j = P.root k →
      ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
        ⁅e i, e j⁆ = ((ε : ℚ) * (P.chainBotCoeff i j + 1)) • e k)
    (hzero : ∀ i j : I, P.root i + P.root j ∉ Set.range P.root →
      P.root i + P.root j ≠ 0 → ⁅e i, e j⁆ = 0)
    (B : Module.Basis (Δ.support ⊕ I) ℚ L)
    (Bh : ∀ i : Δ.support, B (Sum.inl i) = (P.coroot i : L))
    (Be : ∀ i : I, B (Sum.inr i) = e i)
    (α β : I) (hne : α ≠ β) (hnopp : P.root α ≠ -P.root β)
    (s : List (ℕ × ℕ × I)) (hs : s.Nodup)
    (hmem : ∀ d : ℕ × ℕ × I, d ∈ s ↔
      0 < d.1 ∧ 0 < d.2.1 ∧ d.1 • P.root α + d.2.1 • P.root β = P.root d.2.2)
    (horder : s.Pairwise (fun d d' ↦ d.1 + d.2.1 ≤ d'.1 + d'.2.1)) :
    ∃ c : ℕ × ℕ → ℤ,
      ∀ (W : Type w) [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
        [LieRingModule L W] [LieModule ℚ L W] (Λ : Submodule ℤ W)
        [Submodule.IsLattice ℚ Λ] [Module.Free ℤ Λ]
        (hnil : ∀ i : I, IsNilpotent (LieModule.toEnd ℚ L W (e i)))
        (hstable : ∀ (i : I) (m : ℕ) (w : W), w ∈ Λ →
          ((Nat.factorial m : ℚ)⁻¹ • LieModule.toEnd ℚ L W (e i) ^ m) w ∈ Λ)
        (A : Type z) [CommRing A] (a b : A),
        admissibleRootExponential (LieModule.toEnd ℚ L W (e α)) Λ (hstable α) A a *
            admissibleRootExponential (LieModule.toEnd ℚ L W (e β)) Λ (hstable β) A b *
            admissibleRootExponential (LieModule.toEnd ℚ L W (e α)) Λ (hstable α) A (-a) *
            admissibleRootExponential (LieModule.toEnd ℚ L W (e β)) Λ (hstable β) A (-b) =
          (s.map (fun d ↦ admissibleRootExponential
            (LieModule.toEnd ℚ L W (e d.2.2)) Λ (hstable d.2.2) A
            ((c (d.1, d.2.1) : A) * a ^ d.1 * b ^ d.2.1))).prod := by
  sorry

end LieAlgebra
