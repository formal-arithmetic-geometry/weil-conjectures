module

public import Sheaf.Algebra.Lie.ChevalleyRootNormalization
public import Mathlib.RingTheory.Nilpotent.Exp
import Sheaf.Algebra.Lie.SplitSemisimpleRootDecomposition

/-!
# Signed adjoint Weyl operators in a rational Chevalley basis

Source: Milne, Algebraic Groups (2017), Section 23h, Theorem 23.71, pp. 508–509;
agent-formulated root-string consequence used in Theorem 23.72, pp. 510–511
(blueprint: lem-sfb-chevalley-adjoint-weyl-signs).

The exponential is Mathlib's finite nilpotent exponential `IsNilpotent.exp`.
Multiplication of endomorphisms composes from right to left.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

namespace LieAlgebra

open Classical in
/-- The adjoint Weyl operator sends each chosen root vector to its reflected root vector
with a unique sign, and acts on the split Cartan subalgebra by the coroot reflection.

Source: Milne, Algebraic Groups (2017), Section 23h, Theorem 23.71, pp. 508–509;
agent-formulated consequence for the omitted details of Theorem 23.72, pp. 510–511
(blueprint: lem-sfb-chevalley-adjoint-weyl-signs).

Proof plan:
1. If the roots are empty all conclusions are vacuous. Otherwise apply
   `lem-sfb-split-semisimple-root-decomposition` to obtain nilpotence of the root adjoints.
   The normalized opposite brackets and weight equations give the rank-one sl2 relations.
2. Apply `lem-sfb-integrable-sl2-reflection-automorphism`: the three exponentials give
   the stated Cartan reflection, exchange opposite root vectors with minus signs, and map
   every root line isomorphically to its reflected line. Thus the coefficient is nonzero.
3. For roots other than the two roots on this line, reducedness gives independence.
   `lem-sfb-root-string-integer-interval` gives the consecutive string from beta-p alpha
   to beta+q alpha. The successive bracket magnitudes p+1,...,p+m show that the m-th
   divided adjoint power has coefficient plus or minus binomial(p+m,m), hence integral.
   Powers past the string vanish. Apply the same argument to the negative root.
4. On the remaining generators, E(e_alpha)=0, E(e_-alpha)=h_alpha,
   E^2(e_-alpha)/2!=-e_alpha, and E(h_alpha)=-2e_alpha; the analogous F formulas hold.
   Therefore exp(plus or minus E) and exp(plus or minus F) preserve the integer span of
   h_alpha and all root vectors. The finite binomial identity proves exp(E)exp(-E)=1
   and exp(F)exp(-F)=1, so the Weyl operator and its inverse preserve this lattice.
5. The direct root decomposition identifies its intersection with any root line with
   the integer span of that chosen vector. The root-line coefficient and its inverse
   are therefore integers, hence the coefficient is 1 or -1. Nonzero root vectors give
   uniqueness of that sign. The Cartan formula is already supplied by step 2. -/
theorem chevalley_adjoint_weyl_signs
    (L : Type u) [LieRing L] [LieAlgebra ℚ L] [FiniteDimensional ℚ L]
    [HasTrivialRadical ℚ L] (H : LieSubalgebra ℚ L) [IsLieAbelian H]
    (hmax : ∀ K : LieSubalgebra ℚ L, H ≤ K → IsLieAbelian K → K = H)
    (I : Type v) [Finite I] (P : RootPairing I ℚ (Module.Dual ℚ H) H)
    [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (heval : ∀ (a : Module.Dual ℚ H) (h : H), P.toLinearMap a h = a h)
    (hdecomp : DirectSum.IsInternal
      (Sum.elim (fun _ : Unit ↦ H.toSubmodule)
        (fun i : I ↦ (LieModule.weightSpace L (P.root i)).toSubmodule)))
    (hdim : ∀ i : I, Module.finrank ℚ (LieModule.weightSpace L (P.root i)) = 1)
    (e : I → L)
    (he : ∀ i : I, e i ∈ LieModule.weightSpace L (P.root i) ∧ e i ≠ 0)
    (hopp : ∀ i : I, ⁅e i, e (P.reflectionPerm i i)⁆ = (P.coroot i : L))
    (hadd : ∀ i j k : I, P.root i + P.root j = P.root k →
      ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
        ⁅e i, e j⁆ = ((ε : ℚ) * (P.chainBotCoeff i j + 1)) • e k)
    (hzero : ∀ i j : I, P.root i + P.root j ∉ Set.range P.root →
      P.root i + P.root j ≠ 0 → ⁅e i, e j⁆ = 0) :
    (∀ i : I, IsNilpotent (ad ℚ L (e i))) ∧
    ∀ i : I,
      (∀ j : I, ∃! ε : ℤ, (ε = 1 ∨ ε = -1) ∧
        (IsNilpotent.exp (ad ℚ L (e i)) *
          IsNilpotent.exp (-ad ℚ L (e (P.reflectionPerm i i))) *
          IsNilpotent.exp (ad ℚ L (e i))) (e j) =
            (ε : ℚ) • e (P.reflectionPerm i j)) ∧
      ∀ h : H,
        (IsNilpotent.exp (ad ℚ L (e i)) *
          IsNilpotent.exp (-ad ℚ L (e (P.reflectionPerm i i))) *
          IsNilpotent.exp (ad ℚ L (e i))) (h : L) =
            (h : L) - (P.root i h) • (P.coroot i : L) := by
  sorry

end LieAlgebra
