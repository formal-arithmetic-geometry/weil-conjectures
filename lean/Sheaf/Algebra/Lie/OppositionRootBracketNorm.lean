module

public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Algebra.Lie.Weights.Basic
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.RootSystem.Chain
import Sheaf.Algebra.Lie.SplitSemisimpleRootDecomposition

/-!
# Squared norm of an opposition-compatible root bracket

Source: Milne, Algebraic Groups (2017), Section 23h, Theorem 23.71, pp. 508–509;
the conditional local formulation and proof are the agent expansion in the DAG
(blueprint: lem-sfb-opposition-root-bracket-norm).

The evaluation root pairing and ordinary simultaneous eigenspaces are the same as in
`LieAlgebra.exists_splitSemisimple_rootDecomposition`. No Chevalley basis is assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

namespace LieAlgebra

open Classical in
/-- Two root vectors normalized by an opposition involution have a bracket whose
opposition norm is the square of the lower string endpoint plus one, times its coroot.

Source: Milne, Algebraic Groups (2017), Section 23h, Theorem 23.71, pp. 508–509;
agent-stated conditional local version, not an assertion of Chevalley basis existence
(blueprint: lem-sfb-opposition-root-bracket-norm).

Proof plan:
1. Reducedness and the root-sum hypothesis imply that the two roots are independent.
   Apply `lem-sfb-split-semisimple-root-decomposition` and
   `lem-sfb-rational-killing-root-duality`. Write B for the Killing form, b for its dual
   form, t_r for the Killing-dual root and d_r = b(r,r) > 0. Opposite-root duality gives
   [x,y] = B(x,y)t_r and t_r = (d_r/2)h_r.
2. By `lem-sfb-root-string-integer-interval` the string is indexed by -p,...,q, with
   q >= 1. By `lem-sfb-root-string-endpoint-difference`, m = beta(h_alpha) = p-q.
   By `lem-sfb-root-string-adjacent-length-ratio`, q d_gamma = (p+1)d_beta.
3. Put f = -theta(u), E = ad(u), F = ad(f). Jacobi and normalization give
   EF-FE = ad(h_alpha). Choose one basis vector z_k in each one-dimensional string
   space. Write E z_k = a_k z_(k+1), F z_(k+1) = b_(k+1) z_k, and c_k = a_k b_(k+1).
   Endpoint vanishing gives c_q = 0. The commutator gives c_(k-1)-c_k = m+2k for
   k = 1,...,q. Summing gives c_0 = q m + q(q+1) = q(p+1), hence FE(v) = q(p+1)v.
   This does not assume any transition map invertible.
4. For w = [u,v], the automorphism property gives -theta(w) = [f,theta(v)]. Killing
   invariance gives B(w,-theta(w)) = -B(FE(v),theta(v)) = q(p+1)B(v,-theta(v)).
   Normalization of v and opposite-root duality, evaluated by beta, give
   B(v,-theta(v)) = 2/d_beta.
5. Jacobi puts w in the gamma root space. Apply opposite-root duality there and
   substitute the scalar: [w,-theta(w)] = q(p+1)d_gamma/d_beta h_gamma
   = (p+1)^2 h_gamma. Since gamma(h_gamma) = 2 and p+1 is nonzero, this also forces
   w to be nonzero. -/
theorem opposition_root_bracket_norm
    (L : Type u) [LieRing L] [LieAlgebra ℚ L] [FiniteDimensional ℚ L]
    [HasTrivialRadical ℚ L] (H : LieSubalgebra ℚ L) [IsLieAbelian H]
    (hmax : ∀ A : LieSubalgebra ℚ L, H ≤ A → IsLieAbelian A → A = H)
    (hsplit : ∀ h : H, (⨆ a : ℚ, (ad ℚ L (h : L)).eigenspace a) = ⊤)
    (I : Type v) [Finite I] (P : RootPairing I ℚ (Module.Dual ℚ H) H)
    [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (heval : ∀ (ξ : Module.Dual ℚ H) (h : H), P.toLinearMap ξ h = ξ h)
    (hdecomp : DirectSum.IsInternal
      (Sum.elim (fun _ : Unit ↦ H.toSubmodule)
        (fun i : I ↦ (LieModule.weightSpace L (P.root i)).toSubmodule)))
    (hdim : ∀ i : I, Module.finrank ℚ (LieModule.weightSpace L (P.root i)) = 1)
    (hcoroot : ∀ i : I, (P.coroot i : L) ∈ Submodule.span ℚ
      {z : L | ∃ x ∈ LieModule.weightSpace L (P.root i),
        ∃ y ∈ LieModule.weightSpace L (-P.root i), ⁅x, y⁆ = z})
    (θ : L ≃ₗ⁅ℚ⁆ L) (hθsq : ∀ z : L, θ (θ z) = z)
    (hθH : ∀ h : H, θ (h : L) = -(h : L))
    (hθroot : ∀ (i : I) (z : L), z ∈ LieModule.weightSpace L (P.root i) →
      θ z ∈ LieModule.weightSpace L (-P.root i))
    (i j k : I) (hadd : P.root k = P.root i + P.root j)
    (u v : L) (hu : u ∈ LieModule.weightSpace L (P.root i))
    (hv : v ∈ LieModule.weightSpace L (P.root j))
    (hunorm : ⁅u, -θ u⁆ = (P.coroot i : L))
    (hvnorm : ⁅v, -θ v⁆ = (P.coroot j : L)) :
    ⁅⁅u, v⁆, -θ ⁅u, v⁆⁆ = (((P.chainBotCoeff i j : ℚ) + 1) ^ 2) • (P.coroot k : L) ∧
      ⁅u, v⁆ ≠ 0 := by
  sorry

end LieAlgebra
