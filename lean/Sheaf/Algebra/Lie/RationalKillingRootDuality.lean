module

public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Algebra.Lie.TraceForm
public import Mathlib.Algebra.Lie.Weights.Basic
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Killing duality for a split rational root decomposition

Source: Milne, Algebraic Groups (2017), Section 23h, printed pp. 503 and 508;
the explicit Killing-duality calculation supporting Theorem 23.71
(blueprint: lem-sfb-rational-killing-root-duality).
-/

@[expose] public section

universe u

namespace LieAlgebra

open Classical in
/-- Killing duality for the explicit split rational decomposition of Milne, Algebraic Groups,
Section 23h, printed pp. 503 and 508 (blueprint: lem-sfb-rational-killing-root-duality).
The finite root set is indexed by its own elements. `P` records its reduced crystallographic
root-system structure, with the ordinary evaluation pairing, inclusion of roots, and the given
coroots. The internal sum of the simultaneous eigenspaces states diagonal action over Q.

Proof plan:
1. In a basis, exchanging the two matrix indices proves cyclicity of ordinary trace and hence
symmetry and bilinearity of B, using def-weil-endomorphism-trace and def-wf-lie-algebra.
2. Jacobi gives ad([x,y]) = ad(x)ad(y) - ad(y)ad(x). Cyclicity of trace then proves invariance.
3. Use a basis of H together with one vector in each root space. The trace on H is
B(h,k) = sum over roots rho of rho(h)rho(k), so B(h,h) is a sum of rational squares.
4. If all roots vanish on h, the decomposition implies h is central. Its rational span is a
solvable ideal and vanishes by semisimplicity (def-wf-semisimple-lie-algebra). Thus a nonzero h
has a strictly positive square in the sum, and B restricted to H is positive definite.
5. Apply lem-sfb-finite-dimensional-perfect-pairing to this restriction. Its inverse is the
linear map t; this gives existence and uniqueness and the symmetric positive definite form b.
6. Jacobi puts an opposite-root bracket in the common zero eigenspace, which is H. Invariance
identifies its pairing with h as rho(h)B(x,y); nondegeneracy gives [x,y] = B(x,y)t(rho).
7. Thus the bracket span is in Q t(rho). Evaluating rho on its normalized coroot gives
h_rho = (2 / b(rho,rho)) t(rho), with b(rho,rho) strictly positive by step 5.
8. Duality gives lambda(h_rho) = 2 b(lambda,rho) / b(rho,rho). Expanding both reflection
arguments by bilinearity cancels the three correction terms, proving invariance of b. -/
theorem rational_killing_root_duality
    (L : Type u) [LieRing L] [LieAlgebra ℚ L] [FiniteDimensional ℚ L]
    [HasTrivialRadical ℚ L] (H : LieSubalgebra ℚ L) [IsLieAbelian H]
    (hmax : ∀ K : LieSubalgebra ℚ L, H ≤ K → IsLieAbelian K → K = H)
    (R : Finset (Module.Dual ℚ H))
    (P : RootPairing R ℚ (Module.Dual ℚ H) H)
    [P.IsRootSystem] [P.IsReduced] [P.IsCrystallographic]
    (hpair : ∀ (ℓ : Module.Dual ℚ H) (h : H), P.toLinearMap ℓ h = ℓ h)
    (hroot : ∀ ρ : R, P.root ρ = ρ.val)
    (hsplit : DirectSum.IsInternal (fun i : Option R ↦
      match i with
      | none => H.toSubmodule
      | some ρ => (LieModule.weightSpace L (fun h : H ↦ ρ.val h)).toSubmodule))
    (hdim : ∀ ρ : R,
      Module.finrank ℚ (LieModule.weightSpace L (fun h : H ↦ ρ.val h)) = 1)
    (hbracket : ∀ ρ : R,
      Submodule.span ℚ {z : L | ∃ x ∈ LieModule.weightSpace L (fun h : H ↦ ρ.val h),
        ∃ y ∈ LieModule.weightSpace L (fun h : H ↦ -ρ.val h), ⁅x, y⁆ = z} ≤
          H.toSubmodule)
    (hcoroot : ∀ ρ : R, (P.coroot ρ : L) ∈
      Submodule.span ℚ {z : L | ∃ x ∈ LieModule.weightSpace L (fun h : H ↦ ρ.val h),
        ∃ y ∈ LieModule.weightSpace L (fun h : H ↦ -ρ.val h), ⁅x, y⁆ = z}) :
    LinearMap.IsSymm (killingForm ℚ L) ∧
    (∀ x y z : L, killingForm ℚ L ⁅x, y⁆ z = killingForm ℚ L x ⁅y, z⁆) ∧
    (∀ h : H, h ≠ 0 → 0 < killingForm ℚ L h h) ∧
    ∃ (t : Module.Dual ℚ H →ₗ[ℚ] H)
      (b : LinearMap.BilinForm ℚ (Module.Dual ℚ H)),
      (∀ ℓ : Module.Dual ℚ H,
        (∀ h : H, killingForm ℚ L (t ℓ) h = ℓ h) ∧
        ∀ v : H, (∀ h : H, killingForm ℚ L v h = ℓ h) → v = t ℓ) ∧
      (∀ ℓ μ : Module.Dual ℚ H, b ℓ μ = killingForm ℚ L (t ℓ) (t μ)) ∧
      LinearMap.IsSymm b ∧
      (∀ ℓ : Module.Dual ℚ H, ℓ ≠ 0 → 0 < b ℓ ℓ) ∧
      (∀ (ρ : R) (ℓ μ : Module.Dual ℚ H),
        b (ℓ - ℓ (P.coroot ρ) • ρ.val) (μ - μ (P.coroot ρ) • ρ.val) = b ℓ μ) ∧
      ∀ ρ : R, 0 < b ρ.val ρ.val ∧
        P.coroot ρ = (2 / b ρ.val ρ.val) • t ρ.val ∧
        ∀ (x y : L), x ∈ LieModule.weightSpace L (fun h : H ↦ ρ.val h) →
          y ∈ LieModule.weightSpace L (fun h : H ↦ -ρ.val h) →
          ⁅x, y⁆ = killingForm ℚ L x y • (t ρ.val : L) := by
  sorry

end LieAlgebra
