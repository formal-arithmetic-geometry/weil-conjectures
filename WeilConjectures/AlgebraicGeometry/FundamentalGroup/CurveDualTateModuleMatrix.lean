/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.Dual
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.CurveDualTateModule

/-!
# The matrix of the geometric Frobenius on the dual Tate module

Let `C₀` be a proper smooth geometrically integral curve over a finite field `K` with Jacobian
`J`, and `ℓ ≠ char K` a prime. Under the identification
`lim_n H¹(C, ℤ/ℓⁿ) ≃ Hom_{ℤ_ℓ}(T_ℓ J, ℤ_ℓ)`
(`AlgebraicGeometry.Scheme.EtaleTorsor.sheafHOneLimitAddEquivDualJacobianTateModule`), the
geometric Frobenius of `C` acts on the left by pullback and, on the right, by precomposition with
the arithmetic Frobenius `x ↦ x ^ q` acting on `T_ℓ J`
(`AlgebraicGeometry.Scheme.EtaleTorsor.sheafHOneLimitAddEquivDualJacobianTateModule_galois`). So if
the arithmetic Frobenius has matrix `B` in a basis of `T_ℓ J`, then the geometric Frobenius has
matrix `Bᵀ` in the dual basis.

## Main statements

- `AlgebraicGeometry.Scheme.EtaleTorsor.exists_toMatrix_dualBasis_eq_transpose_frobenius`
  (blueprint `proposition-kummer-duality-integral-tate-module--3`).
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory Matrix MonoidalCategory CartesianMonoidalCategory
  MonObj

namespace AlgebraicGeometry.Scheme.EtaleTorsor

open FiniteEtale

variable {K : Type u} [Field K] [Fintype K] {C : Scheme.{u}} (p : C ⟶ Spec (.of K)) [IsCurve p]
  [Smooth p] [SmoothOfRelativeDimension 1 p] [IsProper p] [GeometricallyIntegral p] (l : ℕ)
  [Fact l.Prime] [Fact (ringChar K ≠ l)] [ConnectedSpace p.geometricFiber]

/-- Blueprint `proposition-kummer-duality-integral-tate-module--3`: if the arithmetic Frobenius
on `T_ℓ J` has matrix `B`, then the geometric Frobenius on `Hom_{ℤ_ℓ}(T_ℓ J, ℤ_ℓ)` has matrix `Bᵀ`
in the dual basis.

Let `b` be a basis of the Tate module `T_ℓ J` of the Jacobian (given by a Jacobian torsion datum
`d`), and `B` the matrix in `b` of the arithmetic Frobenius `σ : x ↦ x ^ q` of `Gal(K̄ / K)`,
acting on `T_ℓ J` by coordinates. The geometric Frobenius of `C` acts on `lim_n H¹(C, ℤ/ℓⁿ)`
by transport of torsors along `𝟙 × Spec σ`, that is, by pullback along the geometric Galois
Frobenius `𝟙 × Spec σ⁻¹`. There is an endomorphism `Φ` of `Hom_{ℤ_ℓ}(T_ℓ J, ℤ_ℓ)` through which
it acts under the identification
`AlgebraicGeometry.Scheme.EtaleTorsor.sheafHOneLimitAddEquivDualJacobianTateModule`, and the
matrix of `Φ` in the dual basis of `b` is `Bᵀ`. -/
theorem exists_toMatrix_dualBasis_eq_transpose_frobenius
    (s : Spec (.of (AlgebraicClosure K)) ⟶ p.geometricFiber) (G : Type u) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]
    (d : JacobianTorsionDatum p l) {κ : Type*} [Fintype κ] [DecidableEq κ]
    (b : Module.Basis κ ℤ_[l] (d.tateModule l)) :
    ∃ Φ : Module.Dual ℤ_[l] (d.tateModule l) →ₗ[ℤ_[l]] Module.Dual ℤ_[l] (d.tateModule l),
      (∀ x y : sheafHOneLimit p.geometricFiber l,
        (∀ n, y.1 n = mapIsoH1 p.geometricFiber _
          (p.geometricFiberGaloisIso (FiniteField.frobeniusAlgEquivOfAlgebraic K _)) (x.1 n)) →
        sheafHOneLimitAddEquivDualJacobianTateModule p l s G d y =
          Φ (sheafHOneLimitAddEquivDualJacobianTateModule p l s G d x)) ∧
      LinearMap.toMatrix b.dualBasis b.dualBasis Φ =
        (LinearMap.toMatrix b b (IsAbelianVariety.galoisRepresentation l d.J
          (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K))).toLinearMap)ᵀ :=
  ⟨Module.Dual.transpose (R := ℤ_[l]) (IsAbelianVariety.galoisRepresentation l d.J
      (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K))).toLinearMap,
    fun x y hxy ↦ sheafHOneLimitAddEquivDualJacobianTateModule_galois p l s G d _ x y hxy,
    LinearMap.toMatrix_transpose _⟩

end AlgebraicGeometry.Scheme.EtaleTorsor
