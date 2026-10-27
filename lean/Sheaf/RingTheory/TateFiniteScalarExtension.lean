module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Finite scalar extension of Tate algebras

Source: Conrad, Several approaches to non-archimedean geometry, Definition 1.1.2
and Exercise 2.2.3(3); finite-degree ordinary-tensor specialization
(blueprint: lem-per-tate-finite-scalar-extension).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v w

open scoped TensorProduct

namespace RestrictedSeries

/-- The scalar algebra structure is given by the existing constant-series ring map.
Source: Conrad, Definition 1.1.2 (blueprint: lem-per-tate-finite-scalar-extension). -/
noncomputable instance constantsAlgebra
    (R : Type u) [NormedCommRing R] [IsUltrametricDist R] (r : ℕ) :
    Algebra R ↥(MvPowerSeries.IsRestricted.subring (R := R) (fun _ : Fin r ↦ (1 : ℝ))) :=
  (constants R r).toAlgebra

/-- Finite isometric coefficient extension is ordinary algebraic tensor extension.
The coefficient equations specify the canonical inclusion uniquely; the pure-tensor
formula specifies the L-algebra equivalence uniquely. The tensor has the ordinary
right-factor L-algebra structure, supplied explicitly to avoid ambiguous instances.

Source: Conrad, Definition 1.1.2 and Exercise 2.2.3(3), finite-degree specialization
(blueprint: lem-per-tate-finite-scalar-extension).

Proof (agent reconstruction recorded in the node).
1. For any K-basis of L, the coordinate projections are continuous by
lem-sfb-finite-dimensional-linear-map-continuous. The norm bound of
lem-trf-continuous-linear-map-norm-bound gives positive bounds C_j.
2. Apply each coordinate projection coefficientwise. Its bound shows the resulting
series is restricted, using the finite exceptional set at epsilon/C_j. Isometry
preserves restrictedness under coefficient inclusion. Coefficientwise expansion and
independence give a basis by constant series; finite Cauchy sums show module linearity.
3. Tensor bilinearity (def-weil-pbc-module-tensor-product) gives the displayed map.
Its inverse sends a series with coordinate series f_j to the finite sum of f_j tensor e_j.
Expansion gives one composite; the coordinate formula on pure tensors gives the other.
4. On pure tensors the formula preserves multiplication and one. Tensor generation
extends this to every tensor, and multiplication by constants gives L-linearity.
5. For an injective A-linear map N to P, the constant basis identifies tensoring with
T_r(L) with the coordinatewise map N^d to P^d, which is injective. Thus the coefficient
map is flat (def-weil-pbc-flat-ring-map). With r=0 the same argument is K tensor L = L.
No step uses separability, a trace pairing, or completion of the tensor product.
-/
theorem tate_finite_scalar_extension
    (K : Type u) (L : Type v)
    [NontriviallyNormedField K] [NontriviallyNormedField L]
    [IsUltrametricDist K] [IsUltrametricDist L]
    [CompleteSpace K] [CompleteSpace L] [Algebra K L] [FiniteDimensional K L]
    (hι : Isometry (algebraMap K L)) (r : ℕ) :
    ∃ φ : ↥(MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ))) →+*
        ↥(MvPowerSeries.IsRestricted.subring (R := L) (fun _ : Fin r ↦ (1 : ℝ))),
      (∀ f ν, MvPowerSeries.coeff ν (φ f).val =
        algebraMap K L (MvPowerSeries.coeff ν f.val)) ∧
      (∃ e : @AlgEquiv L
          (↥(MvPowerSeries.IsRestricted.subring
            (R := K) (fun _ : Fin r ↦ (1 : ℝ))) ⊗[K] L)
          ↥(MvPowerSeries.IsRestricted.subring (R := L) (fun _ : Fin r ↦ (1 : ℝ)))
          inferInstance inferInstance inferInstance
          (Algebra.TensorProduct.rightAlgebra (R := K)) inferInstance,
        ∀ f c, e (f ⊗ₜ[K] c) = constants L r c * φ f) ∧
      (∀ (ι : Type w) (b : Module.Basis ι K L),
        ∃ bT : @Module.Basis ι
          ↥(MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ)))
          ↥(MvPowerSeries.IsRestricted.subring (R := L) (fun _ : Fin r ↦ (1 : ℝ)))
          inferInstance inferInstance φ.toAlgebra.toModule,
          ∀ i, bT i = constants L r (b i)) ∧
      φ.Flat := by
  sorry

end RestrictedSeries
