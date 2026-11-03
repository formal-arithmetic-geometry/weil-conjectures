/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PointTensorReduction.CondensedPointTensorReduction
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic

/-! # Native tensor data at integral and finite coefficient points

Source: the finite-reduction compatibility clause of the relative product theorem,
`sec-six-functors/sk-thm-sf-kunneth-relative/_section.md`.
(blueprint: lem-sf-native-integral-point-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 20000]
  CategoryTheory.InternalAbelianSheafModule.comparison_essentiallySmall
attribute [local instance 10000] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj TensorProduct ChangeOfRings
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.CondensedRing.PointTensorReduction

/-- The integral point and all its positive finite quotients have native point tensor data.

Source: `lem-sf-point-ringed-evaluation-model`, tensor and derived fields;
`lem-pe-internal-section-tensor-comparison`; relative product theorem, Step 5.
(blueprint: lem-sf-native-integral-point-tensor).

Proof: Apply the ringed-point evaluation theorem to the reconstructed coefficient-ring
sheaf for O_E and each O_E/pi^(n+1). Compose its exact section functor with the exact
internal-to-section module equivalence and restriction along the canonical singleton
ring isomorphism. The internal section-tensor comparison and the point total-tensor
comparison give a chain isomorphism b. Its inverse on the (i,j) summand sends x tensor y
to the native internal section tensor, since these are the two specified ordinary
balanced comparisons; no summands or variables are permuted. Sections preserve the
resolving flat-term K-flat models. Localize b and use the universal derived-bifunctor
comparison to obtain tensorIso on the constructible finite-Tor objects. The localization
square is precisely NativePointTensor. The ordinary coefficient evaluation identifies
the unit in degree zero; localizing its single-complex comparison proves the unit
normalization. The signed associator and braiding and the two unitors commute before
localization by the ringed-point theorem and internal tensor comparison. Their derived
universal properties preserve those equalities, giving all PointData fields. Make this
same normalized construction for each quotient; the choices are pinned by their
representative equations and hence do not introduce an arbitrary tensorator. -/
theorem native_integral_point_tensor
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hℓ : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span ({π} : Set (PadicAlgCl.integers ell E)) =
      IsLocalRing.maximalIdeal (PadicAlgCl.integers ell E)) :
    ∃ source : PointData (integralCoefficient.{u} ell E) D.k,
      NativePointTensor (integralCoefficient.{u} ell E) D.k source ∧
      ∃ target : ∀ n : ℕ, PointData (finiteCoefficient.{u} ell E π n) D.k,
        ∀ n : ℕ, NativePointTensor (finiteCoefficient.{u} ell E π n) D.k (target n) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.PointTensorReduction
