/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.WeilSheafComplex
public import WeilConjectures.SmoothPurity.GlobalGeometricFrobenius.CondensedGlobalGeometricFrobenius
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedDerived.CondensedScalarDerivedLocalFrobenius
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Complex.Basic
public import Mathlib.Order.KrullDimension
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedComplexLocalFrobeniusPowers

/-! # Native rational-point traces for the Euler product
Source: Euler-product proof Step 3, before grouping the rational points.
(blueprint: def-condensed-weil-euler-rational-traces).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedWeilEuler
open NativeCondensedModule

variable (D : FiniteFieldDatum.{u})
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- The canonical geometric lift respects the structural map.
Source: Euler-product Step 3, the lift of a rational point.
Proof: compose the over-morphism equation with the subfield inclusion; the specified
extension embedding composes to the original base-field embedding.
(blueprint: def-condensed-weil-euler-rational-traces). -/
theorem eulerExtensionPoint_square (m : ℕ) (hm : 1 ≤ m)
    (y : D.extensionPoints X₀ m hm) :
    (Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype) ≫ y.left) ≫
        X₀.hom =
      (𝟙 (Spec (.of D.k))) ≫ Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
  rw [Category.assoc, Over.w y, Category.id_comp]
  change Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype) ≫
    Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime
    D.exponent_pos D.cardinality_eq D.k₀ D.card_base D.k m hm).choose_spec.2.2.2.2.2.2.choose_spec

/-- The geometric lift is the actual pullback lift, with identity second projection.
Source: Euler-product Step 3 (blueprint: def-condensed-weil-euler-rational-traces). -/
def eulerExtensionPoint (m : ℕ) (hm : 1 ≤ m) (y : D.extensionPoints X₀ m hm) :
    Spec (.of D.k) ⟶ (D.geometricFiber X₀).left :=
  pullback.lift (Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype) ≫ y.left)
    (𝟙 _) (eulerExtensionPoint_square D X₀ m hm y)

variable (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
  (c : WeilCoefficient ell) (K : strictWeilComplexCategory D ell hEll X₀ c)

/-- Scalar stalk cohomology at an arbitrary geometric lift.
Source: Euler-product Step 1 (blueprint: def-condensed-weil-euler-rational-traces). -/
abbrev eulerPointCohomology
    (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left) (j : ℤ) :=
  (ModuleCat.restrictScalars (scalarMap c)).obj
    ((NativeCondensedDerived.cohomology (WeilCoefficient.ab c) j).obj
      (NativeCondensedDerived.stalk (WeilCoefficient.ab c) D K.obj.carrier z))

/-- Ordinary scalar trace of the specified semilinear return.
Source: Euler-product Step 3 (blueprint: def-condensed-weil-euler-rational-traces). -/
def eulerPointTrace (z : Spec (.of D.k) ⟶ (D.geometricFiber X₀).left)
    (m : ℕ) (hv : scalarLocalReturn D X₀ z m) (j : ℤ) : Scalar c :=
  LinearMap.trace (Scalar c) (eulerPointCohomology D X₀ ell hEll c K z j)
    ((ModuleCat.restrictScalars (scalarMap c)).map
      ((NativeCondensedDerived.cohomology (WeilCoefficient.ab c) j).map
        (NativeCondensedDerived.operator (WeilCoefficient.ab c) D
          (D.geometricFrobenius X₀).hom K.obj.carrier K.obj.str z (m - 1) hv))).hom

variable [IsSeparated X₀.hom] (c₀ : Compactification (D.geometricFiber X₀).hom)

/-- Ordinary scalar trace of a power of global geometric Frobenius.
Source: Euler-product Step 3 (blueprint: def-condensed-weil-euler-rational-traces). -/
abbrev eulerCompactTrace (m : ℕ) (j : ℤ) : Scalar c :=
  LinearMap.trace (Scalar c) (compactCohomology D ell hEll X₀ c K c₀ j)
    ((compactOperator D ell hEll X₀ c K c₀ j).hom ^ m)

end WeilConjectures.CondensedWeilEuler
