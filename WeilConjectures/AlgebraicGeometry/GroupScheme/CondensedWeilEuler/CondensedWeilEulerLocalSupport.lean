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

/-! # A common finite range for all scalar stalk cohomology
Source: the exact-stalk argument in Euler-product proof Step 1.
(blueprint: lem-condensed-weil-euler-local-support).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedWeilEuler
open WeilConjectures.NativeCondensedModule

/-- The finite cohomological interval of a strict Weil complex bounds every scalar stalk.
Source: Euler-product proof Step 1, exactness of stalk pullback and point sections.
Proof: choose a bounded interval for the underlying complex. Outside this interval its
homology vanishes. Exact pullback and exact sections commute with homology, so the same
vanishing holds at every geometric point. Restriction of scalars preserves zero objects.
This also handles empty schemes and intervals and negative cohomological degrees.
(blueprint: lem-condensed-weil-euler-local-support). -/
theorem eulerLocalSupport
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (c : WeilCoefficient ell) (K : strictWeilComplexCategory D ell hEll X₀ c)
    (iota : ∀ x : ClosedPoint D X₀, X₀.left.residueField x.val →+* D.k)
    (hiota : ∀ x, (iota x).comp (X₀.hom.residueFieldAlgebraMap x.val) =
      algebraMap D.k₀ D.k) :
    ∃ S : Finset ℤ, ∀ x j, j ∉ S →
      IsZero (localCohomology D ell hEll X₀ c K x (iota x) (hiota x) j) := by
  classical
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  obtain ⟨a, b, ha, hb⟩ :=
    (DerivedCategory.exists_homologyConcentratedIn_iff_bounded K.obj.carrier).2 K.property.1
  refine ⟨Finset.Icc a b, ?_⟩
  intro x j hj
  have hzero : IsZero ((DerivedCategory.homologyFunctor _ j).obj K.obj.carrier) := by
    by_cases hja : j < a
    · exact (DerivedCategory.isGE_iff _ a).1 ha j hja
    · exact (DerivedCategory.isLE_iff _ b).1 hb j (by
        simp only [Finset.mem_Icc] at hj
        omega)
  have hpull := (CondensedRing.upperStar (WeilCoefficient.ab c)
    (localClosedPoint D X₀ x (iota x) (hiota x))).isZero_homologyFunctor_mapDerivedCategory_obj
      hzero
  have hsections := Functor.isZero_homologyFunctor_mapDerivedCategory_obj
    (NativeCondensedPoint.sections (WeilCoefficient.ab c) D.k) hpull
  exact (ModuleCat.restrictScalars (scalarMap c)).map_isZero hsections

end WeilConjectures.CondensedWeilEuler
