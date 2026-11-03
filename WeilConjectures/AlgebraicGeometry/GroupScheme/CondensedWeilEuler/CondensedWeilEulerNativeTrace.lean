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
public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedWeilEuler.CondensedWeilEulerRationalTraceDefs
import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedWeilEuler.CondensedWeilEulerScalarTrace
/-! # Scalar traces of the native one-circuit powers
Source: Euler-product proof Step 1, local powers and Step 3.
(blueprint: lem-condensed-weil-euler-native-trace).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open CondensedRing
open scoped CategoryTheory.Obj
namespace WeilConjectures.CondensedWeilEuler
open NativeCondensedModule
variable (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p)
  (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  (c : WeilCoefficient ell) (K : strictWeilComplexCategory D ell hEll X₀ c)
  [IsSeparated X₀.hom]

set_option maxHeartbeats 2000000 in
-- Elaborating the nested derived cohomology and scalar-restriction functors exceeds the default.
/-- The native return trace is the scalar image of the one-circuit power trace.
Source: Euler-product proof Step 1, local powers, and Step 3.
Proof: the existing local power theorem identifies the return trace with the trace
of a power on the chosen closed-point stalk. Restriction along the constant-section
ring isomorphism preserves trace, and homology preserves endomorphism powers.
The argument includes zero spaces and the degree-one case.
(blueprint: lem-condensed-weil-euler-native-trace). -/
theorem nativeLocalTrace (x : ClosedPoint D X₀)
    (iota : X₀.left.residueField x.val →+* D.k)
    (hiota : iota.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (hfinite : ∀ j, Module.Finite (Scalar c)
      (localCohomology D ell hEll X₀ c K x iota hiota j))
    (m : ℕ) (hm : 1 ≤ m) (hd : localClosedPointDegree D X₀ x ∣ m)
    (y : D.extensionPoints X₀ m hm)
    (hy : y.left (IsLocalRing.closedPoint _) = x.val) :
    ∃ hv : scalarLocalReturn D X₀ (eulerExtensionPoint D X₀ m hm y) m,
      ∀ j : ℤ,
      LinearMap.trace (MonObj.Γ (WeilCoefficient.ab c))
        ((NativeCondensedDerived.cohomology (WeilCoefficient.ab c) j).obj
          (NativeCondensedDerived.stalk (WeilCoefficient.ab c) D K.obj.carrier
            (eulerExtensionPoint D X₀ m hm y)))
        ((NativeCondensedDerived.cohomology (WeilCoefficient.ab c) j).map
          (NativeCondensedDerived.operator (WeilCoefficient.ab c) D
            (D.geometricFrobenius X₀).hom K.obj.carrier K.obj.str
            (eulerExtensionPoint D X₀ m hm y) (m - 1) hv)).hom =
      scalarMap c (LinearMap.trace (Scalar c)
        (localCohomology D ell hEll X₀ c K x iota hiota j)
        ((localOperator D ell hEll X₀ c K x iota hiota j).hom ^
          (m / localClosedPointDegree D X₀ x))) := by
  classical
  let z := localClosedPoint D X₀ x iota hiota
  have hz : (z ≫ pullback.fst X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
      (IsLocalRing.closedPoint D.k) = x.val := by
    dsimp only [z, localClosedPoint]
    rw [pullback.lift_fst]
    exact X₀.left.fromSpecResidueField_apply x.val _
  obtain ⟨hz', hw', _, hp⟩ := condensedComplex_localFrobenius_powers
    D ell hEll c X₀ K.obj.carrier K.property K.obj.str x z z hz hz
  obtain ⟨hv, htrace⟩ := hp m hm hd y hy (Iso.refl _)
    (eulerExtensionPoint D X₀ m hm y)
    (by simp [eulerExtensionPoint])
    (by simp [eulerExtensionPoint])
  refine ⟨hv, ?_⟩
  intro j
  rw [htrace j]
  let H := NativeCondensedDerived.cohomology (WeilCoefficient.ab c) j
  let f := NativeCondensedDerived.operator (WeilCoefficient.ab c) D
    (D.geometricFrobenius X₀).hom K.obj.carrier K.obj.str z
    (localClosedPointDegree D X₀ x - 1) hz'
  let M := H.obj (NativeCondensedDerived.stalk (WeilCoefficient.ab c) D K.obj.carrier z)
  have : Module.Finite (MonObj.Γ (WeilCoefficient.ab c)) M :=
    (scalarFinite_iff c M).mp (hfinite j)
  have h := scalarTrace_restrict_pow c M (End.of (H.map f))
    (m / localClosedPointDegree D X₀ x)
  have hmappow : H.map (f ^ (m / localClosedPointDegree D X₀ x)) =
      (End.of (H.map f)) ^ (m / localClosedPointDegree D X₀ x) :=
    map_pow (Functor.mapEnd _ H) _ _
  have hhom : ((End.of (H.map f)) ^ (m / localClosedPointDegree D X₀ x)).hom =
      (H.map f).hom ^ (m / localClosedPointDegree D X₀ x) :=
    map_pow (ModuleCat.endRingEquiv M).toMonoidHom _
      (m / localClosedPointDegree D X₀ x)
  change LinearMap.trace _ M (H.map (f ^ _)).hom = _
  rw [hmappow]
  exact (congrArg (LinearMap.trace _ M) hhom).trans h.symm

end WeilConjectures.CondensedWeilEuler
