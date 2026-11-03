/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaWeil.FiniteTraceGlobalOperator
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback

/-! # The global correspondence operator is triangulated in the coefficient

Source: latest blueprint, literature/blueprint/latest/blueprint/
part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sec-additivity-of-trace-classes/
sk-i-additivity/lem-trf-global-operator-triangulated.md
(blueprint: lem-trf-global-operator-triangulated).

The scheme correspondence `C`, `c₁`, `c₂` is fixed. A distinguished triangle
`K' → K → K'' → K'[1]` of `D^b_ctf(X, A)` is a triangle of objects of the full
subcategory whose image in the ambient derived category is distinguished (the finite-Tor
category is a full triangulated subcategory). The image triangle of `Lc₂^*` uses the
existing shift of the ambient derived pullback. The image triangle of `Rc₁^!` uses the
shift of the specified exceptional inverse image as the right adjoint, in the specified
adjunction, of the shift-commuting restricted compact-support functor; this is the shift
for which the exceptional counit commutes with shifts. `RΓ_c(X, -)` has the composite
shift of `Ra_{X!}` and the point fibre.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
-- As in Sheaf.Paper.FiniteTraceGlobalOperator: the instance of FinitePointSectionsExact is not
-- re-exported through its private import; the same instance at the same priority.
attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian
universe u
open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.MonObj AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures.FiniteTraceFormulaConventions

/-- The canonical shift of the point fibre `Fib_s`: the composite of the shift of the
K-injective right derived section functor and that of the functor induced by exact scalar
restriction. No other shift is chosen.
Source: latest blueprint lem-trf-global-operator-triangulated, proof step 1
(blueprint: lem-trf-global-operator-triangulated). -/
instance pointFiberCommShift (T : FiniteTraceFormulaConventions.{u}) :
    T.pointFiber.CommShift ℤ :=
  inferInstanceAs (((condensedRingCoefficientSections T.coefficients
    (Spec (.of T.datum.k))).rightDerivedFunctor ⋙
      (ModuleCat.restrictScalars T.constantScalars :
        ModuleCat.{u + 1} (Γ T.coefficients) ⥤
          ModuleCat.{u + 1} (ULift.{u + 1} T.A)).mapDerivedCategory).CommShift ℤ)

/-- The canonical shift of `RΓ_c = Fib_s ∘ Ra_!`: the composite of the shift of the
compact-support functor of the compactification and the shift of `Fib_s`.
Source: latest blueprint lem-trf-global-operator-triangulated, proof step 1
(blueprint: lem-trf-global-operator-triangulated). -/
instance operatorCompactSupportCommShift (T : FiniteTraceFormulaConventions.{u})
    {Y : Scheme.{u}} {a : Y ⟶ Spec (.of T.datum.k)} (d : Compactification a) :
    (T.operatorCompactSupport d).CommShift ℤ :=
  inferInstanceAs
    ((rightDerivedLowerShriekOfCompactification T.coefficients d ⋙ T.pointFiber).CommShift ℤ)

end WeilConjectures.FiniteTraceFormulaConventions

namespace WeilConjectures

set_option maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
end WeilConjectures
