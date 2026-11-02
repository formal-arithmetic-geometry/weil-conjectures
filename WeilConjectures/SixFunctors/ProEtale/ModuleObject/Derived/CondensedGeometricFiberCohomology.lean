/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull

/-!
# Geometric-fibre scalar evaluation and unevaluated coefficient cohomology

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/
sk-def-ops/_section.md,
finite-base geometric-fibre scalar convention and unevaluated `RΓ`/`RΓ_c` clauses of the
node `sk-def-ops` (blueprint: sk-def-sfb-geometric-fiber-cohomology).

The unevaluated objects `\mathcal RΓ(X,K) = Ra_{X*}K` and `\mathcal RΓ_c(X,K) = Ra_{X!}K` stay
in the derived category over the base.  The scalar evaluation `Fib_s` is the derived
coefficient-module pullback along an explicitly chosen geometric point `b : Spec K ⟶ Spec k`
with `K` algebraically closed, followed by the actual terminal sections over `Spec K`, which are
exact there (`lem-weil-point-proetale-sections-exact`).  For finite `k` take
`K = AlgebraicClosure k`; for algebraically closed `k` take `b = 𝟙 _`.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.MonObj
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The unevaluated ordinary derived direct image `\mathcal RΓ(X,K) = Ra_{X*}K`, the total
derived pushforward on actual condensed module objects.
Source: `sk-def-ops/_section.md`, unevaluated `RΓ` clause of the finite-base convention
(blueprint: sk-def-sfb-geometric-fiber-cohomology). -/
def geometricFiberUnevaluatedOrdinary
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (a : X ⟶ S) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S)) :=
  moduleObjectDerivedPushforward Λ a

/-- The unevaluated compactly supported derived image `\mathcal RΓ_c(X,K) = Ra_{X!}K`.
The compactification is explicit.
Source: `sk-def-ops/_section.md`, unevaluated `RΓ_c` clause of the finite-base convention
(blueprint: sk-def-sfb-geometric-fiber-cohomology). -/
def geometricFiberUnevaluatedCompact
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} {a : X ⟶ S}
    (c : Compactification a) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S)) :=
  rightDerivedLowerShriekOfCompactification Λ c

/-- Geometric-fibre scalar evaluation at a chosen algebraically closed point
`b : Spec K ⟶ Spec k`.  The inverse-image part is the total derived coefficient-module
pullback, followed by actual terminal sections on `Spec K`.
Source: `sk-def-ops/_section.md`, `Fib_s = Γ(\bar s, b^*(-))` for finite `k`
(blueprint: sk-def-sfb-geometric-fiber-cohomology). -/
def geometricFiberScalarEvaluation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {k K : Type u} [Field k] [Field K] [IsAlgClosed K]
    (b : Spec (.of K) ⟶ Spec (.of k)) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of k)))) ⥤
    DerivedCategory (ModuleCat.{u + 1} (Γ Λ)) :=
  moduleObjectDerivedPullback Λ b ⋙
    (condensedRingCoefficientSections Λ (Spec (.of K))).rightDerivedFunctor

/-- The geometric-fibre scalar ordinary cohomology complex, obtained by applying
`geometricFiberScalarEvaluation` to the unevaluated `Ra_*`.
Source: `sk-def-ops/_section.md`, `RΓ(X,K) = Fib_s(Ra_{X*}K)`
(blueprint: sk-def-sfb-geometric-fiber-cohomology). -/
def geometricFiberOrdinaryCoefficientComplex
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {k K : Type u} [Field k] [Field K] [IsAlgClosed K]
    (b : Spec (.of K) ⟶ Spec (.of k)) {X : Scheme.{u}}
    (a : X ⟶ Spec (.of k)) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ⥤
    DerivedCategory (ModuleCat.{u + 1} (Γ Λ)) :=
  geometricFiberUnevaluatedOrdinary Λ a ⋙ geometricFiberScalarEvaluation Λ b

/-- The geometric-fibre scalar compactly supported cohomology complex, obtained by
applying `geometricFiberScalarEvaluation` to the unevaluated `Ra_!`.
Source: `sk-def-ops/_section.md`, `RΓ_c(X,K) = Fib_s(Ra_{X!}K)`
(blueprint: sk-def-sfb-geometric-fiber-cohomology). -/
def geometricFiberCompactCoefficientComplex
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {k K : Type u} [Field k] [Field K] [IsAlgClosed K]
    (b : Spec (.of K) ⟶ Spec (.of k)) {X : Scheme.{u}}
    {a : X ⟶ Spec (.of k)} (c : Compactification a) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ⥤
    DerivedCategory (ModuleCat.{u + 1} (Γ Λ)) :=
  geometricFiberUnevaluatedCompact Λ c ⋙ geometricFiberScalarEvaluation Λ b

end AlgebraicGeometry.ProEtale.CondensedRing
