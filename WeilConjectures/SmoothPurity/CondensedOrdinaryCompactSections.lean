/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CommonStageCompactWeilCohomology
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek

/-! # Ordinary derived sections for native condensed Qbar coefficients

Source: latest blueprint, sec-six-functors-basics/sk-thm-existence/
def-weil-ordinary-compact-cohomology.md, the displayed RΓ and RΓ_c formulas
(blueprint: def-weil-ordinary-compact-cohomology).

The existing general condensed-ring and older coefficient interfaces remain public.
## Main definitions

`condensedQbarDerivedPointSections` is exact derived geometric evaluation.
`condensedQbarOrdinarySections` and `condensedQbarCompactSections` give the
ordinary and compact-support coefficient complexes in fixed Qbar coordinates.

This specialization accepts every native condensed-module complex, rather than
requiring an object to descend from the finite-stage adic encoding.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace WeilConjectures

/-- Derived geometric-point evaluation, with coefficient ring exactly Qbar_ell.
Source: the node's compact-cohomology convention
(blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev condensedQbarDerivedPointSections (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [IsAlgClosed k] :=
  (ProEtale.CondensedQbarGeometricEvaluation.fieldFiber k ell).mapDerivedCategory

/-- Compact support is exact open extension, then proper derived image, then point sections.
Source: the node's displayed formula RΓ_c(Y,K) = Fib_s(Ra_! K)
(blueprint: def-weil-ordinary-compact-cohomology). -/
abbrev condensedQbarCompactSections (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} {a : X ⟶ Spec (.of k)} (c : Compactification a) :=
  ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification
    (Profinite.padicAlgClRingObj ell) c ⋙ condensedQbarDerivedPointSections ell k

end WeilConjectures
