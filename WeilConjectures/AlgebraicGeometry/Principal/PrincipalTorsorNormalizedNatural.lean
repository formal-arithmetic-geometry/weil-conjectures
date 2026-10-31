/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PrincipalTorsorComparisons.PrincipalTorsorSignTypes
/-! Independent comparison result for the principal torsor sign calculation. -/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite HomologicalComplex
namespace AlgebraicGeometry.Etale
/-- Cocycle-normalized supported-Hom comparisons are natural in coefficient lifts and
etale restriction.
Source: Stacks 03AJ, 0G78; representative naturality in the principal-torsor sign node.
Proof: express each Ext class as extMk of a closed resolution cocycle. A coefficient lift
sends it to extMk of the composite cocycle. The normalization and coefficient-representative
transport theorem give identical signed coordinates for the two classes. For etale restriction,
the stipulated evaluated-cocycle equation and restriction-representative transport likewise
give identical coordinates. Signed coordinates determine a cycle, hence its homology class,
by the degreewise cone decomposition and the monomorphism of cycles into the complex.
(blueprint: lem-pur-principal-torsor-normalized-natural). -/
theorem principalTorsorNormalizedNatural
    (C : PrincipalTorsorComparisons.{u}) (hC : C.Normalized) : C.Natural := by sorry
end AlgebraicGeometry.Etale
