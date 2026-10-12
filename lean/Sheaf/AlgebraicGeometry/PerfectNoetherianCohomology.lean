/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.CoherentModuleLocalOnOpenCover

/-! # Bounded coherent cohomology of perfect complexes

Source: Stacks Project, Derived Categories of Schemes, Tag 0FXU, part (1).
(blueprint: lem-pc-perfect-noetherian-cohomology).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A perfect complex on a Noetherian scheme has bounded coherent cohomology.
Source: Stacks Project, Derived Categories of Schemes, Lemma
`perfect-lemma-perfect-on-noetherian`, Tag 0FXU, part (1).

Proof: choose strictly perfect neighbourhoods from `IsPerfect`. Refine them by affine
opens and then by opens where the finite projective terms become finite free. On these
opens the kernels and images of the matrices are finite modules over Noetherian rings;
their quotients are finite as well. Their associated sheaves are therefore coherent,
and exact restriction identifies them with the restrictions of the cohomology of E.
Coherence is local, so all cohomology sheaves of E are coherent. Each bounded local
model has zero cohomology outside its term bounds. Quasi-compactness selects a finite
subcover; take the minimum of its lower bounds and maximum of its upper bounds.
Outside that interval every restriction of the cohomology sheaf is zero, so the sheaf
itself is zero. On the empty scheme all sheaves are zero; use bounds 0 and 0.
(blueprint: lem-pc-perfect-noetherian-cohomology). -/
theorem perfect_bounded_coherent_cohomology (X : Scheme.{u}) [IsNoetherian X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) (hE : IsPerfect X E) :
    (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E)) ∧
    (∀ i : ℤ, RingedSpace.IsCoherent X.toRingedSpace
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E)) := by sorry

end AlgebraicGeometry.Scheme
