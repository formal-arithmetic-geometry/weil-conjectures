/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Dual

/-! # Dualizing finite free quotients

Source: Stacks Project, Tag 0EKP, the dual-surjection construction in (2) to (3).
(blueprint: new-sbc-quasi-affine-embedding-pullback)
-/

@[expose] public section

noncomputable section
universe u
set_option autoImplicit false
open CategoryTheory Limits SheafOfModules
namespace AlgebraicGeometry.Scheme.Modules

/-- The transpose of a finite free quotient of the dual of a vector bundle,
composed with biduality and the finite free dual comparison, is a universally
monic embedding with finite locally free cokernel.

Source: Stacks Project, Tag 0EKP, the dual-surjection construction in (2) to (3).
(blueprint: new-sbc-quasi-affine-embedding-pullback)

Proof: Near each point shrink to an affine open on which M is finite free.
The sheaf epimorphism β induces a surjection onto the finite free module of
sections of the dual there: the kernel is quasi-coherent, so the affine
sections functor is exact. Lift the standard basis to split this surjection.
Its kernel K is a finitely generated projective direct summand of the finite
free source. Shrinking further makes K finite free. Dualize the split sequence:
the map from the bidual of M to the dual of the free source is the inclusion
of a direct summand, with cokernel the dual of K. The displayed α is exactly
this map under biduality and homObjFreeUnitIso. Hence α is monic and its
categorical cokernel is finite locally free. For any g the inverse images of
these opens cover Y; pulling back a local left inverse preserves its identity
with α. The pulled-back map is monic on that cover, hence monic on Y. Nothing
requires X to be Noetherian or quasi-affine, a constant rank for M, or r > 0.
The construction and the splitting work also for zero modules and empty schemes. -/
theorem dual_free_quotient_embedding
    {X : Scheme.{u}} (M : X.Modules) [M.IsFiniteLocallyFree]
    {r : ℕ} (β : free (R := X.ringCatSheaf) (ULift.{u} (Fin r)) ⟶ dual M) [Epi β] :
    let α := SheafOfModules.bidual (R := X.sheaf) M ≫ dualMap β ≫
      (SheafOfModules.homObjFreeUnitIso (R := X.sheaf) (ULift.{u} (Fin r))).hom
    Mono α ∧ (cokernel α).IsFiniteLocallyFree ∧
      ∀ (Y : Scheme.{u}) (g : Y ⟶ X), Mono ((Modules.pullback g).map α) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
