/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleShiftSingle

/-! Bounded constructibility of the regular module and its positive shift.
(blueprint: lem-fd-regular-single-shift-bounded) -/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The regular module of the pulled-back coefficient ring in degree zero, and its shift by
one, are bounded constructible.

Source: current blueprint, lem-fd-first-formula.proof.md, the six membership clauses (unit
and positive-shift memberships) (blueprint: lem-fd-regular-single-shift-bounded).

Proof in words. The regular module is the monoidal unit of the module category, which is
locally free (of rank one), hence constructible. A constructible module placed in degree
zero is bounded constructible, and bounded constructibility of a single constructible module
is stable under every shift, in particular the shift by one. -/
theorem regular_single_shift_bounded
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    boundedConstructible (condensedRingObj Λ X)
        ((DerivedCategory.singleFunctor _ 0).obj (Mod.regular (condensedRingObj Λ X))) ∧
      boundedConstructible (condensedRingObj Λ X)
        ((shiftFunctor _ (1 : ℤ)).obj
          ((DerivedCategory.singleFunctor _ 0).obj (Mod.regular (condensedRingObj Λ X)))) := by
  have hC : IsConstructibleModuleObject (condensedRingObj Λ X)
      (Mod.regular (condensedRingObj Λ X)) :=
    (isLocallyFree_tensorUnit Λ X).isConstructibleModuleObject
  exact ⟨CondensedRing.boundedConstructible_singleFunctor_obj Λ X 0 _ hC,
    boundedConstructible_shift_single _ _ hC 1⟩

end AlgebraicGeometry.ProEtale
