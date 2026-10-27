/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition
import WeilConjectures.TateTwist.ProEtale
public import Sheaf.Targets.PoincareTateBoundedConstructible

/-! The representing trace required by condensed smooth purity.

This is the geometric input of `def-route-smooth-trace`: the normalized finite and
adic purity system represents the compact-support Hom functor. The resulting trace is
therefore unique, so the source definition can take its witness without arbitrary data.
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped CategoryTheory.Obj
open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- The normalized finite and adic purity system supplies a unique representing trace.

At every positive-power coefficient level, finite smooth purity identifies the
compact-support Hom pairing with postcomposition by the finite counit.  The normalized
integral Tate and unit towers transport these bijections through derived-limit
reconstruction, and scalar extension realizes the result in the condensed coefficient
category.  The resulting counit is unique by the adjunction Hom equivalence, so the
four-step construction gives the displayed existential uniqueness statement.

Source: `def-route-smooth-trace`, Steps 1--4.
(blueprint: lem-route-smooth-trace-representing-unique) -/
theorem existsUnique_smoothTrace
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ℓ)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (d : ℕ)
    (hsm : SmoothOfRelativeDimension d f.left)
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hM : M.obj ≅ (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d))
    (U : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hU : U = MonoidalCategoryStruct.tensorUnit (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) :
    ∃! t :
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj M ⟶ U,
      ∀ K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧,
        Function.Bijective (fun a : K ⟶ M ↦
          (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).map a ≫ t) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
