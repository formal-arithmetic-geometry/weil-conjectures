/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.TraceFormula.Specialization.TraitClosedLift
public import WeilConjectures.TraceFormula.Specialization.TraitGenericFibre

/-!

# The direct image from the geometric generic point of the trait

Let `k'` be a separably closed field, `S = Spec k'⟦t⟧` the strictly henselian trait,
`i : Spec k' ⟶ S` its closed point and `j : Spec Ω ⟶ S` its geometric generic point. For a
commutative condensed ring `Λ`, the coefficient ring `Λ_S` restricted to the closed point does
not see the passage to the geometric generic point:

* the unit `Λ_S ⟶ j_* j^* Λ_S` becomes an isomorphism after `i^*`
  (`ProEtale.CondensedRing.isIso_upperStar_traitClosedPoint_map_unit_app`);
* the higher direct images `Rⁿ j_* (j^* Λ_S)`, `n > 0`, vanish after `i^*`
  (`ProEtale.CondensedRing.isZero_upperStar_traitClosedPoint_obj_rightDerived`).

Both are checked on sections over the henselian lifts `W = Spec H_{k'⟦t⟧}(C̄)` of the
w-contractible ind-étale `k'`-algebras `C̄`, which compute the sections of `i^*`. Such a `W` is
weakly contractible, and so is its geometric generic fibre `W ×_S Spec Ω`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (k' : Type u) [Field k'] [IsSepClosed k']


/-- After restriction to the closed point of the trait, the higher direct images
`Rⁿ j_* (j^* Λ_S)`, `n > 0`, along the geometric generic point `j : Spec Ω ⟶ S` vanish. -/
theorem isZero_upperStar_traitClosedPoint_obj_rightDerived (n : ℕ) (hn : 0 < n) :
    IsZero ((traitClosedPoint k')^*⟦Λ⟧.obj
      (((traitGenericPoint k')_*⟦Λ⟧.rightDerived n).obj
        ((traitGenericPoint k')^*⟦Λ⟧.obj (𝟙_ _)))) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
