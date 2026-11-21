/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLowerShriekOfPreserves

/-!
# Lower shriek on bounded constructible complexes and its ambient compatibility

The lower shriek `Rf_!^c = Rp_* ∘ i_!` on bounded constructible complexes, for an arbitrary
commutative condensed coefficient ring whose derived pushforwards preserve bounded
constructibility, and the chosen `Rf_! = Rf_!^{c_f}`, are the landed declarations
`boundedConstructibleLowerShriekOfCompactificationOfPreserves` and
`boundedConstructibleLowerShriekOfPreserves` of
`Sheaf.Paper.BoundedConstructibleLowerShriekOfPreserves`
, built on the preservation hypothesis
`PreservesBoundedConstructiblePushforwards`. This file adds the compatibility of these functors
with the ambient lower shriek `R(p_*) ∘ D(i_!)` for the same compactification.

## Main definitions

* `boundedConstructibleLowerShriekOfCompactificationOfPreservesCompatibility`:
  `ι_Y ∘ Rf_!^c ≅ Rf_!^c ∘ ι_X` for a given compactification `c`.
* `boundedConstructibleLowerShriekOfPreservesCompatibility`: the same at the chosen
  compactification `AlgebraicGeometry.compactificationOverField`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (H : PreservesBoundedConstructiblePushforwards Λ k)

/-- The lower shriek attached to a compactification `c = (i, p)` is compatible with the ambient
lower shriek `R(p_*) ∘ D(i_!)` for the same `c`: `ι_Y ∘ Rf_!^c ≅ R(p_*) ∘ D(i_!) ∘ ι_X`. -/
noncomputable def boundedConstructibleLowerShriekOfCompactificationOfPreservesCompatibility
    {f : X ⟶ Y} (c : Compactification.BoundaryCompactification f.left) :
    boundedConstructibleLowerShriekOfCompactificationOfPreserves Λ ℓ H c ⋙
        (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ rightDerivedLowerShriekOfCompactification Λ c.obj.obj :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (boundedConstructibleLowerStarOfPreservesCompatibility Λ H c.obj.obj.overG) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (boundedConstructibleOpenImmersionLowerShriekCompatibility Λ ℓ c.obj.obj.overI) _ ≪≫
    Functor.associator _ _ _

end AlgebraicGeometry.ProEtale.CondensedRing
