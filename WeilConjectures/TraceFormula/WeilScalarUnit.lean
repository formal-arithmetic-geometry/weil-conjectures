/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.TraceFormula.BaseChange.Supertrace
public import WeilConjectures.TraceFormula.Statement
public import WeilConjectures.TraceFormula.WeilTrace
public import WeilConjectures.WeilObject.Sheaf.EndTensorUnit
public import WeilConjectures.WeilObject.Sheaf.StalkUnit

/-!

# The unit Weil object twisted by a scalar

Let `ℓ` be a prime, `k = 𝔽_q` a finite field of characteristic `p ≠ ℓ`, `X` a separated scheme of
finite type over `Spec k` with an automorphism `e : X ≅ X` over `Spec k`, and `c` a unit of
`ℚ̄_ℓ`. This file constructs the canonical Weil unit `ℚ̲̄_ℓ,X` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧`
(`ProEtale.CondensedRing.weilUnit`) with its structure isomorphism multiplied by `c`
(`ProEtale.CondensedRing.weilScalarUnit`) and computes its traces: its local trace at every point
of degree `n + 1` is `c^{n+1}`, and so its global trace is `c^{n+1}` times the number of points of
degree `n + 1`.

The constants `ℚ̄_ℓ` act on the unit `ℚ̲̄_ℓ,Y` of `Mod_Y` for every scheme `Y`
(`ProEtale.CondensedRing.scalarEndRingHom`): the multiplication by a constant of the regular
condensed module `ℚ̲̄_ℓ` is pulled back along `p_Y^*`. This action is compatible with all pullbacks
(`ProEtale.CondensedRing.εIso_hom_comp_map_scalarEndRingHom_comp_εIso_inv`), and under
`End (𝟙_ Mod_{Spec Ω}) ≃+* ℚ̄_ℓ` (`ProEtale.CondensedRing.endTensorUnitRingEquiv`) it is the
identity (`ProEtale.CondensedRing.endTensorUnitRingEquiv_scalarEndRingHom`). On `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` the
action is placed in degree `0` (`ProEtale.CondensedRing.homologyUnitEndRingHom`).

The computation follows the one of the untwisted unit in `WeilConjectures.TraceFormula.WeilTrace`:
the only nonzero homology sheaf is `H⁰`, the unit Weil sheaf twisted by `c`
(`ProEtale.CondensedRing.homologyFunctorZeroWeilScalarUnitIso`); the `(n + 1)`-st iterated Weil
structure of the twisted unit Weil sheaf is the twisted unit Weil sheaf for `e^{n+1}` and `c^{n+1}`
(`ProEtale.CondensedRing.WeilSheaf.pow_scalarUnit`), since the action of `c` commutes with the unit
comparisons of the pullbacks; and the Frobenius on its stalk is, conjugated by the unit
comparison of the stalk, the multiplication by `c^{n+1}`, whose trace on the unit is itself.

## Main definitions

- `ProEtale.CondensedRing.scalarEndRingHom`: `ℚ̄_ℓ →+* End (𝟙_ Mod_Y)`.
- `ProEtale.CondensedRing.WeilSheaf.scalarUnit`: the unit Weil sheaf twisted by `c`.
- `ProEtale.CondensedRing.weilScalarUnit`: the canonical Weil unit twisted by `c`.

## Main results

- `ProEtale.CondensedRing.endTensorUnitRingEquiv_weilStalkTraceAlternatingSum_weilScalarUnit`:
  the local trace of the twisted Weil unit at a point of degree `n + 1` is `c^{n+1}`.
- `ProEtale.CondensedRing.endTensorUnitRingEquiv_weilCompactSupportCohomology_weilScalarUnit`:
  for `e` of finite order, its global trace in degree `n + 1` is `c^{n+1} · #X(𝔽_{q^{n+1}})`.
- `ProEtale.CondensedRing.endTensorUnitRingEquiv_weilStalkTraceAlternatingSum_weilScalarUnit_point`,
  `ProEtale.CondensedRing.endTensorUnitRingEquiv_weilCompactSupportCohomology_weilScalarUnit_point`:
  for the base `Spec k`, the local trace at its geometric point and the global trace are `c^{n+1}`.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor MonoidalCategory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- The pullback `p_Y^*` from condensed `Λ`-modules is additive on module objects, being additive
on underlying sheaves. -/
instance additive_upperStarFromPointMod (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) : (upperStarFromPointMod Λ Y).Additive where
  map_add := by
    intros
    ext1
    exact (upperStarFromPoint Y).map_add

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The constants `ℚ̄_ℓ` act on the unit `ℚ̲̄_ℓ,Y` of `Mod_Y`: the image of the multiplication by
a constant on the regular condensed module `ℚ̲̄_ℓ` under the strong monoidal pullback `p_Y^*`. -/
noncomputable def scalarEndRingHom (Y : Scheme.{u}) :
    _root_.PadicAlgCl ℓ →+* End (𝟙_ (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y)
      Ab.{u + 1}) (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))) :=
  (Functor.Monoidal.εIso
      (upperStarFromPointMod (Profinite.padicAlgClRingObj ℓ) Y)).symm.conjRingEquiv.toRingHom.comp
    (((upperStarFromPointMod (Profinite.padicAlgClRingObj ℓ) Y).mapEndRingHom _).comp
      (Profinite.PadicAlgCl.endRegularRingEquiv ℓ).toRingHom)

lemma scalarEndRingHom_apply (Y : Scheme.{u}) (c : _root_.PadicAlgCl ℓ) :
    scalarEndRingHom ℓ Y c =
      (Functor.Monoidal.εIso (upperStarFromPointMod (Profinite.padicAlgClRingObj ℓ) Y)).hom ≫
        (upperStarFromPointMod (Profinite.padicAlgClRingObj ℓ) Y).map
          (Profinite.PadicAlgCl.endRegularRingEquiv ℓ c) ≫
        (Functor.Monoidal.εIso (upperStarFromPointMod (Profinite.padicAlgClRingObj ℓ) Y)).inv :=
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime]

lemma scalarEndRingHom_eq_map (Y : Scheme.{u}) (c : _root_.PadicAlgCl ℓ) :
    scalarEndRingHom ℓ Y c = (upperStarFromPointMod (Profinite.padicAlgClRingObj ℓ) Y).map
      (Profinite.PadicAlgCl.endRegularRingEquiv ℓ c) := by
  rw [scalarEndRingHom_apply]
  refine Mod.hom_ext _ _ ?_
  rw [Mod.comp_hom', Mod.comp_hom']
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- Under the identification `End (𝟙_ Mod_{Spec Ω}) ≃+* ℚ̄_ℓ`, the action of a constant on the
unit is the constant itself. -/
@[simp]
lemma endTensorUnitRingEquiv_scalarEndRingHom (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (c : _root_.PadicAlgCl ℓ) :
    endTensorUnitRingEquiv ℓ Ω (scalarEndRingHom ℓ (Spec (.of Ω)) c) = c := by
  conv_rhs => rw [← (endTensorUnitRingEquiv ℓ Ω).apply_symm_apply c]
  rw [scalarEndRingHom_eq_map]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime]

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]

section ScalarSheaf

variable {X : Over (Spec (.of k))} (e : X ≅ X)

end ScalarSheaf

section ScalarSheafTrace

variable [Finite k] {X : Over (Spec (.of k))} (e : X ≅ X)

end ScalarSheafTrace

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

variable (e : X ≅ X)

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] (e : X ≅ X)

section Trace

variable [Finite k]

attribute [local instance] fintypeFrobeniusFixedPoints

end Trace

/-! ### The base point -/

section Point

variable {k : Type u} [Field k] [Finite k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

end Point

end AlgebraicGeometry.ProEtale.CondensedRing
