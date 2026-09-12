/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import WeilConjectures.Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup

/-!
# The group of units of a commutative ring, functorially

Mathlib has the functor `CommMonCat.units : CommMonCat ⥤ CommGrpCat` taking a commutative
monoid to its group of units, and the adjunction `CommRingCat.forget₂Adj` exhibiting
`R ↦ Rˣ` as a right adjoint. This file records the functor itself, in the two flavours that
sheaf cohomology needs:

* `CommRingCat.units : CommRingCat ⥤ CommGrpCat`, the group of units written multiplicatively;
* `CommRingCat.unitsAddCommGrp : CommRingCat ⥤ AddCommGrpCat`, the same group written
  additively, through the equivalence `CommGrpCat ≌ AddCommGrpCat` of
  `commGroupAddCommGroupEquivalence`.

The second is what the sheaf cohomology of `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
wants: it is defined for sheaves valued in `AddCommGrpCat` only. Both functors preserve
limits, being composites of right adjoints, so both take sheaves of commutative rings to
sheaves.

## Main definitions

- `CommRingCat.units` — the group of units of a commutative ring, as a functor to `CommGrpCat`.
- `CommRingCat.unitsAddCommGrp` — the same functor, valued in `AddCommGrpCat`.
-/

@[expose] public section

universe v₁ u₁ u

open CategoryTheory Limits

/-- The group of units of a commutative ring, as a functor `CommRingCat ⥤ CommGrpCat`. -/
noncomputable def CommRingCat.units : CommRingCat.{u} ⥤ CommGrpCat.{u} :=
  forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units

@[simp]
lemma CommRingCat.units_obj (R : CommRingCat.{u}) : CommRingCat.units.obj R = .of Rˣ := rfl

@[simp]
lemma CommRingCat.units_map {R S : CommRingCat.{u}} (f : R ⟶ S) :
    CommRingCat.units.map f = CommGrpCat.ofHom (Units.map f.hom.toMonoidHom) := rfl

noncomputable instance : PreservesLimitsOfSize.{v₁, u₁} CommRingCat.units.{u} :=
  inferInstanceAs (PreservesLimitsOfSize.{v₁, u₁}
    (forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units))

/-- The group of units of a commutative ring, written *additively*, as a functor
`CommRingCat ⥤ AddCommGrpCat`.

The additive shell is forced by `CategoryTheory.Sheaf.H`, which computes the cohomology of
sheaves valued in `AddCommGrpCat`; the underlying type of `CommRingCat.unitsAddCommGrp.obj R`
is `Additive Rˣ`. -/
noncomputable def CommRingCat.unitsAddCommGrp : CommRingCat.{u} ⥤ AddCommGrpCat.{u} :=
  CommRingCat.units ⋙ CommGrpCat.toAddCommGrp

@[simp]
lemma CommRingCat.unitsAddCommGrp_obj (R : CommRingCat.{u}) :
    CommRingCat.unitsAddCommGrp.obj R = .of (Additive Rˣ) := rfl

@[simp]
lemma CommRingCat.unitsAddCommGrp_map {R S : CommRingCat.{u}} (f : R ⟶ S) :
    CommRingCat.unitsAddCommGrp.map f =
      AddCommGrpCat.ofHom (Units.map f.hom.toMonoidHom).toAdditive := rfl

noncomputable instance : PreservesLimitsOfSize.{v₁, u₁} CommRingCat.unitsAddCommGrp.{u} :=
  inferInstanceAs (PreservesLimitsOfSize.{v₁, u₁}
    (CommRingCat.units ⋙ CommGrpCat.toAddCommGrp))
