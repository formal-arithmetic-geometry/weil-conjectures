/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Abelian
public import WeilConjectures.Mathlib.Algebra.Category.Ring.Adjunctions

/-!
# The sheaf of units and its cohomology

Let `R` be a sheaf of commutative rings on a site `(C, J)`. Its *sheaf of units* `R^×` is the
composite of `R` with the units functor `CommRingCat.unitsAddCommGrp`; it is a sheaf because
that functor preserves limits. This file defines it, identifies its sections and its degree
zero cohomology, and specialises everything to the structure sheaf of a scheme, where `R^×`
is the sheaf `𝒪_X^×`.

`CategoryTheory.Sheaf.H` computes the cohomology of sheaves valued in `AddCommGrpCat` only, so
the sheaf of units is recorded in its *additive* shell: the sections of `R^×` over `X` are
`Additive (R(X))ˣ`. `CategoryTheory.Sheaf.unitsMulEquiv` and
`CategoryTheory.Sheaf.unitsH.mulEquiv₀` undo the shell, so that no consumer has to think about
`Additive`.

## Main definitions

- `CategoryTheory.Sheaf.units` — the sheaf of units of a sheaf of commutative rings on a site,
  and `AlgebraicGeometry.Scheme.unitsSheaf`, its specialisation `𝒪_X^×` to a scheme.
- `AlgebraicGeometry.Scheme.unitsH` — the cohomology `H^n(X, 𝒪_X^×)` of the sheaf of units of a
  scheme.
- `AlgebraicGeometry.Scheme.unitsFunctor` — the group of units of the ring of global sections,
  as a functor `Schemeᵒᵖ ⥤ CommGrpCat`, and `AlgebraicGeometry.Scheme.Hom.unitsMap`, the
  restriction `Γ(Y, 𝒪_Y)ˣ →* Γ(X, 𝒪_X)ˣ` of global units along a morphism `f : X ⟶ Y`.

## Main results

- `CategoryTheory.Sheaf.unitsMulEquiv` — the sections of `R^×` over `X` are `(R(X))ˣ`.
- `CategoryTheory.Sheaf.unitsH.mulEquiv₀` and `AlgebraicGeometry.Scheme.unitsH.mulEquiv₀` —
  `H^0(X, 𝒪_X^×) ≅ Γ(X, 𝒪_X)ˣ`: the global sections of the sheaf of units are the units of the
  ring of global sections.

-/

@[expose] public section

universe w v₁ u₁ u

open CategoryTheory Limits Opposite TopologicalSpace

namespace CategoryTheory.Sheaf

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})

/-- **The sheaf of units** `R^×` of a sheaf of commutative rings `R` on a site, as a sheaf of
abelian groups: the composite of `R` with the units functor `CommRingCat.unitsAddCommGrp`.

The group is written *additively*, because `CategoryTheory.Sheaf.H` only knows how to compute
the cohomology of sheaves valued in `AddCommGrpCat`; the sections over `X` are
`Additive (R(X))ˣ`, see `CategoryTheory.Sheaf.units_obj_obj`. Use
`CategoryTheory.Sheaf.unitsMulEquiv` to pass back to the group of units itself. -/
noncomputable def units : Sheaf J AddCommGrpCat.{u} :=
  (sheafCompose J CommRingCat.unitsAddCommGrp).obj R

/-- The sections of the sheaf of units are the units of the sections, in their additive shell.
This is the defeq on which `CategoryTheory.Sheaf.unitsMulEquiv` rests. -/
@[simp]
lemma units_obj_obj (X : Cᵒᵖ) : R.units.obj.obj X = .of (Additive (R.obj.obj X)ˣ) :=
  rfl

/-- **The sections of the sheaf of units are the units of the sections.** -/
noncomputable def unitsMulEquiv (X : Cᵒᵖ) :
    Multiplicative (R.units.obj.obj X) ≃* (R.obj.obj X)ˣ :=
  MulEquiv.multiplicativeAdditive (R.obj.obj X)ˣ

variable [HasSheafify J AddCommGrpCat.{u}] [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]

/-- **The global sections of the sheaf of units are the units of the global sections**:
`H^0(X, R^×) ≅ (R(X))ˣ` for `X` a terminal object of the site. -/
noncomputable def unitsH.mulEquiv₀ {T : C} (hT : IsTerminal T) :
    Multiplicative (Sheaf.H R.units 0) ≃* (R.obj.obj (op T))ˣ :=
  (Sheaf.H.equiv₀ R.units hT).toMultiplicative.trans (R.unitsMulEquiv (op T))

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- **The sheaf of units `𝒪_X^×`** of a scheme `X`, as a sheaf of abelian groups on the site of
open subsets of `X`: the sheaf of units of the structure sheaf. -/
noncomputable abbrev unitsSheaf : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  X.sheaf.units

/-- The sections of the sheaf of units over an open subset `U` are the units of `Γ(X, U)`. -/
noncomputable def unitsMulEquiv (U : X.Opens) :
    Multiplicative (X.unitsSheaf.obj.obj (op U)) ≃* Γ(X, U)ˣ :=
  X.sheaf.unitsMulEquiv (op U)

/-- The cohomology `H^n(X, 𝒪_X^×)` of the sheaf of units of a scheme. -/
abbrev unitsH (n : ℕ) : Type u :=
  Sheaf.H X.unitsSheaf n

/-- **The global sections of the sheaf of units are the units of the global sections**:
`H^0(X, 𝒪_X^×) ≅ Γ(X, 𝒪_X)ˣ`.

Only the group itself is identified here, not the maps between the groups for varying `X`:
`CategoryTheory.Sheaf.H` is functorial in the sheaf, not in the site, so the comparison of
`AlgebraicGeometry.Scheme.Hom.unitsMap` with the map induced by `f` on `H^0(-, 𝒪^×)` needs
functoriality of sheaf cohomology along a morphism of sites, which is not available. -/
noncomputable def unitsH.mulEquiv₀ : Multiplicative (X.unitsH 0) ≃* Γ(X, ⊤)ˣ :=
  Sheaf.unitsH.mulEquiv₀ X.sheaf (isTerminalTop (α := X.Opens))

/-! ### Global units, functorially -/

/-- The group of units of the ring of global sections, as a functor `Schemeᵒᵖ ⥤ CommGrpCat`:
the global sections functor followed by the units functor of a commutative ring. -/
noncomputable def unitsFunctor : Scheme.{u}ᵒᵖ ⥤ CommGrpCat.{u} :=
  Scheme.Γ ⋙ CommRingCat.units

variable {X}

/-- The restriction of global units along a morphism of schemes `f : X ⟶ Y`, i.e. the action
of `AlgebraicGeometry.Scheme.unitsFunctor` on `f`. -/
noncomputable def Hom.unitsMap {Y : Scheme.{u}} (f : X ⟶ Y) : Γ(Y, ⊤)ˣ →* Γ(X, ⊤)ˣ :=
  (unitsFunctor.map f.op).hom

@[simp]
lemma Hom.unitsMap_apply {Y : Scheme.{u}} (f : X ⟶ Y) (u : Γ(Y, ⊤)ˣ) :
    (f.unitsMap u : Γ(X, ⊤)) = f.appTop (u : Γ(Y, ⊤)) :=
  rfl

variable (X) in
@[simp]
lemma Hom.unitsMap_id : Hom.unitsMap (𝟙 X) = MonoidHom.id Γ(X, ⊤)ˣ :=
  congrArg CommGrpCat.Hom.hom (unitsFunctor.map_id (op X))

@[simp]
lemma Hom.unitsMap_comp {Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).unitsMap = f.unitsMap.comp g.unitsMap :=
  congrArg CommGrpCat.Hom.hom (unitsFunctor.map_comp g.op f.op)

end AlgebraicGeometry.Scheme
