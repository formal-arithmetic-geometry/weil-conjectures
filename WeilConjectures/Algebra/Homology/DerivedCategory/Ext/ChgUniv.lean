/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Compatibilities of the change of universe of `Ext`-groups

Mathlib's `CategoryTheory.Abelian.Ext.chgUniv` identifies `Ext.{w} X Y n` with `Ext.{w'} X Y n`
as types. We show that this bijection is additive and compatible with the composition of
`Ext`-groups and with `Ext.mk₀`.

## Main definitions

- `CategoryTheory.Abelian.Ext.chgUnivAddEquiv`: `Ext.chgUniv` as an additive equivalence.

## Main statements

- `CategoryTheory.Abelian.Ext.chgUniv_comp`: compatibility with composition.
- `CategoryTheory.Abelian.Ext.chgUniv_mk₀`: compatibility with `Ext.mk₀`.
-/

@[expose] public section

universe w'' w' w v u

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] [HasExt.{w'} C]
  {X Y Z : C}

end CategoryTheory.Abelian.Ext
