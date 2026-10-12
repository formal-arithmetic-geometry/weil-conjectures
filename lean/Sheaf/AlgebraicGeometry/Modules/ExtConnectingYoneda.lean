/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExtYonedaFunctoriality
import Sheaf.CategoryTheory.Abelian.ExtResolutionDerivedConnecting
import WeilConjectures.AlgebraicGeometry.Modules.Ext

/-!
# The degree-zero Ext boundary and Yoneda composition

Source: Stacks Project, Cohomology, Tag 0B3A, in the general form for an arbitrary first
argument; Derived Categories, Tags 06XP, 06XQ and 06XR
(blueprint: lem-sc-p1-ext-connecting-yoneda).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The connecting map `Hom(F,C) → Ext¹(F,A)` sends `s` to the Yoneda composite of `s`
with the class of `0 → A → B → C → 0`.
We express the boundary using the homological functor of derived morphisms, then transport
it to the recorded `Ext` groups by `Abelian.Ext.homAddEquiv`. The derived category is the
standard localization, explicitly supplied so no additional existence hypothesis is needed.
Source: Stacks Project, Cohomology, Tag 0B3A; Derived Categories, Tags 06XP and 06XR
(blueprint: lem-sc-p1-ext-connecting-yoneda).

Proof:
1. Compute Ext by an injective resolution in the second variable (def-sc-ext-sheaf).
By lem-sc-p1-ext-resolution-derived-connecting the resolution boundary agrees with the
homology boundary of the distinguished triangle of the short exact sequence. The
canonical degree-zero class of `s` is `Abelian.Ext.mk₀ s`.
2. Apply lem-sc-p1-derived-connecting-extclass with first argument `F` and degree zero.
The triangle boundary is composition with `hS.extClass`. By
lem-sc-ext-yoneda-composition-derived this is Yoneda composition in the convention of
lem-sc-p1-ext-yoneda-functoriality. Transport through the comparison in Step 1.
-/
theorem ext_connecting_yoneda {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (F : X.Modules) (s : F ⟶ S.X₃) :
    (@Abelian.Ext.homAddEquiv X.Modules _ _ _ F S.X₁
      (HasDerivedCategory.standard X.Modules) 1).symm
      ((preadditiveCoyoneda.obj
        (op ((@DerivedCategory.singleFunctor X.Modules _ _
          (HasDerivedCategory.standard X.Modules) 0).obj F))).homologySequenceδ
        (@ShortComplex.ShortExact.singleTriangle X.Modules _ _
          (HasDerivedCategory.standard X.Modules) S hS) 0 1 (by decide)
        (@Abelian.Ext.hom X.Modules _ _ _ F S.X₃
          (HasDerivedCategory.standard X.Modules) 0 (Abelian.Ext.mk₀ s))) =
      ((Abelian.Ext.mk₀ s : Ext F S.X₃ 0).comp
        (hS.extClass : Ext S.X₃ S.X₁ 1) (zero_add 1)) := sorry

end AlgebraicGeometry.Scheme.Modules
