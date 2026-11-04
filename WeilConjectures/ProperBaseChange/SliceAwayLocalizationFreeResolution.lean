/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Exact.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The free telescope resolution of a localized ring sheaf

Source: Stacks Project, algebraization.tex, Tag 0997, lemma-hom-from-Af, displayed resolution
(blueprint: lem-weil-pbc-localization-free-resolution).
-/

@[expose] public section

universe u vC uC

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

section AlgebraicTelescope

variable {R : Type u} [CommRing R]

end AlgebraicTelescope

section

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (O : Sheaf J CommRingCat.{u}) (U : C) (f : O.obj.obj (op U))

end

section

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

private noncomputable abbrev sh : PresheafOfModules.{u} R.obj ⥤ SheafOfModules.{u} R :=
  PresheafOfModules.sheafification (𝟙 R.obj)

private noncomputable abbrev adj :=
  PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj)

end

end CategoryTheory
