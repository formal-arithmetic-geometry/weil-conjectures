/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Derived.DerivedMorphismPresheaf
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.CategoryTheory.Sites.SheafHom
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-!
# Derived Hom on finite disjoint unions of pro-etale objects

Source: Stacks Project, Tags 04TS, 015F and 0F63.
(blueprint: lem-weil-pbc-derived-hom-finite-products)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
set_option autoImplicit false

namespace CategoryTheory

section ModuleExtension

variable {C : Type (u + 1)} [Category.{u} C]
  (B : Type (u + 1)) [CommRing B] (W : C)

end ModuleExtension

section InjectiveRepresentatives

variable {E : Type*} [Category E] [Abelian E] [HasDerivedCategory E]
  (K L : CochainComplex E ℤ) [L.IsKInjective]

end InjectiveRepresentatives

section FiniteProducts

variable {C : Type (u + 1)} [Category.{u} C]
  [EssentiallySmall.{u + 1} C] (J : GrothendieckTopology C)
  (B : Type (u + 1)) [CommRing B]
  (I : Type (u + 1)) (W : I → C) (c : Cofan W)
  (hsec : ∀ H : Sheaf J (Type (u + 1)),
    Function.Bijective (fun t : H.obj.obj (op c.pt) ↦
      fun i ↦ H.obj.map (c.inj i).op t))

include hsec

end FiniteProducts

end CategoryTheory

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
