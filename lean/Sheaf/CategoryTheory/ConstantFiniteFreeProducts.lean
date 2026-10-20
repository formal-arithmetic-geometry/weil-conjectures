/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M8
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Sheaf.CategoryTheory.ConstantFiniteFreePowerIso
import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Countable products and finite-free constant scalar extension

Source: Stacks 03EK and the finite-basis calculation in step 6 of
`lem-pur-compact-support-roos-cofinality`.
-/

@[expose] public section

set_option autoImplicit false

universe uC vC r

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Finite-free constant scalar extension preserves countable products for its
specified sectionwise maps followed by sheafification. No Roos cones or
arithmetic restrictions occur in this assertion.

Source: Stacks 03EK, tensor sheafification, and the finite-basis calculation of
step 6 of `lem-pur-compact-support-roos-cofinality`.
(blueprint: lem-pur-constant-finite-free-products)

Proof: Choose a finite A-basis of B and its coordinate functionals. They induce,
after forgetting the B-action, mutually inverse maps between scalar extension
of M and the corresponding finite power of M. First check the basis identities
on the constant presheaves, then sheafify; the tensor universal property extends
them to arbitrary module sheaves. In these coordinates the canonical product
comparison is the rearrangement of a finite power of a countable product.
The inverse sends the family of basis coordinates to the finite sum of tensors
of their product families with the basis vectors. All formulas commute with
restriction and hence define sheaf maps. On local pure tensors the comparison
sends a tensor of a product family to the family of its tensors, so is B-linear.
This proves its invertibility without choosing the canonical comparison from
the basis. The specified object and morphism equalities identify F with this
scalar extension, and invertibility of all countable comparisons implies the
stated preservation of limits of discrete shape. This includes the rank-zero
case, in which the target module category is the zero category. -/
theorem constantFiniteFree_preservesCountableProducts
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J CommRingCat.{max uC vC r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (A B : CommRingCat.{max uC vC r}) [Algebra A B] [Module.Free A B]
    [Module.Finite A B]
    (F : SheafOfModules.{max uC vC r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          ((constantSheaf J CommRingCat).obj A)) ⥤
      SheafOfModules.{max uC vC r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          ((constantSheaf J CommRingCat).obj B)))
    (hobj : ∀ M, F.obj M = SheafOfModules.changeOfRingsOfUniverses
      ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))) M)
    (hmap : ∀ M N (f : M ⟶ N), HEq (F.map f)
      (SheafOfModules.changeOfRingsHomOfUniverses
        ((constantSheaf J CommRingCat).map (CommRingCat.ofHom (algebraMap A B))) M f)) :
    PreservesLimitsOfShape (Discrete ℕ) F := by
  obtain ⟨n, ⟨h⟩⟩ := constantFiniteFree_underlyingPowerIso.{uC, vC, r} J A B F hobj hmap
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj
    ((constantSheaf J CommRingCat).obj A)
  let S := (sheafCompose J (forget₂ CommRingCat RingCat)).obj
    ((constantSheaf J CommRingCat).obj B)
  let U := SheafOfModules.forget.{max uC vC r} S ⋙ PresheafOfModules.toPresheaf S.obj
  have : PreservesLimitsOfShape (Discrete ℕ)
      (SheafOfModules.forget.{max uC vC r} R ⋙ PresheafOfModules.toPresheaf R.obj) :=
    inferInstance
  have : PreservesLimitsOfShape (Discrete ℕ) (F ⋙ U) :=
    preservesLimitsOfShape_of_natIso h.symm
  have : ReflectsLimitsOfShape (Discrete ℕ) U :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves F U

end CategoryTheory
