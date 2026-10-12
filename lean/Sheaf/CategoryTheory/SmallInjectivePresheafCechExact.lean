/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Positive exactness of the small-valued injective presheaf Čech complex

Source: Stacks Project, Tags 03AS, 03AT and 03AU.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Limits Opposite

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- Positive exactness of the categorical Čech complex of a size-aligned injective presheaf.
Source: Stacks Project, Cohomology on Sites, Tags 03AS, 03AT and 03AU.
(blueprint: lem-sc-small-injective-presheaf-cech-exact)

Proof: In degree n form the coproduct of free abelian representables of the products
indexed by Fin (n+1) -> iota. Hom sets and the tuple index are v-small, so these are
presheaves of v-small abelian groups even when the object type of C is larger.
Use the alternating projection boundary. Evaluated at Z, the basis decomposes by
the common composite Z -> X. Each summand is the free abelian tuple complex on
the set of lifts to the family. For an empty lift set every term is zero. Otherwise,
choose a lift and prepend it to tuples; the alternating boundary identity contracts
the complex, proving exactness in all positive chain degrees. Kernels and images
of presheaves are computed objectwise, so the free presheaf complex is exact there.
Apply Hom(-, P): a cocycle factors through the image of the preceding boundary,
and injectivity extends the resulting map from that image to the preceding free
term. This produces a primitive. The free representable adjunction and the product
universal property identify this Hom complex with Mathlib's categorical Čech
complex, including its alternating signs. Thus every positive cocycle is a boundary.
The argument requires no covering, and treats the empty family without exception. -/
theorem small_injective_presheaf_cech_exact
    {C : Type u} [Category.{v} C] [HasFiniteWidePullbacks C]
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{v}) [Injective P] (X : C)
    {ι : Type v} (U : ι → C) (π : ∀ i, U i ⟶ X) (q : ℕ) :
    ((cechComplexFunctor (fun i ↦ Over.mk (π i))).obj
      ((Over.forget X).op ⋙ P)).ExactAt (q + 1) := by
  sorry

end CategoryTheory
