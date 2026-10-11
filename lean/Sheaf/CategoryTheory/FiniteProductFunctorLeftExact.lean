/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Left exactness of a finite product of functors

Source: Stacks Project, Homology, Lemma 060K, together with the componentwise universal
properties in a product category (blueprint: lem-weil-pbc-finite-product-functor-left-exact).
-/

@[expose] public section

universe u v w z

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- For a finite family of abelian categories and additive left exact functors to abelian
groups, the product category has finite biproducts and kernels, computed componentwise,
and the product of the functors is additive and left exact. The structure on the product
category is stated existentially as an `Abelian` instance (the shared form of
`rightDerived_finite_product` and `finiteProduct_injectiveResolutions`; Mathlib has no
`Abelian` instance on `∀ i, A i`); it provides the finite biproducts and kernels. The
evaluation functors being additive and preserving finite biproducts and kernel diagrams
says that addition, biproducts and kernels are computed componentwise.
`Functor.pi Γi ⋙ Pi.functor I` takes objects and maps to their products.

Source: Stacks Project, Homology, Lemma 060K, and componentwise universal properties.
Proof: by `def-sp-abelian`, take zero objects and finite biproducts componentwise.
For a family of morphisms take the family of kernels: a cone into it is precisely a
family of cones into the component kernels, whose unique lifts assemble to the unique
lift in the product category. Evaluation therefore preserves these biproducts and
kernels. For the second step, use `def-sp-left-exact-additive`: each Γi preserves finite
biproducts and kernels. Finite products of abelian groups are biproducts, products commute
with products, and the kernel of the product map is the product of its kernels (060K).
Thus Γ preserves finite products and kernels and is additive and left exact.
(blueprint: lem-weil-pbc-finite-product-functor-left-exact) -/
theorem finite_product_functor_left_exact
    (I : Type u) [Finite I]
    (A : I → Type v) [∀ i, Category.{w} (A i)] [∀ i, Abelian (A i)]
    (Γi : (i : I) → A i ⥤ AddCommGrpCat.{z})
    [∀ i, (Γi i).Additive] [∀ i, PreservesFiniteLimits (Γi i)] :
    let Γ := Functor.pi Γi ⋙ Pi.functor I
    ∃ hAb : Abelian (∀ i, A i),
      letI := hAb
      (∀ i, ∃ hEvalAdd : (Pi.eval A i).Additive,
        letI := hEvalAdd
        PreservesFiniteBiproducts (Pi.eval A i) ∧
          ∀ (X Y : ∀ i, A i) (f : X ⟶ Y),
            PreservesLimit (parallelPair f 0) (Pi.eval A i)) ∧
        Γ.Additive ∧ PreservesFiniteLimits Γ := by
  sorry

end CategoryTheory
