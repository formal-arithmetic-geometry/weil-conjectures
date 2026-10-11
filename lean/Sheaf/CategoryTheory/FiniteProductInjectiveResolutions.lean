/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution

/-!
# Injective resolutions in finite products of abelian categories

Source: Stacks Project, Derived Categories, Section 13.20 (Tag 0156), and the
componentwise product-category argument recorded in the DAG
(blueprint: lem-weil-pbc-finite-product-injective-resolutions).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A finite product of abelian categories with enough injectives is abelian and has enough
injectives. Its injective objects and injective resolutions are componentwise.
Source: Stacks Project, Derived Categories, Section 13.20 (Tag 0156), for the injective-resolution
setup; the product-category argument is supplied by the DAG
(blueprint: lem-weil-pbc-finite-product-injective-resolutions).

Proof, following the four steps of the node:
1. Zero objects, biproducts, kernels and cokernels are computed componentwise. A morphism is
mono or epi exactly when every component is. Normal monos and normal epis therefore hold
componentwise, giving the abelian structure (def-sp-abelian).
2. If every component of J is injective, extend a map along a mono in each component and
assemble the extensions. Conversely, put a mono and a map into J i in component i, with
zero objects in every other component; an extension into J gives the required extension
into J i (def-sp-injective-resolutions).
3. Choose monomorphisms into injectives componentwise (degree zero of the component
resolutions). Their assembled map is mono and their assembled target is injective by step 2,
giving enough injectives; with step 4 every object of the product has an injective resolution
(`HasInjectiveResolutions`, the form of lem-weil-pbc-derived-finite-product).
4. Assemble any given complexes and augmentations componentwise. Every term is injective
by step 2. Kernels and images are componentwise, so exactness in positive degrees and the
identification of degree-zero cohomology with A follow from the given resolutions. Thus
this very complex and augmentation form an injective resolution, not just some unrelated
resolution (def-sp-injective-resolutions).

The equations on X, d and the degree-zero augmentation specify the componentwise data
exactly. Heterogeneous equality allows the differential and augmentation to be compared
before rewriting the equalities of their endpoint objects. In higher degrees the source
of the augmentation is zero, so those components are forced. -/
theorem finiteProduct_injectiveResolutions
    (I : Type w) [Finite I] (C : I → Type u) [∀ i, Category.{v} (C i)]
    [∀ i, Abelian (C i)] [∀ i, HasInjectiveResolutions (C i)] :
    ∃ abelian : Abelian (∀ i, C i),
      letI := abelian
      HasInjectiveResolutions (∀ i, C i) ∧
        (∀ J : ∀ i, C i, Injective J ↔ ∀ i, Injective (J i)) ∧
        (∀ (A : ∀ i, C i) (R : ∀ i, InjectiveResolution (A i)),
          ∃ K : InjectiveResolution A,
            (∀ n : ℕ, K.cocomplex.X n = fun i ↦ (R i).cocomplex.X n) ∧
            (∀ n m : ℕ, HEq (K.cocomplex.d n m)
              (fun i ↦ (R i).cocomplex.d n m)) ∧
            HEq (K.ι.f 0) (fun i ↦ (R i).ι.f 0)) := by
  sorry

end CategoryTheory
