/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.Algebra.Homology.RingedSiteGlobalRHomModel


/-! Models used in the global derived Hom and inverse-limit comparison. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v r a w z

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RingedSiteGlobalRHom

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max c v r})
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w} (Modules.{c, v, max c v r} R)]
  (A : Type a) [CommRing A] (φ : A →+* Scalars.{c, v, max c v r} R)
  [HasDerivedCategory.{z} (ModuleCat.{max c v r} A)]

/-- Ordinary limit and normalized Roos models on resolved strict towers.

Source: Stacks Project, sites-cohomology.tex, Tag 0941, proof of
lemma-derived-limit-is-ok; derived.tex, Tag 08BJ.
(blueprint: lem-sfb-global-rhom-resolved-tower-models).

Proof: For a resolved tower, injectivity of each term makes every transition split epic.
The injective-tower Roos theorem identifies Q of its termwise product with the
product of the Q values, and the kernel of 1-shift with the ordinary limit.
Transport its distinguished triangle to the chosen derived product. Its first map
has exactly the ordinary limit projections; this gives the source triangle.
In each degree, representative(L,I) is the product over p of Hom(L^p,I^(p+q)),
with the section-ring action restricted along φ. Maps into limits are compatible
families, and interchanging the products identifies representative(L,lim I)
with lim representative(L,I), with identical differentials. This is precisely
limit.post, proving its invertibility. The split transitions of I induce split
surjections on each product of Hom groups. Recursively solve x_n-t_n x_(n+1)=b_n,
starting with x_0=0, to see that 1-shift is surjective in every degree. Its kernel
is the ordinary limit. The kernel-to-shifted-cone lemma and exact products of
A-modules give the target Roos triangle. Its kernel inclusion is (0,z), so its
first arrow has the stated projections, with no sign change. These constructions
also cover zero or identity transitions and zero objects; no exact-products
hypothesis is imposed on module sheaves. -/
theorem resolved_tower_models
    (L : CochainComplex (Modules.{c, v, max c v r} R) ℤ) :
    (∀ I : (resolvedProperty.{c, v, r} R).FullSubcategory,
      IsIso (limit.post I.obj.asFunctor (representative.{c, v, r, a} R A φ L))) ∧
      (∀ I : (resolvedProperty.{c, v, r} R).FullSubcategory,
        ∃ hp : HasProduct (fun n : ℕ ↦
            DerivedCategory.Q.{w}.obj (I.obj.asFunctor.obj (op n))),
        ∃ (p : DerivedCategory.Q.{w}.obj (limit I.obj.asFunctor) ⟶
            ∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj (I.obj.asFunctor.obj (op n))))
          (δ : (∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj
              (I.obj.asFunctor.obj (op n)))) ⟶
            (DerivedCategory.Q.{w}.obj (limit I.obj.asFunctor))⟦(1 : ℤ)⟧),
          IsDerivedLimitTriangle
            (fun n : ℕ ↦ DerivedCategory.Q.{w}.map
              (I.obj.asFunctor.map (homOfLE (Nat.le_succ n)).op))
            (DerivedCategory.Q.{w}.obj (limit I.obj.asFunctor)) p δ ∧
          ∀ n : ℕ, p ≫ Pi.π _ n = DerivedCategory.Q.{w}.map
            (limit.π I.obj.asFunctor (op n))) ∧
      (∀ I : (resolvedProperty.{c, v, r} R).FullSubcategory,
        ∃ hp : HasProduct (fun n : ℕ ↦ DerivedCategory.Q.obj
            (((representativeTowers.{c, v, r, a} R A φ L).obj I).obj (op n))),
        ∃ (p : (globalHomLimit.{c, v, r, a} R A φ L).obj I ⟶
            ∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.obj
              (((representativeTowers.{c, v, r, a} R A φ L).obj I).obj (op n))))
          (δ : (∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.obj
              (((representativeTowers.{c, v, r, a} R A φ L).obj I).obj (op n)))) ⟶
            ((globalHomLimit.{c, v, r, a} R A φ L).obj I)⟦(1 : ℤ)⟧),
          IsDerivedLimitTriangle
            (fun n : ℕ ↦ DerivedCategory.Q.map
              (((representativeTowers.{c, v, r, a} R A φ L).obj I).map
                (homOfLE (Nat.le_succ n)).op))
            ((globalHomLimit.{c, v, r, a} R A φ L).obj I) p δ ∧
          ∀ n : ℕ, p ≫ Pi.π _ n = DerivedCategory.Q.map
            (limit.π ((representativeTowers.{c, v, r, a} R A φ L).obj I) (op n))) := by sorry

end CategoryTheory.RingedSiteGlobalRHom
