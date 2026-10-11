/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.CategoryTheory.ExactCouple

/-!
# Exactness of derived bigraded couples

Source: Stacks Project, Homological Algebra, Lemma 12.21.2 (Tag 011R),
Definition 12.21.3 (Tag 011S), and Remark 12.21.5 (Tag 0AMJ)
(blueprint: lem-sp-derived-couple-exact).
-/

@[expose] public section

universe u v

open CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

/-- Kernel and image identities, and unique induced exact maps, for a type-`s` couple.
Source: Stacks Project, Tags 011R and 0AMJ (blueprint: lem-sp-derived-couple-exact).

Proof (steps 0--10 of the node). Work with generalized elements `T ⟶ Y`, allowing
precomposition with epimorphic refinements, as in `lem-sp-abelian-refinements`.
Membership in kernels means annihilation; membership in images means lifting after
an epimorphic refinement. Membership descends along epimorphisms because a subobject
in an abelian category is the kernel of its cokernel. These tests determine subobjects.
The three complex relations give `d d = g f g f = 0`. Consequently boundaries are cycles,
and the projection from cycles to their quotient is the cokernel of the lifted incoming
boundary. The kernel test gives `ker d = f⁻¹(ker g) = f⁻¹(im alpha)`.
The refined image test gives `im d = g(im f) = g(ker alpha)`.
Restrict `alpha` to its image; the inclusion is mono, so this restriction is unique.
The cycle restriction of `f` lands in `im alpha` by the kernel identity and kills
boundaries by `f g = 0`, so it descends uniquely through the cycle quotient.
The map `g` lands in cycles by `g f g = 0`. Composing with the quotient kills
`ker alpha = im f`, so it descends uniquely through the image epimorphism of `alpha`.
For exactness between `f'` and `alpha'`, lift an element killed by `alpha'` along `f`
after refinement; its lift is a cycle because the image of `alpha` is killed by `g`.
For exactness between `g'` and `f'`, lift to cycles along the quotient, then lift along
`g` using `ker f = im g`; the image under the image epimorphism of `alpha` is a `g'`-lift.
For exactness between `alpha'` and `g'`, lift along the image epimorphism of `alpha`.
If its `g`-image is a boundary, subtract an `f`-lift of that boundary after refinement.
The difference is killed by `g`, hence lifts along `alpha`; projecting this lift to
`im alpha` gives the required `alpha'`-preimage. The three complex identities follow
from the defining commutative equations, cancellation of mono inclusions and epi
projections, and the original complex identities. These chases use only the abelian
category axioms and `lem-sp-abelian-refinements`, not an embedding theorem. -/
theorem derived_couple_exact {C : Type u} [Category.{v} C] [Abelian C]
    {s : ℕ} (X : BigradedExactCouple C s) :
    (∀ p q : ℤ,
      let a : X.D (p + 3) (q - 2) ⟶ X.D (p + 2) (q - 1) :=
        X.alpha (p + 3) (q - 2) ≫ eqToHom (by congr 1 <;> omega)
      kernelSubobject (X.d p q) =
          (Subobject.pullback (X.f p q)).obj (kernelSubobject (X.g (p + 2) (q - 1))) ∧
      kernelSubobject (X.d p q) =
          (Subobject.pullback (X.f p q)).obj (imageSubobject a) ∧
      kernelSubobject (X.g (p + 2) (q - 1)) = imageSubobject a ∧
      imageSubobject (X.d p q) =
          imageSubobject ((imageSubobject (X.f p q)).arrow ≫ X.g (p + 2) (q - 1)) ∧
      imageSubobject (X.d p q) =
          imageSubobject
            ((kernelSubobject (X.alpha (p + 2) (q - 1))).arrow ≫
              X.g (p + 2) (q - 1)) ∧
      imageSubobject (X.f p q) = kernelSubobject (X.alpha (p + 2) (q - 1)) ∧
      imageSubobject (kernel.ι (X.d p q) ≫ X.f p q) ≤ imageSubobject a) ∧
    (∀ p q : ℤ,
      X.gToCycles p q ≫ kernel.ι (X.d (p + s) (q - s)) = X.g p q) ∧
    (∀ p q : ℤ, X.d p q ≫ X.d (p + 2 + s) (q - 1 - s) = 0) ∧
    (∀ p q : ℤ,
      kernel.ι (factorThruImage (X.alpha (p + 1) (q - 1))) ≫
        X.gToCycles (p + 1) (q - 1) ≫
          X.derivedEProjection ((p + 1) + s) ((q - 1) - s) = 0) ∧
    (∃ M : DerivedMaps X,
      (∀ (p q : ℤ) (a : X.derivedD p q ⟶ X.derivedD (p - 1) (q + 1)),
        a ≫ X.derivedDInclusion (p - 1) (q + 1) = X.derivedDInclusion p q ≫ X.alpha p q →
          a = M.alpha p q) ∧
      (∀ (p q : ℤ) (b : X.derivedE p q ⟶ X.derivedD (p + 2) (q - 1)),
        X.derivedEProjection p q ≫ b ≫ X.derivedDInclusion (p + 2) (q - 1) =
            kernel.ι (X.d p q) ≫ X.f p q →
          b = M.f p q) ∧
      (∀ (p q : ℤ) (c : X.derivedD p q ⟶ X.derivedE (p + (s + 1)) (q - (s + 1))),
        factorThruImage (X.alpha (p + 1) (q - 1)) ≫ c =
            X.gToCycles (p + 1) (q - 1) ≫
              X.derivedEProjection ((p + 1) + s) ((q - 1) - s) ≫
                eqToHom (by congr 1 <;> omega) →
          c = M.g p q)) := by
  sorry

/-- Iterated derived couples are the images of the iterated `alpha` maps.
Here `n` is `r - 2`: the actual page number is `n + 2`. The quantified families
`A` and `I` are uniquely prescribed by their recurrences: `A` is the incoming
`alpha` power and `I` is the composite of all the canonical image inclusions.
Source: Stacks Project, Tags 011S and 0AMJ (blueprint: lem-sp-derived-couple-exact).

Proof (step 11 of the node). Induct on `n`. At `n = 0` the couple is the original
one and both maps are identities. For the induction step use steps 1--9, stated in
`derived_couple_exact`, for the type-`n` couple. Its next `D` is the image of its
restricted `alpha`. Composing the image inclusion with the previous inclusion is
mono; its image in the original `D` equals the image of the next power of `alpha`.
Indeed both images consist of elements which, after epimorphic refinement, are
`alpha` of an element of the previous image, by the image membership tests of
`lem-sp-abelian-refinements`. The defining equation for the restriction persists
under composition with the previous inclusion. The `E` recurrence is precisely the
cokernel of the incoming differential lifted into the outgoing kernel, hence cycles
modulo boundaries. The types of `pageCouple`, its `alpha`, `f`, `g`, and `d` give
respectively type `n = r-2` and bidegrees `(-1,1)`, `(2,-1)`, `(n,-n)` and
`(n+2,-n-1) = (r,1-r)`. This proves every asserted recurrence and image formula. -/
theorem pageCouple_image {C : Type u} [Category.{v} C] [Abelian C]
    (X : BigradedExactCouple C 0) :
    ∃ (A : ∀ (n : ℕ) (p q : ℤ), X.D (p + n) (q - n) ⟶ X.D p q)
      (I : ∀ (n : ℕ) (p q : ℤ), (X.pageCouple n).D p q ⟶ X.D p q),
      (∀ p q : ℤ, A 0 p q = eqToHom (by congr 1 <;> omega)) ∧
      (∀ (n : ℕ) (p q : ℤ), A (n + 1) p q =
        X.alpha (p + (n + 1 : ℕ)) (q - (n + 1 : ℕ)) ≫
          eqToHom (by congr 1 <;> omega) ≫ A n p q) ∧
      (∀ p q : ℤ, I 0 p q = 𝟙 (X.D p q)) ∧
      (∀ (n : ℕ) (p q : ℤ), I (n + 1) p q =
        (X.pageCouple n).derivedDInclusion p q ≫ I n p q) ∧
      (∀ (n : ℕ) (p q : ℤ), Mono (I n p q)) ∧
      (∀ (n : ℕ) (p q : ℤ), imageSubobject (I n p q) = imageSubobject (A n p q)) ∧
      (∀ (n : ℕ) (p q : ℤ),
        (X.pageCouple n).alpha p q ≫ I n (p - 1) (q + 1) =
          I n p q ≫ X.alpha p q) ∧
      (∀ (n : ℕ) (p q : ℤ), (X.pageCouple (n + 1)).E p q =
        cokernel (kernel.lift ((X.pageCouple n).d p q)
          ((X.pageCouple n).dInto p q) ((X.pageCouple n).dInto_comp_d p q))) := by
  sorry

end CategoryTheory.BigradedExactCouple
