/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.Triangulated.DerivedLimitExistence
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Derived limits of surjective towers on the small pro-etale site

Source: Bhatt--Scholze, Proposition 3.1.10, Proposition 3.2.3(1), and Proposition 4.2.8;
Stacks Project, Tags 07KC, 08TC, and 06XS
(blueprint: lem-weil-proetale-surjective-tower-derived-limit).

`n : ℕ` denotes positive level `n + 1`. Products and inverse limits are the existing
Mathlib constructions. The derived product is asserted to exist and the Roos assertion
works for every choice of its limit structure, without an existence hypothesis.

## Main declarations

* `surjectiveTower_hasSheafify` and `surjectiveTower_wEqualsLocallyBijective` transport
  Mathlib's sheafification structures to larger coefficient universes.
* `proEtale_surjectiveTower_derivedLimit` states the short exact Roos sequence, its
  derived-limit triangle, and uniqueness of compatible lifts from degree-zero sheaves.
-/

@[expose] public section

set_option autoImplicit false

universe t u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Sheafification of large abelian coefficients on the unchanged small pro-etale site.
This is Mathlib's sheafification transported through an equivalent small model.
Source: Stacks Project, Tags 00W1 and 03DA
(blueprint: lem-weil-proetale-surjective-tower-derived-limit). -/
noncomputable instance surjectiveTower_hasSheafify (Y : Scheme.{t}) :
    HasSheafify (Scheme.ProEt.topology Y) AddCommGrpCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} Y.ProEt := essentiallySmallSelf.{u} _
  hasSheafifyEssentiallySmallSite.{t, max u (t + 1), t + 1,
    max u (t + 1) + 1, max u (t + 1)} _ _

/-- Large-coefficient sheafification detects the same locally bijective maps.
This reuses Mathlib's small-model transport without changing the original site.
Source: Stacks Project, Tags 00W1 and 03DA
(blueprint: lem-weil-proetale-surjective-tower-derived-limit). -/
noncomputable instance surjectiveTower_wEqualsLocallyBijective (Y : Scheme.{t}) :
    (Scheme.ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} Y.ProEt := essentiallySmallSelf.{u} _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{t, max u (t + 1),
    t + 1, max u (t + 1) + 1, max u (t + 1)} _

/-- A surjective tower of module sheaves has its ordinary limit as a derived limit,
with its canonical projections and the triangle of its short exact Roos sequence.

Source: Bhatt--Scholze, Proposition 3.1.10 (sign changed to `1 - s`), Proposition 3.2.3(1),
and Proposition 4.2.8; Stacks Project, Tags 07KC, 08TC, and 06XS
(blueprint: lem-weil-proetale-surjective-tower-derived-limit).

Proof plan:
1. Form the sectionwise product by `lem-weil-proetale-countable-products-exact` and the
inverse limit by `def-pur-sheaf-inverse-limit`. The existing transition endomorphism is
`1 - s` with nth coordinate `x n - t n (x (n + 1))`.
2. Cover any site object by affine weakly contractible objects using
`lem-weil-pbc-proetale-affine-wcontractible-covering-family`. Exact evaluation from
`lem-weil-pbc-proetale-wcontractible-affine-evaluation-colimits` makes all transitions
surjective on the sections of each member of this same cover.
3. Choose set-theoretic sections sigma_n of these surjections. Starting with x_0 = 0,
set x_(n+1) = sigma_n (x_n - y_n). This locally lifts any section of the product under
`1 - s`. These choices need not be linear or natural; only the preimage is needed.
4. Sheaf uniqueness (`def-weil-pbc-sites-and-cohomology`) makes this local lifting an
epimorphism. Its sectionwise kernel is exactly the compatible sequences, with inclusion
the tuple of limit projections. Thus the displayed short complex is short exact.
5. Exact countable products and clause 2 of `lem-weil-derived-limit-existence` show
that the degree-zero product, with its localized projections, is a derived product.
No enough-injectives hypothesis is used. The short exact sequence gives the canonical
triangle `hSES.singleTriangle` by `lem-sf-derived-ses-triangle`. The product comparison
identifies its second arrow with `1 - s`, making it `def-weil-derived-limit`'s triangle.
6. For compatible g_n, the sheaf limit gives a unique sheaf map h_0. Full faithfulness
of the degree-zero embedding (`lem-weil-pbc-derived-single-fully-faithful`) says every
derived map between these sheaves comes from a unique sheaf map. Its composites with
all limit projections determine it. Thus the unique derived lift is the image of h_0.
7. For the parenthesis, the standard t-structure (`def-sbc-standard-tstructure-derived-category`)
and orthogonality (`def-weil-t-structure`) give Hom(G[0], P[0][-1]) = 0. The shift is
supported in cohomological degree 1. Two lifts have zero difference; in particular that
difference factors through the zero morphism to P[0][-1] and the shifted connecting map.
-/
theorem proEtale_surjectiveTower_derivedLimit
    (Y : Scheme.{t})
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    [HasDerivedCategory.{w} (ringedSiteModules.{max u (t + 1)}
      ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R))]
    (F : ℕ → ringedSiteModules.{max u (t + 1)}
      ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R))
    (t : ∀ n : ℕ, F (n + 1) ⟶ F n) (ht : ∀ n : ℕ, Epi (t n)) :
    ∃ (hzero :
        (Pi.lift (fun n : ℕ ↦ limit.π (Functor.ofOpSequence t) (op n))) ≫
          towerTransitionEndomorphism t = 0)
      (hSES : (ShortComplex.mk
        (Pi.lift (fun n : ℕ ↦ limit.π (Functor.ofOpSequence t) (op n)))
        (towerTransitionEndomorphism t) hzero).ShortExact),
      Epi (towerTransitionEndomorphism t) ∧
      Nonempty (IsLimit (KernelFork.ofι
        (Pi.lift (fun n : ℕ ↦ limit.π (Functor.ofOpSequence t) (op n))) hzero)) ∧
      Nonempty (IsLimit (Fan.mk ((DerivedCategory.singleFunctor.{w} _ 0).obj (∏ᶜ F))
        (fun n : ℕ ↦ (DerivedCategory.singleFunctor.{w} _ 0).map (Pi.π F n)))) ∧
      hSES.singleTriangle ∈ distTriang _ ∧
      (∀ [hprod : HasProduct (fun n : ℕ ↦
          (DerivedCategory.singleFunctor.{w} _ 0).obj (F n))],
        ∃ e : (DerivedCategory.singleFunctor.{w} _ 0).obj (∏ᶜ F) ≅
            ∏ᶜ (fun n : ℕ ↦ (DerivedCategory.singleFunctor.{w} _ 0).obj (F n)),
          (∀ n : ℕ, e.hom ≫
              Pi.π (fun n : ℕ ↦ (DerivedCategory.singleFunctor.{w} _ 0).obj (F n)) n =
            (DerivedCategory.singleFunctor.{w} _ 0).map (Pi.π F n)) ∧
          IsDerivedLimitTriangle
            (K := fun n : ℕ ↦ (DerivedCategory.singleFunctor.{w} _ 0).obj (F n))
            (fun n : ℕ ↦ (DerivedCategory.singleFunctor.{w} _ 0).map (t n))
            ((DerivedCategory.singleFunctor.{w} _ 0).obj (limit (Functor.ofOpSequence t)))
            ((DerivedCategory.singleFunctor.{w} _ 0).map
              (Pi.lift (fun n : ℕ ↦ limit.π (Functor.ofOpSequence t) (op n))) ≫ e.hom)
            (e.inv ≫ hSES.singleδ)) ∧
      (∀ (G : ringedSiteModules.{max u (t + 1)}
          ((sheafCompose (Scheme.ProEt.topology Y)
            (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R))
        (g : ∀ n : ℕ, G ⟶ F n), (∀ n : ℕ, g (n + 1) ≫ t n = g n) →
        ∃ (h₀ : G ⟶ limit (Functor.ofOpSequence t)),
          (∀ n : ℕ, h₀ ≫ limit.π (Functor.ofOpSequence t) (op n) = g n) ∧
          (∃! h : (DerivedCategory.singleFunctor.{w} _ 0).obj G ⟶
              (DerivedCategory.singleFunctor.{w} _ 0).obj (limit (Functor.ofOpSequence t)),
            h ≫ (DerivedCategory.singleFunctor.{w} _ 0).map
                (Pi.lift (fun n : ℕ ↦ limit.π (Functor.ofOpSequence t) (op n))) =
              (DerivedCategory.singleFunctor.{w} _ 0).map (Pi.lift g)) ∧
          (∀ h : (DerivedCategory.singleFunctor.{w} _ 0).obj G ⟶
              (DerivedCategory.singleFunctor.{w} _ 0).obj (limit (Functor.ofOpSequence t)),
            h ≫ (DerivedCategory.singleFunctor.{w} _ 0).map
                (Pi.lift (fun n : ℕ ↦ limit.π (Functor.ofOpSequence t) (op n))) =
              (DerivedCategory.singleFunctor.{w} _ 0).map (Pi.lift g) →
            h = (DerivedCategory.singleFunctor.{w} _ 0).map h₀) ∧
          (∀ k : (DerivedCategory.singleFunctor.{w} _ 0).obj G ⟶
            ((DerivedCategory.singleFunctor.{w} _ 0).obj (∏ᶜ F))⟦(-1 : ℤ)⟧, k = 0)) := by
  sorry

end AlgebraicGeometry.ProEtale
