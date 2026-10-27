/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.RingedKFlatSingleTensorComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Algebra.Homology.BoundedFlatReplacement
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.SiteFlatOpcyclesTorCriterion

/-! # Flat lower opcycles of bounded flat derived approximations

Source: Stacks Project, sites-cohomology.tex, Tag 08G7, lemma-perfect-precise,
proof through flatness of the lower cokernel, before the finite-presentation step.
(blueprint: lem-sfb-flat-approximation-opcycle)

The site is essentially small in the coefficient/module universe. Its object and
morphism universes are independent. The tensor is the published K-flat localization.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

attribute [local instance] hasSheafify_coefficientUniverse
  wEqualsLocallyBijective_coefficientUniverse

/-- The lower cokernel of a bounded flat approximation to a derived object of Tor amplitude
`[a,b]` is flat. The approximation morphism is in the derived category; no chain-map
representative, finite generation, or local projectivity of its terms is assumed.

Source: Stacks Project, sites-cohomology.tex, Tag 08G7, lemma-perfect-precise,
proof through flatness of E', before its finite-presentation argument.
(blueprint: lem-sfb-flat-approximation-opcycle)

Proof:
1. Tensor K with the unit sheaf. A flat-term K-flat resolution
   [lem-pc-kflat-resolution], its single-tensor comparison
   [lem-sf-ringed-kflat-single-tensor-comparison], and the unit isomorphism
   [lem-pc-sheaf-modules-tensor-closed] identify this tensor with K. Thus K has no
   cohomology outside [a,b].
2. Put Z = ker(d_P^(a-1)). Resolve Z[0] by a flat complex F supported in degrees
   at most zero, with an epimorphic quasi-isomorphism to Z[0]
   [lem-pc-kflat-bounded-flat-replacement]. Splice F below P^(a-1): E^j = P^j for
   j >= a-1, and E^j = F^(j-a+2) for j <= a-2. The joining differential is
   F^0 -> Z -> P^(a-1). Its adjacent composites vanish by the augmentation identity
   and the kernel identity. The complex E is bounded above with flat terms.
3. Map E to the good truncation T = tau_ge_a P [def-kun-truncations], using the
   quotient P^a -> coker(d_P^(a-1)) in degree a, identity above a, and zero below.
   Exactness of the augmented F-resolution kills cohomology below a. In degree a,
   both cohomologies are ker(d_P^a)/im(d_P^(a-1)); above a they agree. The map is
   therefore a quasi-isomorphism [def-weil-abstract-derived-category].
4. Apply functorial truncation to f [lem-weil-heart-short-exact-triangles]. Its
   retained cohomology maps are H^j(f), hence isomorphisms. The truncation unit of
   K is also a cohomology isomorphism by step 1. All objects are bounded below
   [def-weil-pbc-bounded-derived-subcategories]; cohomology detects isomorphisms
   there [lem-weil-pbc-derived-plus-iso-on-cohomology]. Thus Q(E) is isomorphic to K.
5. E is K-flat [lem-weil-pbc-independent-bounded-flat-kflat]. For every module N,
   the single-tensor comparison [lem-sf-ringed-kflat-single-tensor-comparison]
   identifies its ordinary tensor with K tensor-derived N. Tor amplitude gives
   vanishing in degree a-1. Sheaf tensor symmetry
   [lem-pc-sheaf-modules-tensor-closed] gives the same for N tensor E, whose
   differential is 1_N tensor d_E.
6. The universal-tensor criterion [lem-weil-pbc-site-flat-opcycles-tor-criterion]
   gives flatness of coker(d_E^(a-1)). The construction leaves this differential
   equal to d_P^(a-1), so this is the stated cokernel. No finiteness is used.
-/
theorem isFlatOnSite_cokernel_of_bounded_flat_approximation
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]
    (a b : ℤ) (_hab : a ≤ b)
    (K : DerivedCategory (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)))
    (_hTor : ∀ (N : ringedSiteModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
        (j : ℤ), j < a ∨ b < j →
      IsZero ((DerivedCategory.homologyFunctor _ j).obj
        ((siteDerivedTensorIndependentCoefficients J R).obj
          (K, (DerivedCategory.singleFunctor _ 0).obj N))))
    (P : CochainComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
    (_hbounded : ∃ l n : ℤ, ∀ j : ℤ, j < l ∨ n < j → IsZero (P.X j))
    (_hflat : ∀ j : ℤ, IsFlatOnSite (J := J) (R := R) (P.X j))
    (_hzero : ∀ j : ℤ, j < a - 1 → IsZero (P.X j))
    (f : DerivedCategory.Q.obj P ⟶ K)
    (_hf : ∀ j : ℤ, a ≤ j → IsIso ((DerivedCategory.homologyFunctor _ j).map f)) :
    IsFlatOnSite (J := J) (R := R) (cokernel (P.d (a - 1) a)) := by
  sorry

end SheafOfModules
