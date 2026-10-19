/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Sheaf.Algebra.Homology.KInjectiveProductsTermwise
import Sheaf.Algebra.Homology.KInjectiveProducts
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.CategoryTheory.Triangulated.MilnorSequence
import Sheaf.CategoryTheory.DerivedLimitEventuallyIso
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.CategoryTheory.Sites.RGammaDerivedLimit
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence

/-! # Reconstruction from lower truncations on a ringed site

Source: Stacks Project, Cohomology on Sites, Tag 0D6P, lemma-is-limit-dimension
(blueprint: lem-kun-site-truncation-derived-limit).

Vanishing of H^p(V,M) is written using its defining K-injective computation: for every
K-injective resolution of the single complex M[0], the degree-p homology of its
section complex is zero. Thus no choice of a resolution or total derived functor is
introduced. The specified product lift retains all the canonical truncation maps.
-/

@[expose] public section

set_option autoImplicit false

universe c v r w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- A uniform local bound for negative cohomology sheaves gives the distinguished
Roos triangle of the lower-truncation tower, with the specified canonical projections.
Source: Stacks Project, Cohomology on Sites, Tag 0D6P
(blueprint: lem-kun-site-truncation-derived-limit).

Proof:
1. Resolve every truncation by a K-injective complex (prop-pur-kinjective-resolutions-exist).
Sectionwise products exist (lem-weil-pbc-module-sheaves-colimits-forgetful); their complex
represents the derived product (lem-pc-ringed-space-product-kinjective). Complete 1-s
by lem-weil-derived-limit-existence (1), obtaining L -> P -> P -> L[1].
2. The canonical maps satisfy f_n c_(n+1) = c_n. Their product lift is killed by 1-s.
Hom exactness (lem-weil-pbc-hom-into-triangle-exact) supplies c : E -> L with p_n c = c_n;
no uniqueness of this lift is needed.
3. On a representative, the kernel of the successive lower-truncation quotient has
terms coker d^(a-1) and im d^a in degrees a=-n-1 and a+1. Its cohomology is H^a(E)
in degree a. The complex SES triangle (lem-weil-pbc-complex-ses-triangle) yields
H^(-n-1)(E)[n+1] -> E_(n+1) -> E_n -> H^(-n-1)(E)[n+2].
4. Derived sections preserve this triangle and shifts
(lem-pc-right-derived-functor-triangulated). The long exact sequence
(lem-sf-derived-homology-long-exact) and N >= max(0,-m,d-m+1) show that both degree
m-1 and degree m section-cohomology transitions are isomorphisms for n >= N, uniformly
on B: all three intervening groups have section degree > d and sheaf degree < 0.
5. Apply lem-kun-site-rgamma-derived-limit and lem-pc-derived-limit-milnor-sequence.
The first derived limit vanishes by lem-pc-derived-limit-eventually-iso. The ordinary
limit projects isomorphically to stage N. Thus H^m(V,p_N) is an isomorphism on B.
6. The sheafification of V |-> H^m(V,T) is the underlying abelian sheaf of H^m(T):
exact sheafification commutes with cohomology, and forgetting module scalars is exact
(lem-weil-pbc-site-module-presheaf-sheafification-exact and
lem-weil-pbc-module-sheaves-colimits-forgetful). This is natural for derived morphisms
using K-injective chain-map representatives (lem-weil-pbc-kinjective-hom-derived).
7. A covering by B makes the presheaf map for p_N locally injective and surjective.
By lem-weil-pbc-site-sheafification-iso-locally-bijective its sheafification, hence
H^m(p_N), is invertible.
8. Since N >= -m, H^m(c_N) is invertible. From p_N c = c_N it follows that H^m(c)
is invertible for every m. Represent c by a chain map into a K-injective target;
it is a quasi-isomorphism and is inverted in the derived localization.
9. Transport the distinguished triangle along c. Its first arrow is exactly the
product lift of c_n. Its middle arrow remains 1-s. The final arrow is the old boundary
followed by the shifted inverse of c. This is def-weil-derived-limit, indexed by n+1.
No exactness of products of module sheaves is used. -/
theorem site_truncation_isDerivedLimitTriangle
    {C : Type c} [Category.{v} C] (J : Precoverage C)
    (_hJ : J.IsSiteForCoverings)
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max c v r}]
    [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J.toGrothendieck RingCat.{max c v r})
    (_hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{w} (ringedSiteModules.{max c v r} R)]
    (E : DerivedCategory (ringedSiteModules.{max c v r} R))
    (hE : ∃ (d : ℕ) (B : Set C),
      (∀ U : C, ∃ S : Presieve U, S ∈ J U ∧
        ∀ (V : C) (f : V ⟶ U), S f → V ∈ B) ∧
      ∀ (V : C), V ∈ B → ∀ (p : ℤ), (d : ℤ) < p → ∀ (q : ℤ), q < 0 →
        ∀ (I : CochainComplex (ringedSiteModules.{max c v r} R) ℤ)
          (ι : (CochainComplex.singleFunctor (ringedSiteModules.{max c v r} R) 0).obj
            ((DerivedCategory.homologyFunctor (ringedSiteModules.{max c v r} R) q).obj E)
              ⟶ I),
          I.IsKInjective → QuasiIso ι →
            IsZero (((SheafOfModules.toSheaf R ⋙
              sheafToPresheaf J.toGrothendieck AddCommGrpCat.{max c v r} ⋙
              (evaluation Cᵒᵖ AddCommGrpCat.{max c v r}).obj (op V)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj I |>.homology p)) :
    ∃ (_ : HasProduct (fun n : ℕ ↦ ((DerivedCategory.TStructure.t
        (C := ringedSiteModules.{max c v r} R)).truncGE (-(n : ℤ))).obj E)),
      ∃ δ : (∏ᶜ (fun n : ℕ ↦ ((DerivedCategory.TStructure.t
          (C := ringedSiteModules.{max c v r} R)).truncGE (-(n : ℤ))).obj E)) ⟶ E⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle (fun n : ℕ ↦ ((DerivedCategory.TStructure.t
          (C := ringedSiteModules.{max c v r} R)).natTransTruncGEOfLE
            (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (Int.neg_le_neg (Int.ofNat_le.mpr
              (Nat.le_succ n)))).app E) E
          (Pi.lift (fun n : ℕ ↦ ((DerivedCategory.TStructure.t
            (C := ringedSiteModules.{max c v r} R)).truncGEπ (-(n : ℤ))).app E)) δ := by
  sorry

end CategoryTheory
