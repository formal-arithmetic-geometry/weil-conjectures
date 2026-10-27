module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.CategoryTheory.KInjectiveComputes
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Finite-window comparison for bounded-below derived sections

Source: Stacks Project, Cohomology on Sites, Tag 0D6T, first paragraph of the proof;
Derived Categories, Tag 015J
(blueprint: lem-sfb-ringed-bounded-below-section-window-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe c v r w z

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  (R : Sheaf J CommRingCat.{r})
  [HasDerivedCategory.{w} (ringedSiteModules.{r, r, v, c}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))]
  [HasDerivedCategory.{z} AddCommGrpCat.{r}]

/-- Right derived evaluation at a site object, with its scalar action forgotten.
This is the existing total right derived functor of the literal section functor;
no comparison map or resolution is chosen independently.

Source: Stacks Project, Section 07A5 and Tag 0D6T
(blueprint: lem-sfb-ringed-bounded-below-section-window-comparison).
The Grothendieck theorem for a site essentially small in the coefficient universe
supplies K-injective resolutions without identifying the site universes. -/
def ringedSiteDerivedEvaluation (U : C) :
    DerivedCategory (ringedSiteModules.{r, r, v, c}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ⥤
        DerivedCategory AddCommGrpCat.{r} := by
  let S := (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
  letI : IsGrothendieckAbelian.{r} (ringedSiteModules.{r, r, v, c} S) :=
    SheafOfModules.isGrothendieckAbelian_coefficientUniverse S
  exact (SheafOfModules.forget S ⋙ PresheafOfModules.evaluation S.obj (op U) ⋙
    forget₂ (ModuleCat.{r} (S.obj.obj (op U))) AddCommGrpCat.{r}).rightDerivedFunctor

/-- Finite-window comparison for the actual map on derived sections.

Source: Stacks Project, Tag 0D6T, first paragraph of the proof, with the bounded-below
hypercohomology spectral sequence of Tag 015J
(blueprint: lem-sfb-ringed-bounded-below-section-window-comparison).

Proof:
1. Sections followed by forgetting scalars are additive and left exact. Module sheaves
   have K-injective resolutions by prop-pur-kinjective-resolutions-exist. Abelian groups
   are Grothendieck (lem-weil-pbc-ring-modules-grothendieck-abelian at the integers).
   The chosen right derived functor computes the specified sections, by
   lem-sp-kinjective-computes.
2. Complete f to a triangle E → F → K → E[1]. The cohomology long exact sequence
   (lem-sf-derived-homology-long-exact) gives an extension of coker H^q(f) by
   ker H^(q+1)(f). Thus H^q(K) lies in S, K is bounded below using the minimum of
   the two lower bounds, and H^q(K) vanishes for a-d-1 ≤ q ≤ b.
3. Represent K by a bounded-below complex using def-sbc-standard-tstructure-derived-category.
   Apply thm-sp-truncation-e2 and lem-sp-kinjective-computes: E₂^(p,q) is
   H^p(U,H^q(K)), zero for p < 0 and for p > d, and converges with a finite filtration.
4. For t = r-1 or r and a ≤ r ≤ b, every remaining index 0 ≤ p ≤ d has
   a-d-1 ≤ t-p ≤ b. Hence its E₂ term vanishes. All later pages and the associated
   graded pieces vanish; the finite filtration gives H^(r-1)(U,K) = H^r(U,K) = 0.
5. The derived functor is triangulated (lem-pc-right-derived-functor-triangulated;
   lem-weil-pbc-kinjective-functorial-existence supplies resolutions). Its triangle's
   long exact sequence has these zero outer terms, so its middle arrow is invertible.
   This arrow is precisely H^r(RΓ(U,f)), not a newly chosen map. -/
theorem ringed_boundedBelow_section_window_comparison
    (S : ObjectProperty (ringedSiteModules.{r, r, v, c}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)))
    [S.IsClosedUnderIsomorphisms] (hzero : S 0)
    (hkernel : ∀ {M N : ringedSiteModules.{r, r, v, c}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
      (g : M ⟶ N), S M → S N → S (kernel g))
    (hcokernel : ∀ {M N : ringedSiteModules.{r, r, v, c}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)}
      (g : M ⟶ N), S M → S N → S (cokernel g))
    [S.IsClosedUnderExtensions] (U : C) (d : ℤ) (hd : 0 ≤ d)
    (hcd : ∀ (M : ringedSiteModules.{r, r, v, c}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)), S M →
      ∀ p : ℤ, d < p → IsZero ((DerivedCategory.homologyFunctor _ p).obj
        ((ringedSiteDerivedEvaluation R U).obj
          ((DerivedCategory.singleFunctor _ 0).obj M))))
    {E F : DerivedCategory (ringedSiteModules.{r, r, v, c}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))}
    (f : E ⟶ F)
    (hE : ∃ m : ℤ, ∀ q : ℤ, q < m →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj E))
    (hF : ∃ m : ℤ, ∀ q : ℤ, q < m →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj F))
    (hES : ∀ q : ℤ, S ((DerivedCategory.homologyFunctor _ q).obj E))
    (hFS : ∀ q : ℤ, S ((DerivedCategory.homologyFunctor _ q).obj F))
    (a b : ℤ) (hab : a ≤ b)
    (hf : ∀ q : ℤ, a - d - 1 ≤ q → q ≤ b + 1 →
      IsIso ((DerivedCategory.homologyFunctor _ q).map f)) :
    ∀ n : ℤ, a ≤ n → n ≤ b →
      IsIso ((DerivedCategory.homologyFunctor _ n).map
        ((ringedSiteDerivedEvaluation R U).map f)) := by
  sorry

end CategoryTheory
