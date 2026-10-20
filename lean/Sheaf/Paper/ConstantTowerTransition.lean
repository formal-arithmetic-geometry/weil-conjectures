/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q130
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Mathlib.CategoryTheory.Abelian.RightDerived
import Sheaf.AlgebraicGeometry.ProEtaleModuleDirectImageLeftExact
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Sheaf.CategoryTheory.KInjectiveDerivedMapComputation
import Sheaf.CategoryTheory.NormalizedDerivedComparisonCommonResolution
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage

/-!
# Degree-zero direct image and coefficient transition maps

Source: Stacks Project, derived.tex, Tag 05TD (`lemma-left-exact-higher-derived`),
and the normalized coefficient comparison
(blueprint: lem-pod-constant-tower-transition).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The canonical augmentation isomorphism from ordinary direct image to degree-zero
unbounded derived direct image. The first comparison uses nonnegative injective
resolutions; the second is the inverse of the augmentation to the zeroth classical
right derived functor. Thus no arbitrary isomorphism is chosen.
Source: Stacks Project, Tag 05TD, part (3)
(blueprint: lem-pod-constant-tower-transition). -/
noncomputable def constantTowerTransitionAugmentation
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (lowerStar (ModuleCat.{u + 1} A) f).obj F ≅
      (DerivedCategory.homologyFunctor
        (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) 0).obj
        ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor
            (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) 0).obj F)) :=
  ((lowerStar (ModuleCat.{u + 1} A) f).homologyRightDerivedFunctorObjSingleFunctorIso F 0 ≪≫
    (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedZeroIsoSelf.app F).symm

/-- The derived coefficient comparison retains the ordinary direct-image section map
under the canonical degree-zero augmentations. The single/restriction comparison and
exact-restriction/homology comparison are included explicitly.
Source: Stacks Project, Tag 05TD, part (3), and the K-injective normalization of
lem-weil-proetale-direct-image-restriction-of-scalars
(blueprint: lem-pod-constant-tower-transition).

Proof: (1) On the small pro-etale sites take nonnegative injective resolutions
s : F[0] -> L, a : G[0] -> J, and b : (Res G)[0] -> I. Grothendieck existence
(prop-pur-kinjective-resolutions-exist, lem-sp-grothendieck-enough-injectives) supplies
these resolutions (lem-weil-pbc-left-exact-injective-resolution-degree-zero).
Their bounded-below injective terms make them K-injective
(lem-weil-pbc-bounded-below-injectives-kinjective). Restriction is exact.
(2) The Hom bijection into I (lem-weil-pbc-kinjective-hom-derived) lifts the two derived
maps to v : Res J -> I and h : L -> I. The equations v Res(a) = b and h s = b u[0]
hold strictly: a homotopy from a degree-zero complex into I has its only relevant
component in I^{-1} = 0. The first equation also makes v a quasi-isomorphism.
(3) Left exactness (lem-weil-proetale-module-direct-image-left-exact) gives the
augmentation isomorphisms alpha_F, alpha_G, alpha_r. The sectionwise formula
(def-weil-proetale-module-direct-image) identifies f_* Res with Res f_* on maps as
well as objects. Exactness identifies the restricted alpha_G with alpha'_G.
(4) Use lem-sf-kinjective-derived-map-computation for the map u. Apply
lem-sf-normalized-derived-comparison-common-resolution to a and v and the normalization
of lem-weil-proetale-direct-image-restriction-of-scalars: c is represented by
Q(f_*v) inverse. This does not assume that Res J is K-injective.
(5) Put V = H^0(f_*v), H = H^0(f_*h). Composing with degree-zero cycles inclusions
reduces V alpha'_G = alpha_r and H alpha_F = alpha_r f_*u to the strict chain equations
in (2). These inclusions are monic since all degree-minus-one terms vanish. Cancel V
to obtain V^{-1} H alpha_F = alpha'_G f_*u, the displayed equality. -/
theorem constantTowerTransition
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
    (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B))
    (u : F ⟶ (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).obj G) :
    (constantTowerTransitionAugmentation A f F).hom ≫
        (DerivedCategory.homologyFunctor
          (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) 0).map
          ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.map
              ((DerivedCategory.singleFunctor
                (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) 0).map u) ≫
            (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.map
              (((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapDerivedCategorySingleFunctor
                0).inv.app G) ≫
            (fixedScalarRestrictionDirectImage φ f).hom.app
              ((DerivedCategory.singleFunctor
                (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) 0).obj G)) =
      (lowerStar (ModuleCat.{u + 1} A) f).map u ≫
        (Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ).map
          (constantTowerTransitionAugmentation B f G).hom ≫
        ((Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ).mapDerivedCategoryHomologyFunctorIso
          0).hom.app
          ((lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctor.obj
            ((DerivedCategory.singleFunctor
              (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) 0).obj G)) := by
  sorry

end AlgebraicGeometry.ProEtale
