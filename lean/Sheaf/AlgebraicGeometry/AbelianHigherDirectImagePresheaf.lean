/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Sheaf.AlgebraicGeometry.DerivedCategories

/-!
# Higher direct images as sheafified cohomology presheaves

Source: Stacks Project, Tag 03Q8 (blueprint: sbc-lem-higher-direct-image-presheaf).
The presheaf is written using derived Hom from the free abelian sheaf of an etale
representable. This is the standard representation of restricted hypercohomology:
Hom(Z[U ×_X Y][0], K[q]) = H^q(U ×_X Y, K|). Its restriction maps are precomposition.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Higher direct image is the sheaf associated to the restricted cohomology presheaf.
Source: Stacks Project, Tag 03Q8 (blueprint: sbc-lem-higher-direct-image-presheaf).

Proof:
1. Choose a bounded below injective representative I of K
   (lem-weil-pbc-dplus-injective-representative). It is K-injective, and derived direct
   image is represented by h_*I (def-weil-pbc-direct-image).
2. For W = U ×_X Y, restriction along the etale projection W → Y is exact
   (prop-weil-pbc-inverse-image-exact) and preserves injectives, being right adjoint
   to exact extension by zero (lem-weil-pbc-etale-restriction-injectives).
   Thus H^q(W, K|) is H^q(Gamma(W, I|)), by def-weil-pbc-etale-cohomology.
   Sections of I| over W are I(W), naturally and compatibly with differentials
   (lem-weil-pbc-etale-inverse-image-restriction). Free abelian representables
   corepresent these sections, giving the displayed derived-Hom presheaf.
3. Kernels and images in presheaves are sectionwise. Exact sheafification commutes
   with complex cohomology (lem-weil-pbc-sheafification-exact and
   lem-weil-pbc-exact-functor-complex-cohomology), identifying the sheafification of
   this presheaf with H^q(h_*I). For a sheaf use its degree-zero complex. -/
theorem nonempty_higherDirectImage_iso_sheafification_abelian {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    Nonempty
      ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (((uliftYoneda.{u + 1} ⋙
          (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
          presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
          upperStar AddCommGrpCat.{u + 1} h ⋙
          DerivedCategory.Plus.singleFunctor _ 0).op ⋙
            preadditiveYoneda.obj (K⟦q⟧))) ≅
        (DerivedCategory.Plus.homologyFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
          ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h).obj K)) := by
  sorry

/-- Higher direct image is the sheaf associated to the restricted cohomology presheaf.
Source: Stacks Project, Tag 03Q8 (blueprint: sbc-lem-higher-direct-image-presheaf).

Proof:
1. Choose a bounded below injective representative I of K
   (lem-weil-pbc-dplus-injective-representative). It is K-injective, and derived direct
   image is represented by h_*I (def-weil-pbc-direct-image).
2. For W = U ×_X Y, restriction along the etale projection W → Y is exact
   (prop-weil-pbc-inverse-image-exact) and preserves injectives, being right adjoint
   to exact extension by zero (lem-weil-pbc-etale-restriction-injectives).
   Thus H^q(W, K|) is H^q(Gamma(W, I|)), by def-weil-pbc-etale-cohomology.
   Sections of I| over W are I(W), naturally and compatibly with differentials
   (lem-weil-pbc-etale-inverse-image-restriction). Free abelian representables
   corepresent these sections, giving the displayed derived-Hom presheaf.
3. Kernels and images in presheaves are sectionwise. Exact sheafification commutes
   with complex cohomology (lem-weil-pbc-sheafification-exact and
   lem-weil-pbc-exact-functor-complex-cohomology), identifying the sheafification of
   this presheaf with H^q(h_*I). For a sheaf use its degree-zero complex. -/
theorem nonempty_higherDirectImage_iso_sheafification_abelian_single
    {X Y : Scheme.{u}} (h : Y ⟶ X) (q : ℤ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Nonempty
      ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (((uliftYoneda.{u + 1} ⋙
          (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
          presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
          upperStar AddCommGrpCat.{u + 1} h ⋙
          DerivedCategory.Plus.singleFunctor _ 0).op ⋙
            preadditiveYoneda.obj
              (((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦q⟧))) ≅
        (DerivedCategory.Plus.homologyFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
          ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  sorry

end AlgebraicGeometry.Etale
