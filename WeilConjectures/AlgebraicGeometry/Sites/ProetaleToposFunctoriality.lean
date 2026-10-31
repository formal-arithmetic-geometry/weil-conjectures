/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
public import Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlyingSupplement
public import WeilConjectures.CategoryTheory.Sites.GrothendieckTopos
import WeilConjectures.AlgebraicGeometry.Sites.ProetaleSiteProperties

/-!
# The pro-étale topos and its functoriality

Source: latest Weil conjectures blueprint, `sec-proetale-coefficients`,
`sk-def-sfb-finite-pushforward-pullback`; Stacks Project, Tags 098L, 098Z, 098T and 098U
(blueprint: sk-def-sfb-finite-pushforward-pullback).

The site is Mathlib's small pro-étale site with fpqc coverings. Schemes lie in universe `u`;
sets and abelian groups take values in the larger universe `u + 1`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The small pro-étale site is subcanonical, its set-valued sheaves form a Grothendieck
 topos, and arbitrary scheme morphisms induce geometric morphisms compatible with composition.

Source: latest blueprint, `sk-def-sfb-finite-pushforward-pullback`, statement and unit step 1;
Stacks Project, Tags 098L, 098Z, 098T(2) and 098U
(blueprint: sk-def-sfb-finite-pushforward-pullback).

Proof:
1. Apply `det-pe-topos-functoriality-site` to `X`. Its first clause gives the site axioms
   for exactly `Scheme.ProEt.precoverage X`, its second gives subcanonicity, and its third
   gives the larger-universe small-site presentation required by `IsGrothendieckTopos`.
2. Apply `det-pe-topos-functoriality-inverse-image` to `f` and `g`. Base change preserves
   covers and finite limits. The constructed inverse image `setPullback f` is left Kan
   extension followed by sheafification, adjoint to restriction `lowerStar _ f`.
   Its preservation of finite limits and all colimits gives the geometric morphism.
3. The same lemma identifies abelian inverse image on underlying set sheaves and gives
   preservation of finite limits and finite colimits, hence abelian exactness. Its last
   clause identifies the composite adjunction's unit through the canonical isomorphisms
   `setPullbackComp f g` and `lowerStarComp _ f g`; thus the geometric morphisms compose.
-/
theorem proetaleToposFunctoriality (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.ProEt.precoverage X).IsSiteForCoverings ∧
    (Scheme.ProEt.topology X).Subcanonical ∧
    IsGrothendieckTopos.{u + 1} (Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) ∧
    Nonempty (setPullback f ⊣ lowerStar (Type (u + 1)) f) ∧
    PreservesFiniteLimits (setPullback f) ∧
    PreservesColimits (setPullback f) ∧
    (Nonempty (upperStar AddCommGrpCat.{u + 1} f ⋙
        sheafCompose (Scheme.ProEt.topology X) (forget AddCommGrpCat.{u + 1}) ≅
      sheafCompose (Scheme.ProEt.topology Y) (forget AddCommGrpCat.{u + 1}) ⋙
        setPullback f) ∧
      PreservesFiniteLimits (upperStar AddCommGrpCat.{u + 1} f) ∧
      PreservesFiniteColimits (upperStar AddCommGrpCat.{u + 1} f)) ∧
    ∀ F : Sheaf (Scheme.ProEt.topology Z) (Type (u + 1)),
      (setPullbackAdjunction (f ≫ g)).unit.app F ≫
          (lowerStar (Type (u + 1)) (f ≫ g)).map ((setPullbackComp f g).hom.app F) =
        ((setPullbackAdjunction g).comp (setPullbackAdjunction f)).unit.app F ≫
          (lowerStarComp (Type (u + 1)) f g).hom.app
            ((setPullback g ⋙ setPullback f).obj F) := by
  have hsite := Scheme.proetale_site_properties X
  have hinv := toposFunctorialityInverseImage f g
  rcases hsite with ⟨hcover, hsub, _hsmall, htopos⟩
  rcases hinv with ⟨_hbase, hadj, hcolim, hlim, habelian, hcomp⟩
  exact ⟨hcover, hsub, htopos, hadj, hlim, hcolim, habelian, hcomp⟩

end AlgebraicGeometry.ProEtale
