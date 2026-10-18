/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q153
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import Sheaf.AlgebraicGeometry.ProEtaleOpenUnitEvaluation
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Unit normalization of the open etale/pro-etale comparison

Source: Stacks Project, Tag 09AF, `lemma-jshriek-comparison`, common-right-adjoint proof
(blueprint: lem-sf-open-comparison-unit-normalization).

## Main definitions

- `openComparisonRestrictionIso`: the canonical inverse-image comparison in restriction form.
- `openComparisonHomEquiv`: the displayed composite of four natural Hom bijections.

## Main statements

- `openComparison_unit_normalization`: the Hom formula and the open-unit equation.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The canonical pullback comparison, expressed using localization restriction on both
sites. The first factor converts etale restriction to inverse image; the middle factor
is the recorded canonical comparison, and the last converts pro-etale inverse image to
restriction. No independent comparison is chosen.
Source: Stacks Project, Tags 099R and 09AF
(blueprint: lem-sf-open-comparison-unit-normalization). -/
noncomputable def openComparisonRestrictionIso (A : Type (u + 1)) [CommRing A]
    [Finite A] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j ⋙
        comparisonUpperStar (ModuleCat.{u + 1} A) U ≅
      comparisonUpperStar (ModuleCat.{u + 1} A) X ⋙
        openImmersionRestriction (ModuleCat.{u + 1} A) j :=
  Functor.isoWhiskerRight
      (Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).symm _ ≪≫
    supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) j ≪≫
      Functor.isoWhiskerLeft _
        (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j)

/-- The displayed Hom chain of Tag 09AF: the comparison adjunction, the etale open
adjunction, postcomposition with the sectionwise identity `r R_X ≅ R_U s`, and the
inverses of the comparison and pro-etale open adjunctions. Every factor is a natural
bijection, so their composite is natural in the two sheaves.
Source: Stacks Project, Tag 09AF
(blueprint: lem-sf-open-comparison-unit-normalization). -/
noncomputable def openComparisonHomEquiv (A : Type (u + 1)) [CommRing A]
    [Finite A] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).obj
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj F) ⟶ M) ≃
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) U).obj F) ⟶ M) :=
  (((comparisonAdjunction (ModuleCat.{u + 1} A) X).homEquiv _ _).trans
    ((Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).homEquiv _ _)).trans
      (((comparisonLowerStarOpenImmersionRestrictionIso (ModuleCat.{u + 1} A) j).app M
        ).homToEquiv.trans
        (((comparisonAdjunction (ModuleCat.{u + 1} A) U).homEquiv _ _).symm.trans
          ((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).homEquiv _ _).symm))

/-- The natural Hom chain sends `h` to `c_F⁻¹ ≫ h`, and the specified comparison `c`
intertwines the two open units via the canonical restriction comparison `a`.
Source: Stacks Project, Tag 09AF, common-right-adjoint proof
(blueprint: lem-sf-open-comparison-unit-normalization).

Proof plan:
1. Etale restriction and pro-etale localization identify `r R_X` and `R_U s` on each
   object and arrow, including scalar actions (lem-weil-pbc-etale-inverse-image-restriction,
   lem-weil-proetale-weakly-etale-localization,
   def-weil-pbc-site-comparison-morphism).
2. Compose the comparison and open adjunctions. Their conjugate of this sectionwise
   identity is the specified `c` (lem-weil-pbc-extension-by-zero-adjunction,
   lem-weil-extension-by-zero-adjunction, def-weil-pbc-composite-adjunction,
   lem-weil-pbc-conjugate-iso-unit-equation,
   lem-cbc-proetale-extension-zero-comparison).
3. The Hom chain sends `c` to the identity. Naturality in its target then sends an
   arbitrary `h` to `c_F⁻¹ ≫ h`.
4. The direct-image square is the identity on sections over the same fibre product.
   The actual pro-etale inverse image is identified with restriction by the canonical
   localization isomorphism; its unit restricts along the projection
   (def-weil-pbc-direct-image, def-weil-proetale-inverse-image,
   def-weil-pbc-inverse-image, lem-pur-proetale-open-unit-evaluation).
5. Conjugate that square to obtain the specified pullback comparison `a`. The composite
   unit formula, its conjugation equation and the restriction triangle identity give
   `R_U(a_G) u_U = theta r(u_X)` (lem-weil-pbc-comparison-pullback).
6. Expand the four Hom bijections on `h`, then use this equality and naturality of the
   comparison unit: its open transpose is `C_U(eta^e_F) ≫ a_(eF) ≫ s(h)`.
7. Set `h = c_F`. Its Hom image is the identity, whose open transpose is `eta^d`.
   This proves the unit equation, naturally in `F`, also for the identity immersion,
   empty open subscheme, zero sheaf and zero ring. -/
theorem openComparison_unit_normalization (A : Type (u + 1)) [CommRing A]
    [Finite A] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (∀ (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
      (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
      (h : (comparisonUpperStar (ModuleCat.{u + 1} A) X).obj
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj F) ⟶ M),
      openComparisonHomEquiv A j F M h =
        (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) j).inv.app F ≫
          h) ∧
    (∀ (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)),
      (comparisonUpperStar (ModuleCat.{u + 1} A) U).map
          ((Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).unit.app F) ≫
        (openComparisonRestrictionIso A j).hom.app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj F) ≫
        (openImmersionRestriction (ModuleCat.{u + 1} A) j).map
          ((openImmersionLowerShriekComparisonUpperStarIso
            (ModuleCat.{u + 1} A) j).hom.app F) =
      (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).unit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) U).obj F)) := by
  sorry

end AlgebraicGeometry.ProEtale
