/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationCounit.DiagonalCounitComparisonData
public import WeilConjectures.AlgebraicGeometry.Section.SectionExceptionalFibreCoherence
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.ComparisonPullbackDerivedCoherence
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs

/-! # Restriction coherence for the fixed site comparison

Source: diagonal-dualizing proof Steps 1--2; orientation-charts proof Step 3.
(blueprint: lem-pur-comparison-pullback-restriction-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] Etale.upperStar Etale.lowerStar
  Etale.rightDerivedUpperShriek Etale.rightDerivedUpperShriekAdjunction
  Functor.mapDerivedCategory Functor.rightDerivedFunctor conjugateIsoEquiv

private theorem comparison_comp_named (P : PurityFiniteSetting.{u})
    {T S R : Scheme.{u}} (a : T ⟶ S) (b : S ⟶ R) (z : T ⟶ R) (hz : z = a ≫ b)
    (M : Etale.DerivedCategoryModule P.Coefficient R) :
    (Dnc.pullComparison P z M).hom ≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.map
        ((Etale.leftDerivedUpperStarComp
          (ModuleCat.{u + 1} P.Coefficient) a b z hz).hom.app M) =
    (ProEtale.leftDerivedUpperStarCongr
        (ModuleCat.{u + 1} P.Coefficient) hz).hom.app
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) R).mapDerivedCategory.obj M) ≫
      (ProEtale.leftDerivedUpperStarComp
        (ModuleCat.{u + 1} P.Coefficient) a b).hom.app
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) R).mapDerivedCategory.obj M) ≫
      (OrientationRefinement.pull P a).map (Dnc.pullComparison P b M).hom ≫
      (Dnc.pullComparison P a
        ((Etale.ordinaryFinitePullback P.Coefficient b).obj M)).hom := by
  subst z
  simpa only [ProEtale.leftDerivedUpperStarCongr_rfl, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp, OrientationRefinement.pull,
    Etale.ordinaryFinitePullback] using Dnc.pullComparison_comp P a b M

/-- The fixed site comparison commutes with restriction along an arbitrary open square.
Proof: use composition compatibility for the two factorizations of the common composite.
Cancel the pullback compositor, then cancel its image under the site comparison.
Expanding the specified restriction isomorphism gives the remaining compositor equality.
There is no Cartesian or nonempty hypothesis: this is pseudofunctor composition coherence.
Source: diagonal-dualizing proof Steps 1--2; orientation-charts proof Step 3.
(blueprint: lem-pur-comparison-pullback-restriction-coherence).
-/
theorem diagonalEtaleComparison_restriction (P : PurityFiniteSetting.{u})
    {U X : Scheme.{u}} (j : U ⟶ X) (W : X.Opens) (O : U.Opens)
    (k : O.toScheme ⟶ W.toScheme) (hk : k ≫ W.ι = O.ι ≫ j)
    (M : Etale.DerivedCategoryModule P.Coefficient X) :
    (OrientationRefinement.pull P k).map (Dnc.pullComparison P W.ι M).hom ≫
      (Dnc.pullComparison P k
        ((Etale.ordinaryFinitePullback P.Coefficient W.ι).obj M)).hom ≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) O.toScheme).mapDerivedCategory.map
        (Etale.sectionCoherencePullbackIso P.Coefficient k W.ι O.ι j hk M).hom =
    ((OrientationCounit.restrictionAlong P j W O k hk).app M).hom ≫
      (Dnc.pullComparison P O.ι
        ((Etale.ordinaryFinitePullback P.Coefficient j).obj M)).hom := by
  have ha := comparison_comp_named P k W.ι (k ≫ W.ι) rfl M
  simp only [ProEtale.leftDerivedUpperStarCongr_rfl, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp] at ha
  have hb := comparison_comp_named P O.ι j (k ≫ W.ι) hk M
  apply (cancel_epi ((ProEtale.leftDerivedUpperStarComp
    (ModuleCat.{u + 1} P.Coefficient) k W.ι).hom.app
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.obj M))).mp
  rw [← reassoc_of% ha]
  simp only [Etale.sectionCoherencePullbackIso, Iso.trans_hom,
    Iso.symm_hom, Iso.app_hom, Functor.map_comp]
  have hc := ((ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) O.toScheme).mapDerivedCategory.mapIso
      ((Etale.leftDerivedUpperStarComp
        (ModuleCat.{u + 1} P.Coefficient) k W.ι).app M)).hom_inv_id
  simp only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv] at hc
  rw [reassoc_of% hc, hb]
  unfold OrientationCounit.restrictionAlong OrientationCounit.comparisonPull
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  rfl

end WeilConjectures.PurityFiniteSetting
