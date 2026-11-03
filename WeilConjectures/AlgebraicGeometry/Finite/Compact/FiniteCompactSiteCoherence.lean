/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportSiteCoherence
import all WeilConjectures.AlgebraicGeometry.Compact.CompactSupportSiteCoherence
import all WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Finite.FiniteSiteWordRefinement
import all WeilConjectures.AlgebraicGeometry.FiniteSiteTower.FiniteSiteTowerPaste
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientMate
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperOpenComparison
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableCompatibleTower
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportComparisons
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenComparison
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.Adjunction.SixFunctors.CompositionAdjunctionNormalization
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.Compactification.CategoryBaseChange

/-! # Finite-ring compact-support site coherence

Source: Stacks Project, more-etale.tex, Tags 0F7I, 0F7J and 0F7K;
canonical site-square deduction in the DAG
(blueprint: lem-sp-finite-compact-site-coherence).

The tower arrow below uses the specified open adjunct Gamma, not conjugation of
an etale composition arrow. All inputs retain their bounded-below etale witness.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local implicit_reducible] AlgebraicGeometry.Etale.derivedPlusFormalism

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

attribute [local implicit_reducible] Compactification.copy
attribute [local implicit_reducible] coherenceEtaleFunctor
variable (R : Type (u + 1)) [CommRing R] [Finite R]

/-- Change of compactification through the canonical common proper refinement,
in bounded-below pro-etale modules. Each leg uses the proper/open refinement map.
Source: Stacks Tag 0F7I (blueprint: lem-sp-finite-compact-site-coherence). -/
def finiteCompactSiteChangePlus {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :=
  (properTransportRefinementPlus R (Compactification.infFst c d) E).symm ≪≫
    properTransportRefinementPlus R (Compactification.infSnd c d) E

/-- Change on an explicitly witnessed etale-origin object. The witness is retained
and the underlying change is the computed common-refinement map.
Source: Stacks Tag 0F7I (blueprint: lem-sp-finite-compact-site-coherence). -/
def finiteCompactSiteChangeAtWitness {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)))
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R)))
    (w : (comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.obj E ≅ K) :=
  (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) c).mapIso w.symm ≪≫
    finiteCompactSiteChangePlus R c d E ≪≫
    (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) d).mapIso w

/-- Equality transport of derived open extension, including the open-immersion instance.
Source: Stacks Tag 0F7J (blueprint: lem-sp-finite-compact-site-coherence). -/
def finiteCompactSiteOpenCongr {X Y : Scheme.{u}} {j k : X ⟶ Y}
    [IsOpenImmersion j] [IsOpenImmersion k] (w : j = k) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategoryPlus ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} R) k).mapDerivedCategoryPlus := by
  subst k
  exact Iso.refl _

/-- Canonical open-extension composition on a compatible tower, including its
factorization equality. Source: Stacks Tag 0F7J
(blueprint: lem-sp-finite-compact-site-coherence). -/
def finiteCompactSiteTowerOpen {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} R) T.cf.i).mapDerivedCategoryPlus ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} R) T.q).mapDerivedCategoryPlus ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} R) T.cfg.i).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (proEtaleOpenExtensionComp R T.cf.i T.q).symm ≪≫
    finiteCompactSiteOpenCongr R T.i_q

/-- The computed tower arrow: apply P_q to the open adjunct Gamma, then the proper
and open compositors. The first and last open comparisons insert the etale witness
of J_a N E. Source: Stacks Tag 0F7J, the four displayed functors in its proof
(blueprint: lem-sp-finite-compact-site-coherence). -/
def finiteCompactSiteTowerPlus {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g)
    [IsNoetherian Y] [IsNoetherian Z]
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) T.cg).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) T.cf).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.obj E)) ⟶
      (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) T.cfg).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.obj E) :=
  letI := isNoetherian_of_locallyOfFiniteType T.cf.g
  letI := isNoetherian_of_locallyOfFiniteType T.cfg.g
  letI := isNoetherian_of_locallyOfFiniteType T.cg.g
  (lowerStar (ModuleCat.{u + 1} R) T.cg.g).rightDerivedFunctorPlus.map
    ((openImmersionLowerShriek (ModuleCat.{u + 1} R) T.cg.i).mapDerivedCategoryPlus.map
        ((lowerStar (ModuleCat.{u + 1} R) T.cf.g).rightDerivedFunctorPlus.map
          ((properOpenSiteExtensionIso R T.cf.i).inv.app E)) ≫
      properOpenSiteInterchange R T.isPullback.flip
        ((Etale.openImmersionLowerShriek
          (ModuleCat.{u + 1} R) T.cf.i).mapDerivedCategoryPlus.obj E) ≫
      (lowerStar (ModuleCat.{u + 1} R) T.p).rightDerivedFunctorPlus.map
        ((openImmersionLowerShriek (ModuleCat.{u + 1} R) T.q).mapDerivedCategoryPlus.map
          ((properOpenSiteExtensionIso R T.cf.i).hom.app E))) ≫
    (proEtaleComparisonDirectImageCompIso R T.p T.cg.g).hom.app _ ≫
    (properTransportDirectImageCongr R T.p_g).hom.app _ ≫
    (lowerStar (ModuleCat.{u + 1} R) T.cfg.g).rightDerivedFunctorPlus.map
      ((finiteCompactSiteTowerOpen R T).hom.app _)

/-- Composition on arbitrary supplied compactifications, computed through the supplied
tower and proper/open common-refinement changes. The middle witness is exactly C_f.
Source: Stacks Tags 0F7I and 0F7J
(blueprint: lem-sp-finite-compact-site-coherence). -/
def finiteCompactSiteCompositionPlus {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (T : Compactification.Triangle f g)
    [IsNoetherian Y] [IsNoetherian Z]
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) d).obj
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) c).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.obj E)) ⟶
      (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) e).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategoryPlus.obj E) :=
  (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) d).map
      ((finiteCompactSiteChangePlus R c T.cf E).hom) ≫
    (finiteCompactSiteChangeAtWitness R d T.cg
      ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) T.cf).obj E)
      _ ((compactSupportSiteComparisonPlus R T.cf).app E)).hom ≫
    finiteCompactSiteTowerPlus R T E ≫
    (finiteCompactSiteChangePlus R T.cfg e E).hom

/-- The site square for the actual proper/open refinement arrow. Here c is the fine
compactification and d the coarse one, so rho is the inverse of properTransportRefinementPlus.
Source: Stacks Tag 0F7I (blueprint: lem-sp-finite-compact-site-coherence).
Proof: expand rho as P(alpha) followed by the proper compositor, using
lem-amb-etale-compact-comparisons. Normalize direct-image composition with
lem-sfb-derived-composition-adjunction-normalization and lem-weil-pbc-mate-pasting.
The counit mates d then compose. Naturality moves N(alpha) next to d_u; the site
clause of lem-sp-refinement-coefficient-mate replaces the three inner factors by
alpha_pro followed by the open comparison. Naturality of the proper compositor
moves that open comparison to its final position, giving precisely the two paths.
No Cartesian hypothesis is placed on the original refinement square.
-/
theorem finiteCompactSite_refinement
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (comparisonUpperStar (ModuleCat.{u + 1} R) Y).mapDerivedCategoryPlus.map
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso R r).hom.app E) ≫
      (compactSupportSiteComparisonPlus R c).hom.app E =
    (compactSupportSiteComparisonPlus R d).hom.app E ≫
      (properTransportRefinementPlus R r E).inv := by
  exact refinement_plus_inverse R r E

private theorem common_refinement_square
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d b : Compactification f) (r : b.Refinement c) (s : b.Refinement d)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (comparisonUpperStar (ModuleCat.{u + 1} R) Y).mapDerivedCategoryPlus.map
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusIso R c d).hom.app E) ≫
      (compactSupportSiteComparisonPlus R d).hom.app E =
    (compactSupportSiteComparisonPlus R c).hom.app E ≫
      ((properTransportRefinementPlus R r E).inv ≫
        (properTransportRefinementPlus R s E).hom) := by
  have hs := inverse_square
    (comparisonUpperStar (ModuleCat.{u + 1} R) Y).mapDerivedCategoryPlus
    ((Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso R s).app E)
    ((compactSupportSiteComparisonPlus R b).app E)
    ((compactSupportSiteComparisonPlus R d).app E)
    (properTransportRefinementPlus R s E) (finiteCompactSite_refinement R f s E)
  rw [Etale.rightDerivedLowerShriekOfCompactificationPlusIso_eq_refinementIso R r s]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    Category.assoc]
  simp only [Iso.app_inv, Iso.app_hom] at hs
  rw [hs, ← Category.assoc, finiteCompactSite_refinement R f r E, Category.assoc]

private theorem change_square_plus
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (comparisonUpperStar (ModuleCat.{u + 1} R) Y).mapDerivedCategoryPlus.map
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusIso R c d).hom.app E) ≫
      (compactSupportSiteComparisonPlus R d).hom.app E =
    (compactSupportSiteComparisonPlus R c).hom.app E ≫
      (finiteCompactSiteChangePlus R c d E).hom := by
  exact common_refinement_square R f c d _
    (Compactification.infFst c d) (Compactification.infSnd c d) E

private def towerEtaleIso
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) :
    coherenceEtaleFunctor R T.cf ⋙ coherenceEtaleFunctor R T.cg ≅
      coherenceEtaleFunctor R T.cfg :=
  Etale.native_bounded_triangle_iso (ModuleCat.{u + 1} R) T

private theorem etale_change_trans
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d e : Compactification f) :
    coherenceEtaleChangeIso R c d ≪≫ coherenceEtaleChangeIso R d e =
      coherenceEtaleChangeIso R c e :=
  Etale.rightDerivedLowerShriekOfCompactificationPlusIso_trans R c d e

private theorem compositor_paste
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F F₀ F₁ : A ⥤ B} {G G₀ G₁ : B ⥤ C} {H H₀ H₁ : A ⥤ C}
    (a₀ : F ⟶ F₀) (a₁ : F₀ ⟶ F₁) (b₀ : G ⟶ G₀) (b₁ : G₀ ⟶ G₁)
    (c : F₁ ⋙ G₁ ⟶ H₁) (d₁ : H₁ ⟶ H₀) (d₀ : H₀ ⟶ H)
    (μ : F₀ ⋙ G₀ ⟶ H₀)
    (hm : μ = NatTrans.hcomp a₁ b₁ ≫ c ≫ d₁) (E : A) :
    G.map (a₀.app E) ≫ b₀.app (F₀.obj E) ≫ μ.app E ≫ d₀.app E =
      G.map ((a₀ ≫ a₁).app E) ≫ (b₀ ≫ b₁).app (F₁.obj E) ≫
        c.app E ≫ (d₁ ≫ d₀).app E := by
  rw [hm]
  simp only [NatTrans.comp_app, NatTrans.hcomp_app, Functor.map_comp, Category.assoc]
  rw [← b₁.naturality_assoc, ← b₀.naturality_assoc]

private theorem compositor_component
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F F' : A ⥤ B) (G G' : B ⥤ C) (H H' : A ⥤ C)
    (a : F ≅ F') (b : G ≅ G') (c : F' ⋙ G' ≅ H) (d : H ≅ H') (E : A) :
    (coherenceCompositorOfChanges F F' G G' H H' a b c d).hom.app E =
      G.map (a.hom.app E) ≫ b.hom.app (F'.obj E) ≫ c.hom.app E ≫ d.hom.app E := by
  rfl

private theorem compositor_iso_paste
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F F₀ F₁ : A ⥤ B} {G G₀ G₁ : B ⥤ C} {H H₀ H₁ : A ⥤ C}
    (a₀ : F ≅ F₀) (a₁ : F₀ ≅ F₁) (b₀ : G ≅ G₀) (b₁ : G₀ ≅ G₁)
    (c : F₁ ⋙ G₁ ≅ H₁) (d₁ : H₁ ≅ H₀) (d₀ : H₀ ≅ H)
    (μ : F₀ ⋙ G₀ ≅ H₀)
    (hm : μ.hom = NatTrans.hcomp a₁.hom b₁.hom ≫ c.hom ≫ d₁.hom) :
    coherenceCompositorOfChanges F F₀ G G₀ H₀ H a₀ b₀ μ d₀ =
      coherenceCompositorOfChanges F F₁ G G₁ H₁ H
        (a₀ ≪≫ a₁) (b₀ ≪≫ b₁) c (d₁ ≪≫ d₀) := by
  apply Iso.ext
  ext E
  simp only [compositor_component, Iso.trans_hom]
  exact compositor_paste a₀.hom a₁.hom b₀.hom b₁.hom c.hom d₁.hom d₀.hom μ.hom hm E

-- Avoid unfolding whole derived functors when normalizing the compositor.
set_option backward.isDefEq.respectTransparency false in
private theorem etale_compositor_tower
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (T : Compactification.Triangle f g)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (coherenceEtaleCompositor R c d e).hom.app E =
      (coherenceEtaleFunctor R d).map
        ((coherenceEtaleChangeIso R c T.cf).hom.app E) ≫
      (coherenceEtaleChangeIso R d T.cg).hom.app ((coherenceEtaleFunctor R T.cf).obj E) ≫
      (towerEtaleIso R T).hom.app E ≫
      (coherenceEtaleChangeIso R T.cfg e).hom.app E := by
  let := c.hasCompactification
  let := d.hasCompactification
  let := e.hasCompactification
  have h : (coherenceChosenEtaleCompositorIso R f g).hom =
      NatTrans.hcomp
        (coherenceEtaleChangeIso R (HasCompactification.compactification f) T.cf).hom
        (coherenceEtaleChangeIso R (HasCompactification.compactification g) T.cg).hom ≫
      (towerEtaleIso R T).hom ≫
      (coherenceEtaleChangeIso R T.cfg
        (HasCompactification.compactification (f ≫ g))).hom := by
    exact Etale.compositor_middle_transport _ _ _ _
      (congrArg Iso.hom
        (Etale.native_bounded_triangle_iso_eq (ModuleCat.{u + 1} R) T).symm)
      (Etale.rightDerivedLowerShriekPlusCompIso_hom_eq R T)
  have hp := compositor_iso_paste
    (F := coherenceEtaleFunctor R c)
    (F₀ := coherenceEtaleFunctor R (HasCompactification.compactification f))
    (F₁ := coherenceEtaleFunctor R T.cf)
    (G := coherenceEtaleFunctor R d)
    (G₀ := coherenceEtaleFunctor R (HasCompactification.compactification g))
    (G₁ := coherenceEtaleFunctor R T.cg)
    (H := coherenceEtaleFunctor R e)
    (H₀ := coherenceEtaleFunctor R (HasCompactification.compactification (f ≫ g)))
    (H₁ := coherenceEtaleFunctor R T.cfg)
    (coherenceEtaleChangeIso R c (HasCompactification.compactification f))
    (coherenceEtaleChangeIso R (HasCompactification.compactification f) T.cf)
    (coherenceEtaleChangeIso R d (HasCompactification.compactification g))
    (coherenceEtaleChangeIso R (HasCompactification.compactification g) T.cg)
    (towerEtaleIso R T)
    (coherenceEtaleChangeIso R T.cfg (HasCompactification.compactification (f ≫ g)))
    (coherenceEtaleChangeIso R (HasCompactification.compactification (f ≫ g)) e)
    (coherenceChosenEtaleCompositorIso R f g) h
  rw [etale_change_trans, etale_change_trans, etale_change_trans] at hp
  exact (congrArg (fun t ↦ t.hom.app E) hp).trans
    (compositor_component _ _ _ _ _ _ _ _ _ _ E)

section TowerCalculation
attribute [local implicit_reducible] ExchangeFormalism.shriek
attribute [local irreducible] Functor.rightDerivedFunctorPlus Functor.rightDerivedFunctor
  Functor.mapDerivedCategoryPlus Functor.mapDerivedCategory
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option maxRecDepth 2048 in
private theorem tower_etale_normalization
    {X U XB Y YB Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian U] [IsNoetherian XB]
    [IsNoetherian Y] [IsNoetherian YB] [IsNoetherian Z]
    (a : X ⟶ U) (b : U ⟶ XB) (p : XB ⟶ YB) (q : YB ⟶ Z)
    (i : Y ⟶ YB) (s : U ⟶ Y)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion i]
    [QuasiCompact a] [QuasiCompact b] [QuasiCompact i]
    [IsProper p] [IsProper q] [IsProper s]
    (sq : IsPullback b s p i) (E : FiniteSiteTower.DE R X) :
    FiniteSiteTower.AE R a b p q i s sq E =
      (Etale.native_bounded_triangle_iso (ModuleCat.{u + 1} R)
        (FiniteSiteTower.towerTriangle a b p q i s sq)).hom.app E := by
  apply DerivedCategory.Plus.ι.map_injective
  apply (cancel_mono (FiniteSiteTower.targetCompatibility R a b p q E).hom).1
  rw [FiniteSiteTower.etale_normalization, FiniteSiteTower.AEUnbounded_eq_triangle]
  have h := Etale.triangle_comp_plus R (FiniteSiteTower.towerTriangle a b p q i s sq) E
  simp only [FiniteSiteTower.sourceCompatibility, FiniteSiteTower.targetCompatibility,
    Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility,
    Etale.native_unbounded_triangle_iso, FiniteSiteTower.towerTriangle,
    FiniteSiteTower.compactificationF, FiniteSiteTower.compactificationG,
    FiniteSiteTower.compactificationGF, Iso.symm_hom, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id,
    Etale.rightDerivedLowerShriekOfCompactification, Functor.comp_map,
    Functor.map_comp, Category.assoc, FiniteSiteTower.JE, FiniteSiteTower.PE,
    Etale.rightDerivedLowerShriekOfCompactificationPlus, Functor.comp_obj,
    ObjectProperty.ι_obj] at h ⊢
  convert! h.symm using 1

private def TowerSiteSquare
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    {f : X ⟶ Y} {g : Y ⟶ Z} (T : Compactification.Triangle f g)
    (E : FiniteSiteTower.DE R X) : Prop :=
    (FiniteSiteTower.N R Z).map
        ((Etale.native_bounded_triangle_iso (ModuleCat.{u + 1} R) T).hom.app E) ≫
      (compactSupportSiteComparisonPlus R T.cfg).hom.app E =
    (compactSupportSiteComparisonPlus R T.cg).hom.app
        ((coherenceEtaleFunctor R T.cf).obj E) ≫
      (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) T.cg).map
        ((compactSupportSiteComparisonPlus R T.cf).hom.app E) ≫
      finiteCompactSiteTowerPlus R T E

private theorem tower_site_square
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    {f : X ⟶ Y} {g : Y ⟶ Z} (T : Compactification.Triangle f g)
    (E : FiniteSiteTower.DE R X) : TowerSiteSquare R T E := by
  rcases T with ⟨cf, cg, cfg, b, p, hi, hp, sq⟩
  rcases cf with ⟨U, s, a, hf, hs, ha⟩
  rcases cg with ⟨YB, q, i, hg, hq, hι⟩
  rcases cfg with ⟨XB, r, j, hfg, hr, hj⟩
  change U ⟶ XB at b
  change XB ⟶ YB at p
  change a ≫ b = j at hi
  change p ≫ q = r at hp
  change IsPullback s b i p at sq
  subst f g j r
  let := hs
  let := hq
  let := hr
  let := ha
  let := hι
  let := hj
  let := isNoetherian_of_locallyOfFiniteType s
  let := isNoetherian_of_locallyOfFiniteType q
  let := isNoetherian_of_locallyOfFiniteType (p ≫ q)
  have : IsProper p := IsProper.of_comp p q
  dsimp only [TowerSiteSquare]
  have h := (FiniteSiteTower.paste R a b p q i s sq.flip E).2.1
  rw [tower_etale_normalization] at h
  have hk : proEtaleComparisonDirectImageCompIso R p q = FiniteSiteTower.kP R p q := by
    unfold FiniteSiteTower.kP
    rw [FiniteSiteTower.conjugate_iso_reverse]
    exact (finiteSiteWordRefinement R).2.2.2.2.1 p q |>.2
  simp only [FiniteSiteTower.B, FiniteSiteTower.D, FiniteSiteTower.AP,
    FiniteSiteTower.GP, FiniteSiteTower.mP, FiniteSiteTower.towerTriangle,
    FiniteSiteTower.compactificationF, FiniteSiteTower.compactificationG,
    FiniteSiteTower.compactificationGF, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Category.assoc, Functor.map_comp, FiniteSiteTower.N,
    FiniteSiteTower.PE, FiniteSiteTower.PP, FiniteSiteTower.JE, FiniteSiteTower.JP,
    Etale.rightDerivedLowerShriekOfCompactificationPlus, Functor.comp_obj] at h
  simp only [site_plus_hom, finiteCompactSiteTowerPlus, finiteCompactSiteTowerOpen,
    finiteCompactSiteOpenCongr, hk, properTransportDirectImageCongr_rfl, Iso.trans_hom,
    NatTrans.comp_app, Iso.symm_hom, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id, Category.id_comp, Category.assoc, Functor.map_comp,
    rightDerivedLowerShriekOfCompactificationPlus, coherenceEtaleFunctor,
    Etale.rightDerivedLowerShriekOfCompactificationPlus, Functor.comp_obj, Functor.comp_map]
  convert! h using 1

/-- The computed tower composition satisfies the site-comparison equation, for
arbitrary finite commutative coefficients and every supplied compactification tower.
Source: Stacks Tags 0F7I, 0F7J and 0F7K
(blueprint: lem-sp-finite-compact-site-coherence).

Proof (the eight steps of the node):
1. Exact open extensions and N preserve lower bounds. Each proper map between the
Noetherian schemes is qcqs. Thus the specified proper counit mate and the open
comparison are invertible, and F_pro N E has witness F_et E via C(E).
2. Derive the ordinary direct-image compositors with their adjunction normalization,
using lem-sfb-derived-composition-adjunction-normalization. The module sheaf categories
are Grothendieck by lem-cbc-sieve-module-sheaves-grothendieck and the constant-ring
module realization. Exact inverse images and their adjunctions give the Grothendieck
hypotheses. The inverse-image comparisons compose. Parts (2), (3), (4) of
lem-weil-pbc-mate-pasting therefore give composition and identity for the specified d.
The exact open comparison composition equation descends termwise as well.
3. The refinement square follows by expanding P(alpha), applying the site clause of
lem-sp-refinement-coefficient-mate, and using naturality and step 2.
4. On T, lem-amb-unbounded-compact-support-comparisons normalizes etale composition
to P_q(Gamma_et J_a), followed by the proper and open compositors. It restricts on
D+ to lem-amb-etale-compact-comparisons. The pro-etale arrow in this module uses
properOpenSiteInterchange, the specified open adjunct of inverse transported restriction.
5. Evaluate lem-sp-proper-open-coefficient-mate on J_a E. Whisker its site square by
P_q and J_a; attach d_q on the source and P_q P_p J_b(e_a) on the target.
Naturality of d_q and Gamma_pro gives the two comparison paths for the tower word.
6. Postcompose with the proper and open compositors. Step 2 replaces comparison for
the word P_q P_p J_b J_a by C_gf. The result is exactly the equation below.
7. Use lem-cbc-compactifiable-compatible-tower and lem-cbc-compactifiable-cofiltered
to compare arbitrary candidates with the tower. The refinement squares of step 3
move C through each change. Naturality moves C_g through the change of F_f E;
etale tower independence cancels the remaining comparisons. Every tower yields the
same computed pro-etale arrow, equal to transport through C as a conclusion.
8. Identity d is normalized, and identity e is an invertible idempotent by its
composition law. For three maps substitute this equation twice and use naturality:
both paths are C_hgf N(alpha_et_triple) followed by the inverse of
F_h F_g(C_f), F_h(C_g F_f), C_h(F_g F_f). Etale associativity and units give
pro-etale associativity and units. Naturality follows from that of all constituents.
No coefficient presentation or base field is used.
-/
theorem finiteCompactSiteCoherence
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (T : Compactification.Triangle f g)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (comparisonUpperStar (ModuleCat.{u + 1} R) Z).mapDerivedCategoryPlus.map
        ((coherenceEtaleCompositor R c d e).hom.app E) ≫
      (compactSupportSiteComparisonPlus R e).hom.app E =
    (compactSupportSiteComparisonPlus R d).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) c).obj E) ≫
      (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) d).map
        ((compactSupportSiteComparisonPlus R c).hom.app E) ≫
      finiteCompactSiteCompositionPlus R c d e T E := by
  let N := (comparisonUpperStar (ModuleCat.{u + 1} R) Z).mapDerivedCategoryPlus
  let P := rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} R) d
  let α := (coherenceEtaleChangeIso R c T.cf).hom.app E
  have hf := map_cancel_boundary P ((compactSupportSiteComparisonPlus R T.cf).app E)
    ((compactSupportSiteComparisonPlus R c).hom.app E)
    ((finiteCompactSiteChangePlus R c T.cf E).hom)
    ((comparisonUpperStar (ModuleCat.{u + 1} R) Y).mapDerivedCategoryPlus.map α)
    (change_square_plus R f c T.cf E)
  have hn := (compactSupportSiteComparisonPlus R d).hom.naturality α
  have hp := mapped_paste_composition N
    (change_square_plus R (f ≫ g) T.cfg e E)
    (tower_site_square R T E)
    (change_square_plus R g d T.cg ((coherenceEtaleFunctor R T.cf).obj E)) hn hf
  rw [etale_compositor_tower R c d e T E]
  simpa only [N, P, α, towerEtaleIso, coherenceEtaleFunctor, coherenceEtaleChangeIso,
    coherenceFourMap, coherenceSixMap, finiteCompactSiteCompositionPlus,
    finiteCompactSiteChangeAtWitness, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Category.assoc] using hp

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
end TowerCalculation

omit [Finite R] in
private theorem etale_proper_id_eq (X : Scheme.{u}) :
    (Etale.derivedPlusFormalism (ModuleCat.{u + 1} R)).pfId X =
      Etale.lowerStarIdDerivedPlus (ModuleCat.{u + 1} R) X := by
  let a := (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) (𝟙 X)).derivedPlus
  let e := Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} R) X
  let r := Etale.lowerStarIdDerivedPlus (ModuleCat.{u + 1} R) X
  change conjugateIsoEquiv a Adjunction.id e.symm = r
  apply Iso.ext
  apply conjugateEquiv_eq_of_unit
  intro K
  have h := NatTrans.congr_app
    (Etale.derivedPlus_unit_comp_upperStarIdDerivedPlus (ModuleCat.{u + 1} R) X) K
  change a.unit.app K ≫
    (Etale.lowerStar (ModuleCat.{u + 1} R) (𝟙 X)).rightDerivedFunctorPlus.map
      (e.hom.app K) = r.inv.app K at h
  have ht := congrArg (fun t ↦ t ≫
    (Etale.lowerStar (ModuleCat.{u + 1} R) (𝟙 X)).rightDerivedFunctorPlus.map
      (e.inv.app K) ≫ r.hom.app _) h
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp] at ht
  rw [r.hom.naturality (e.inv.app K)] at ht
  simpa only [Iso.symm_hom, Adjunction.id_unit, NatTrans.id_app, Functor.id_map,
    Functor.id_obj, Category.id_comp, Iso.inv_hom_id_app_assoc] using ht

omit [Finite R] in
private theorem etale_open_id_eq (X : Scheme.{u}) :
    (Etale.derivedPlusFormalism (ModuleCat.{u + 1} R)).shId X =
      finiteSiteEtaleOpenId R X := by
  apply Etale.conjugate_iso_symm_eq
  apply conjugateEquiv_eq_of_unit
  intro K
  apply DerivedCategory.Plus.ι.map_injective
  have hp : DerivedCategory.Plus.ι.mapIso
      ((Etale.upperStarIdDerivedPlus (ModuleCat.{u + 1} R) X).app K) =
      (Functor.mapDerivedCategoryNatIso
        (Etale.upperStarId (ModuleCat.{u + 1} R) X) ≪≫
          Functor.mapDerivedCategoryIdIso _).app K.obj := by
    apply Iso.ext
    simp only [Functor.mapIso_hom, Iso.app_hom, Etale.upperStarIdDerivedPlus,
      Iso.trans_hom, NatTrans.comp_app, Functor.map_comp,
      Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
      Functor.ι_map_mapDerivedCategoryPlusIdIso_hom_app]
    rfl
  have hi := congrArg Iso.inv hp
  simp only [Functor.mapIso_inv, Iso.app_inv] at hi
  have h := unit_conjugateEquiv Adjunction.id
    (Etale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} R) (𝟙 X)).mapDerivedCategoryAdjunction
    (Functor.mapDerivedCategoryNatIso
      (Adjunction.leftAdjointIdIso
        (Etale.openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} R) (𝟙 X))
        (Etale.upperStarId (ModuleCat.{u + 1} R) X)) ≪≫
      Functor.mapDerivedCategoryIdIso _).hom K.obj
  rw [Etale.derived_open_id_conjugate] at h
  simp only [Adjunction.id_unit, NatTrans.id_app, Functor.id_obj,
    Category.id_comp] at h
  dsimp only [Etale.derivedPlusFormalism, ExchangeFormalism.pb,
    ExchangeFormalism.pbId, ExchangeFormalism.shAdj]
  simp only [Adjunction.id_unit, NatTrans.id_app, Functor.id_obj,
    Category.id_comp, Iso.symm_hom, Functor.map_comp, Etale.open_unit_plus,
    Etale.exact_map_plus, finiteSiteEtaleOpenId, Iso.trans_hom, NatTrans.comp_app,
    Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusIdIso_hom_app, hi]
  change (Functor.mapDerivedCategoryNatIso
      (Etale.upperStarId (ModuleCat.{u + 1} R) X) ≪≫
        Functor.mapDerivedCategoryIdIso _).inv.app K.obj =
    (Etale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} R) (𝟙 X)).mapDerivedCategoryAdjunction.unit.app K.obj ≫
      (Etale.upperStar (ModuleCat.{u + 1} R) (𝟙 X)).mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatIso
          ((Etale.openImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} R) (𝟙 X)).leftAdjointIdIso
              (Etale.upperStarId (ModuleCat.{u + 1} R) X))).hom.app K.obj) ≫
      (Etale.upperStar (ModuleCat.{u + 1} R) (𝟙 X)).mapDerivedCategory.map
        ((Functor.mapDerivedCategoryIdIso _).hom.app K.obj)
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc] using h

private theorem etale_compositor_unit_left
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c : Compactification f)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (coherenceEtaleCompositor R (Compactification.ofIsProper (𝟙 X)) c
        (c.copy (Category.id_comp f))).hom.app E =
      (coherenceEtaleFunctor R c).map
        (((Etale.derivedPlusFormalism (ModuleCat.{u + 1} R)).shriekOfIsProperIdIso X).hom.app
          E) := by
  have h := etale_compositor_tower R (Compactification.ofIsProper (𝟙 X)) c
    (c.copy (Category.id_comp f)) (Compactification.Triangle.unitLeft c) E
  simp only [Compactification.Triangle.unitLeft, coherenceEtaleChangeIso, coherenceEtaleFunctor,
    Etale.rightDerivedLowerShriekOfCompactificationPlusIso_refl,
    Iso.refl_hom, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id] at h
  simp only [towerEtaleIso, Etale.native_bounded_triangle_iso] at h
  have hn := NatTrans.congr_app
    ((Etale.derivedPlusFormalism (ModuleCat.{u + 1} R)).compIso_unitLeft c) E
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Etale.derivedPlusFormalism_shriek] at hn
  dsimp only [ExchangeFormalism.shriek, Etale.derivedPlusFormalism,
    Functor.comp_obj, Functor.comp_map, Functor.id_obj] at hn
  simp only [Category.comp_id] at hn
  dsimp only [ExchangeFormalism.shriek, Etale.derivedPlusFormalism,
    Functor.comp_obj, Functor.comp_map, Functor.id_obj, coherenceEtaleFunctor] at h ⊢
  exact h.trans hn

private theorem etale_compositor_unit_right
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c : Compactification f)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (coherenceEtaleCompositor R c (Compactification.ofIsProper (𝟙 Y))
        (c.copy (Category.comp_id f))).hom.app E =
      ((Etale.derivedPlusFormalism (ModuleCat.{u + 1} R)).shriekOfIsProperIdIso Y).hom.app
        ((coherenceEtaleFunctor R c).obj E) := by
  have h := etale_compositor_tower R c (Compactification.ofIsProper (𝟙 Y))
    (c.copy (Category.comp_id f)) (Compactification.Triangle.unitRight c) E
  simp only [Compactification.Triangle.unitRight, coherenceEtaleChangeIso, coherenceEtaleFunctor,
    Etale.rightDerivedLowerShriekOfCompactificationPlusIso_refl,
    Iso.refl_hom, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id] at h
  simp only [towerEtaleIso, Etale.native_bounded_triangle_iso] at h
  have hn := NatTrans.congr_app
    ((Etale.derivedPlusFormalism (ModuleCat.{u + 1} R)).compIso_unitRight c) E
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, Etale.derivedPlusFormalism_shriek] at hn
  dsimp only [ExchangeFormalism.shriek, Etale.derivedPlusFormalism,
    Functor.comp_obj, Functor.comp_map, Functor.id_obj] at hn
  simp only [Category.comp_id] at hn
  dsimp only [ExchangeFormalism.shriek, Etale.derivedPlusFormalism,
    Functor.comp_obj, Functor.comp_map, Functor.id_obj, coherenceEtaleFunctor] at h ⊢
  exact h.trans hn

private theorem compositor_assoc_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F F₀ : A ⥤ B} {G G₀ : B ⥤ C} {H H₀ : C ⥤ D}
    {P P₀ : A ⥤ C} {Q Q₀ : B ⥤ D} {S S₀ S₁ : A ⥤ D}
    (a : F ≅ F₀) (b : G ≅ G₀) (c : H ≅ H₀) (d : P ≅ P₀) (e : Q ≅ Q₀)
    (μ : F₀ ⋙ G₀ ≅ P₀) (ν : G₀ ⋙ H₀ ≅ Q₀)
    (ξ : P₀ ⋙ H₀ ≅ S₀) (ζ : F₀ ⋙ Q₀ ≅ S₁)
    (t₀ : S₀ ≅ S) (t₁ : S₁ ≅ S) (E : A)
    (h : H₀.map (μ.hom.app E) ≫ ξ.hom.app E ≫ t₀.hom.app E =
      ν.hom.app (F₀.obj E) ≫ ζ.hom.app E ≫ t₁.hom.app E) :
    H.map ((coherenceCompositorOfChanges F F₀ G G₀ P₀ P a b μ d.symm).hom.app E) ≫
        (coherenceCompositorOfChanges P P₀ H H₀ S₀ S d c ξ t₀).hom.app E =
      (coherenceCompositorOfChanges G G₀ H H₀ Q₀ Q b c ν e.symm).hom.app (F.obj E) ≫
        (coherenceCompositorOfChanges F F₀ Q Q₀ S₁ S a e ζ t₁).hom.app E := by
  simp only [compositor_component, Iso.symm_hom, Functor.map_comp, Category.assoc]
  slice_lhs 4 5 => rw [← H.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]
  simp only [Category.assoc]
  rw [c.hom.naturality_assoc, ← H.map_comp_assoc, b.hom.naturality,
    H.map_comp_assoc]
  rw [← e.inv.naturality_assoc, Iso.inv_hom_id_app_assoc]
  rw [← ν.hom.naturality_assoc]
  dsimp only [Functor.comp_map]
  rw [c.hom.naturality_assoc]
  rw [h]

private def formalCompositor (F : CompactSupportFormalism) [F.HasProperExchange]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g)) :
    F.shriek c ⋙ F.shriek d ≅ F.shriek e :=
  letI := c.hasCompactification
  letI := d.hasCompactification
  letI := e.hasCompactification
  coherenceCompositorOfChanges _ _ _ _ _ _
    (F.shriekIso c (HasCompactification.compactification f))
    (F.shriekIso d (HasCompactification.compactification g))
    (F.lowerShriekCompIso f g)
    (F.shriekIso (HasCompactification.compactification (f ≫ g)) e)

private theorem formal_change_copy (F : CompactSupportFormalism) [F.HasProperExchange]
    {X Y : Scheme.{u}} {f f' : X ⟶ Y} [QuasiCompact f] [QuasiCompact f']
    [HasCompactification f] [HasCompactification f'] (w : f = f')
    (d : Compactification f') :
    (F.shriekIso (HasCompactification.compactification f) (d.copy w)).hom =
      (F.lowerShriekCongr w).hom ≫
        (F.shriekIso (HasCompactification.compactification f') d).hom := by
  subst f'
  simp only [CompactSupportFormalism.lowerShriekCongr_refl, Iso.refl_hom, Category.id_comp]
  rfl

private theorem formal_compositor_assoc (F : CompactSupportFormalism) [F.HasProperExchange]
    {X Y Z W : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact h]
    (c : Compactification f) (d : Compactification g) (e : Compactification h)
    (cfg : Compactification (f ≫ g)) (cgh : Compactification (g ≫ h))
    (cfgh : Compactification (f ≫ g ≫ h)) (E : F.obj X) :
    (F.shriek e).map ((formalCompositor F c d cfg).hom.app E) ≫
        (formalCompositor F cfg e (cfgh.copy (Category.assoc f g h))).hom.app E =
      (formalCompositor F d e cgh).hom.app ((F.shriek c).obj E) ≫
        (formalCompositor F c cgh cfgh).hom.app E := by
  let := c.hasCompactification
  let := d.hasCompactification
  let := e.hasCompactification
  let := cfg.hasCompactification
  let := cgh.hasCompactification
  let := cfgh.hasCompactification
  let := (cfgh.copy (Category.assoc f g h)).hasCompactification
  have hn := congr_app (F.lowerShriekCompIso_assoc f g h) E
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at hn
  have ht := congrArg (fun t ↦ t ≫
      (F.shriekIso (HasCompactification.compactification (f ≫ g ≫ h)) cfgh).hom.app E) hn
  have hcopy := congr_app (formal_change_copy F (Category.assoc f g h) cfgh) E
  simp only [NatTrans.comp_app] at hcopy
  simp only [Category.assoc] at ht
  rw [← hcopy] at ht
  have hp := compositor_assoc_transport
    (F.shriekIso c (HasCompactification.compactification f))
    (F.shriekIso d (HasCompactification.compactification g))
    (F.shriekIso e (HasCompactification.compactification h))
    (F.shriekIso cfg (HasCompactification.compactification (f ≫ g)))
    (F.shriekIso cgh (HasCompactification.compactification (g ≫ h)))
    (F.lowerShriekCompIso f g) (F.lowerShriekCompIso g h)
    (F.lowerShriekCompIso (f ≫ g) h) (F.lowerShriekCompIso f (g ≫ h))
    (F.shriekIso (HasCompactification.compactification ((f ≫ g) ≫ h))
      (cfgh.copy (Category.assoc f g h)))
    (F.shriekIso (HasCompactification.compactification (f ≫ g ≫ h)) cfgh) E ht
  simp only [formalCompositor, F.shriekIso_symm] at hp ⊢
  dsimp only [CompactSupportFormalism.lowerShriek, CompactSupportFormalism.shriek,
    ExchangeFormalism.shriek,
    Compactification.copy] at hp ⊢
  exact hp

private theorem formalCompositor_etale
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g)) :
    formalCompositor (Etale.derivedPlusFormalism (ModuleCat.{u + 1} R)) c d e =
      coherenceEtaleCompositor R c d e := by
  unfold formalCompositor coherenceEtaleCompositor coherenceEtaleChangeIso
    coherenceChosenEtaleCompositorIso Etale.rightDerivedLowerShriekPlusCompIso
  simp only [Etale.derivedPlusFormalism_shriekIso]
  rfl

private theorem etale_compositor_assoc
    {X Y Z W : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ W}
    [QuasiCompact f] [QuasiCompact g] [QuasiCompact h]
    (c : Compactification f) (d : Compactification g) (e : Compactification h)
    (cfg : Compactification (f ≫ g)) (cgh : Compactification (g ≫ h))
    (cfgh : Compactification (f ≫ g ≫ h))
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (coherenceEtaleFunctor R e).map ((coherenceEtaleCompositor R c d cfg).hom.app E) ≫
        (coherenceEtaleCompositor R cfg e (cfgh.copy (Category.assoc f g h))).hom.app E =
      (coherenceEtaleCompositor R d e cgh).hom.app ((coherenceEtaleFunctor R c).obj E) ≫
        (coherenceEtaleCompositor R c cgh cfgh).hom.app E := by
  have h := formal_compositor_assoc (Etale.derivedPlusFormalism
    (ModuleCat.{u + 1} R)) c d e cfg cgh cfgh E
  simpa only [formalCompositor_etale, Etale.derivedPlusFormalism_shriek,
    coherenceEtaleFunctor] using h

section UnitCalculation
attribute [local implicit_reducible] ExchangeFormalism.shriek
attribute [local irreducible] Functor.rightDerivedFunctorPlus Functor.rightDerivedFunctor
  Functor.mapDerivedCategoryPlus Functor.mapDerivedCategory
end UnitCalculation

section AssociativityCalculation
attribute [local implicit_reducible] ExchangeFormalism.shriek
attribute [local irreducible] Functor.rightDerivedFunctorPlus Functor.rightDerivedFunctor
  Functor.mapDerivedCategoryPlus Functor.mapDerivedCategory

end AssociativityCalculation

end AlgebraicGeometry.ProEtale
