/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import all WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import all WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import all WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import all WeilConjectures.SixFunctors.BaseChange.Square
import all WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
import all WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SmoothPurity.CompactificationProjectionComposition
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived
import WeilConjectures.ProperBaseChange.RingedToposDerivedPushforwardComposition
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Mathlib.CategoryTheory.Sites.Subsheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpenEtaleCriterion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.Defs
import WeilConjectures.SixFunctors.OpenClosed.Complex
import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
import WeilConjectures.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
import WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeRepresentative
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointPullbackStalk
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointCanonicalGerm
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Compactification.BaseChange
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.SixFunctors.BaseChange.Pasting
import WeilConjectures.AlgebraicGeometry.Derived.DerivedExchangeModuleTermwiseSupplement
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenCompositionSupplement
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenInterchangeSupplement
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenPastingSupplement

/-! # Base change of a single explicit product-graph map

Source: Stacks Project, Tag 0F7F, applied factor by factor to the graph formula.
(blueprint: lem-pur-etale-graph-from-open-base-change).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar lowerStar openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  rightDerivedLowerStarComp rightDerivedLowerStarIdIso
  mapDerivedCategoryOpenImmersionLowerShriekComp
  mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso exactDerivedBaseChangeMap

/-- A functor word together with its successive base-change exchange. -/
private structure ExchangeWord
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    (P : C ⥤ C') (Q : D ⥤ D') where
  top : C ⥤ D
  bot : C' ⥤ D'
  exchange : top ⋙ Q ⟶ P ⋙ bot

private def ExchangeWord.comp
    {C C' D D' E E' : Type*}
    [Category C] [Category C'] [Category D] [Category D'] [Category E] [Category E']
    {P : C ⥤ C'} {Q : D ⥤ D'} {R : E ⥤ E'}
    (w : ExchangeWord P Q) (z : ExchangeWord Q R) : ExchangeWord P R where
  top := w.top ⋙ z.top
  bot := w.bot ⋙ z.bot
  exchange := (TwoSquare.hComp (TwoSquare.mk _ _ _ _ w.exchange)
    (TwoSquare.mk _ _ _ _ z.exchange)).natTrans

private def ExchangeWord.id
    {C C' : Type*} [Category C] [Category C'] (P : C ⥤ C') : ExchangeWord P P where
  top := 𝟭 C
  bot := 𝟭 C'
  exchange := (Functor.leftUnitor P).hom ≫ (Functor.rightUnitor P).inv

/-- An isomorphism of words which commutes with their exchanges. -/
private structure ExchangeIso
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    {P : C ⥤ C'} {Q : D ⥤ D'} (w z : ExchangeWord P Q) where
  top : w.top ≅ z.top
  bot : w.bot ≅ z.bot
  comm : Functor.whiskerRight top.hom Q ≫ z.exchange =
    w.exchange ≫ Functor.whiskerLeft P bot.hom

private def ExchangeIso.trans
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    {P : C ⥤ C'} {Q : D ⥤ D'} {w z t : ExchangeWord P Q}
    (e : ExchangeIso w z) (d : ExchangeIso z t) : ExchangeIso w t where
  top := e.top ≪≫ d.top
  bot := e.bot ≪≫ d.bot
  comm := by
    simp only [Iso.trans_hom, Functor.whiskerRight_comp, Functor.whiskerLeft_comp]
    rw [Category.assoc, d.comm, ← Category.assoc, e.comm, Category.assoc]

private def ExchangeIso.symm
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    {P : C ⥤ C'} {Q : D ⥤ D'} {w z : ExchangeWord P Q}
    (e : ExchangeIso w z) : ExchangeIso z w where
  top := e.top.symm
  bot := e.bot.symm
  comm := by
    ext K
    have h := congr_app e.comm K
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h ⊢
    apply (cancel_mono (e.bot.hom.app (P.obj K))).1
    simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [← h, ← Category.assoc, ← Q.map_comp, Iso.inv_hom_id_app, Q.map_id]
    erw [Category.id_comp, Category.comp_id]

private def ExchangeIso.comp
    {C C' D D' E E' : Type*}
    [Category C] [Category C'] [Category D] [Category D'] [Category E] [Category E']
    {P : C ⥤ C'} {Q : D ⥤ D'} {R : E ⥤ E'}
    {w w' : ExchangeWord P Q} {z z' : ExchangeWord Q R}
    (e : ExchangeIso w w') (d : ExchangeIso z z') :
    ExchangeIso (w.comp z) (w'.comp z') where
  top := Functor.isoWhiskerRight e.top z.top ≪≫ Functor.isoWhiskerLeft w'.top d.top
  bot := Functor.isoWhiskerRight e.bot z.bot ≪≫ Functor.isoWhiskerLeft w'.bot d.bot
  comm := by
    ext K
    have he := congr_app e.comm K
    have hd := congr_app d.comm (w'.top.obj K)
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at he hd
    simp only [ExchangeWord.comp, TwoSquare.hComp, TwoSquare.mk, TwoSquare.natTrans,
      Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc]
    dsimp only [Functor.comp_obj, Functor.comp_map]
    have hn := z.exchange.naturality (e.top.hom.app K)
    dsimp only [Functor.comp_map] at hn
    rw [reassoc_of% hd, reassoc_of% hn]
    have hn' := d.bot.hom.naturality (w'.exchange.app K)
    dsimp only [Functor.comp_obj] at hn'
    rw [← hn']
    rw [← z.bot.map_comp_assoc, he, Functor.map_comp, Category.assoc]

private def ExchangeIso.refl
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    {P : C ⥤ C'} {Q : D ⥤ D'} (w : ExchangeWord P Q) : ExchangeIso w w where
  top := Iso.refl _
  bot := Iso.refl _
  comm := by simp

private def ExchangeIso.associator
    {C C' D D' E E' F F' : Type*}
    [Category C] [Category C'] [Category D] [Category D']
    [Category E] [Category E'] [Category F] [Category F']
    {P : C ⥤ C'} {Q : D ⥤ D'} {R : E ⥤ E'} {S : F ⥤ F'}
    (w : ExchangeWord P Q) (z : ExchangeWord Q R) (t : ExchangeWord R S) :
    ExchangeIso ((w.comp z).comp t) (w.comp (z.comp t)) where
  top := Functor.associator _ _ _
  bot := Functor.associator _ _ _
  comm := by
    ext K
    simp [ExchangeWord.comp, TwoSquare.hComp, Functor.map_comp, Category.assoc]

private def ExchangeIso.leftUnitor
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    {P : C ⥤ C'} {Q : D ⥤ D'} (w : ExchangeWord P Q) :
    ExchangeIso ((ExchangeWord.id P).comp w) w where
  top := Functor.leftUnitor _
  bot := Functor.leftUnitor _
  comm := by
    ext K
    simp [ExchangeWord.comp, ExchangeWord.id, TwoSquare.hComp]

end AlgebraicGeometry.Etale
