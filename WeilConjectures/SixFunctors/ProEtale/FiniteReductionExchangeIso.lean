/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.CompleteExchangeMap
public import WeilConjectures.SixFunctors.ProEtale.CompleteDerivedCompletion
public import WeilConjectures.SixFunctors.ClassicalDefinition
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import all WeilConjectures.AlgebraicGeometry.ExactCondensedExchangeComparison
import WeilConjectures.CategoryTheory.DerivedExactCube
import all WeilConjectures.AlgebraicGeometry.FiniteProperExchange
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.RingTheory.Ideal.Quotient.Index
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import all WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all Mathlib.Algebra.Homology.ShortComplex.Ab
import all WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import all Mathlib.Topology.Bases
import all Mathlib.Topology.MetricSpace.Pseudo.Defs
import all Mathlib.Analysis.SpecificLimits.Basic
import all Mathlib.Topology.LocallyConstant.Basic
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import all WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import all Mathlib.CategoryTheory.Center.Linear
import all Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import all WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import all Mathlib.Topology.Algebra.Order.Field
import all WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import all Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import all Mathlib.Algebra.Order.AbsoluteValue.Basic
import all Mathlib.LinearAlgebra.FiniteDimensional.Basic
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.RingTheory.DiscreteValuationRing.Basic
import all Mathlib.RingTheory.Localization.FractionRing
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.NumberTheory.Padics.ProperSpace
import all Mathlib.Topology.Algebra.Valued.LocallyCompact
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import all WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.AlgebraicGeometry.FreeParameterScalarMaps
import WeilConjectures.AlgebraicGeometry.ComapUpperStarIsoComposition
import WeilConjectures.CategoryTheory.Adjunction.CoefficientExchange
import all WeilConjectures.AlgebraicGeometry.FiniteCoefficientExchangeEncoding
import WeilConjectures.AlgebraicGeometry.BoundedBelowProEtaleComparison
import WeilConjectures.AlgebraicGeometry.ClassicalDerivedEquivalence
import all WeilConjectures.AlgebraicGeometry.ClassicalDerivedCounit
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange

/-! Finite-level exchange for the integral reduction tower.

Source: the finite-reduction portion of
`literature/blueprint/latest/blueprint/sec-proper-base-change/
sk-prop-pbc-complete/det-pbc-complete-exchange-iso.proof.md`.
(blueprint: det-pbc-complete-exchange-iso-finite-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v w z

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CompleteDerivedCompletion

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.modulesDerived AdicCompletion.finiteRingMonoidalObject
  AdicCompletion.finiteRingCommutative AdicCompletion.finiteModulesDerived

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Mod.derivedExtendMapDerivedCategoryAdjunction
  CondensedRing.upperStar CondensedRing.lowerStar DerivedCategory upperStarFromPoint
  HasDerivedCategory.standard Functor.mapDerivedCategoryNatIso Functor.mapDerivedCategoryCompIso
  Mod.monoidalCategory Mod.monoidalCategoryStruct Mod.monoidalClosed

attribute [local instance 20000] sheafMonoidalCategory sheafBraidedCategory
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.W.monoidal

attribute [local instance 30000] isCommMonObj_condensedRingObj

set_option maxHeartbeats 200000 in
-- The concrete localized functors have large coefficient and site instances.
private theorem moduleSquare_exact (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' p' p g) :
    (modulePullSquare l E sq).hom =
      (Functor.mapDerivedCategorySquareIso
        (condensedPullbackSquareFor (DerivedNakayama.integerRing l E) sq)).hom := by
  simpa only [modulePullSquare, modulePullComp, dpullModule, exactComp] using
    exact_square_normalizationFor (DerivedNakayama.integerRing l E) sq

set_option maxHeartbeats 200000 in
-- The concrete localized functors have large coefficient and site instances.
private theorem towerSquare_exact (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' p' p g) :
    (towerPullSquare l E sq).hom =
      (Functor.mapDerivedCategorySquareIso
        (F₁ := pull l E g) (F₂ := pull l E p')
        (G₁ := pull l E p) (G₂ := pull l E g')
        ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso
          (condensedPullbackSquareFor (DerivedNakayama.integerRing l E) sq))).hom := by
  have ht (a b : X' ⟶ Y) (h : a = b) :
      (Functor.mapDerivedCategoryNatIso
        ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso
          (eqToIso (congrArg (CondensedRing.upperStar
            (DerivedNakayama.integerRing l E)) h)))).hom =
        (eqToIso (congrArg (dpull l E) h)).hom := by
    cases h
    simp only [eqToIso_refl, Functor.mapIso_refl, Functor.mapDerivedCategoryNatIso_refl,
      Iso.refl_hom]
  have hp := derived_paste_square
    (F₁ := pull l E g) (F₂ := pull l E p')
    (G₁ := pull l E p) (G₂ := pull l E g')
    ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso
      (CondensedRing.upperStarComp (DerivedNakayama.integerRing l E) p' g))
    ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso
      (eqToIso (congrArg (CondensedRing.upperStar
        (DerivedNakayama.integerRing l E)) sq.w.symm)))
    ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso
      (CondensedRing.upperStarComp (DerivedNakayama.integerRing l E) g' p))
  rw [ht _ _ sq.w.symm] at hp
  simpa only [towerPullSquare, towerPullComp, condensedPullbackSquareFor,
    Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_hom, Iso.symm_hom,
    Category.assoc] using hp.symm

set_option maxHeartbeats 200000 in
-- The concrete localized functors have large coefficient and site instances.
private theorem evaluationSquare_eq (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {U V : Scheme.{u}} (f : U ⟶ V) (n : ℕ) :
    Functor.mapDerivedCategorySquareIso
      (F₁ := pull l E f) (F₂ := ev l E U n)
      (G₁ := ev l E V n)
      (G₂ := CondensedRing.upperStar (DerivedNakayama.integerRing l E) f)
      (Iso.refl _) = pullEvaluation l E f n := by
  apply Iso.ext
  simp only [Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_refl,
    Iso.trans_hom, Category.id_comp]
  rfl

-- Localize the six faces together so their source and target models stay aligned.
private theorem localizedCube
    {C : Type w} {D : Type w} {E : Type w} {F : Type w}
  {G : Type w} {H : Type w} {I : Type w} {J : Type w}
  [Category.{v} C] [Abelian C] [HasDerivedCategory.{z} C]
  [Category.{v} D] [Abelian D] [HasDerivedCategory.{z} D]
  [Category.{v} E] [Abelian E] [HasDerivedCategory.{z} E]
  [Category.{v} F] [Abelian F] [HasDerivedCategory.{z} F]
  [Category.{v} G] [Abelian G] [HasDerivedCategory.{z} G]
  [Category.{v} H] [Abelian H] [HasDerivedCategory.{z} H]
  [Category.{v} I] [Abelian I] [HasDerivedCategory.{z} I]
  [Category.{v} J] [Abelian J] [HasDerivedCategory.{z} J]
  (a : C ⥤ D)
  (b : D ⥤ E)
  (c : E ⥤ F)
  (d : C ⥤ G)
  (e : G ⥤ E)
  (f : G ⥤ H)
  (g : H ⥤ F)
  (h : C ⥤ I)
  (i : I ⥤ H)
  (j : D ⥤ J)
  (k : J ⥤ F)
  (m : I ⥤ J)
  [a.Additive] [PreservesFiniteLimits a] [PreservesFiniteColimits a]
  [b.Additive] [PreservesFiniteLimits b] [PreservesFiniteColimits b]
  [c.Additive] [PreservesFiniteLimits c] [PreservesFiniteColimits c]
  [d.Additive] [PreservesFiniteLimits d] [PreservesFiniteColimits d]
  [e.Additive] [PreservesFiniteLimits e] [PreservesFiniteColimits e]
  [f.Additive] [PreservesFiniteLimits f] [PreservesFiniteColimits f]
  [g.Additive] [PreservesFiniteLimits g] [PreservesFiniteColimits g]
  [h.Additive] [PreservesFiniteLimits h] [PreservesFiniteColimits h]
  [i.Additive] [PreservesFiniteLimits i] [PreservesFiniteColimits i]
  [j.Additive] [PreservesFiniteLimits j] [PreservesFiniteColimits j]
  [k.Additive] [PreservesFiniteLimits k] [PreservesFiniteColimits k]
  [m.Additive] [PreservesFiniteLimits m] [PreservesFiniteColimits m]
    (q1 : a ⋙ b ≅ d ⋙ e)
    (q2 : e ⋙ c ≅ f ⋙ g)
    (q3 : d ⋙ f ≅ h ⋙ i)
    (q4 : b ⋙ c ≅ j ⋙ k)
    (q5 : a ⋙ j ≅ h ⋙ m)
    (q6 : m ⋙ k ≅ i ⋙ g)
    (comm : ∀ X : C,
      c.map (q1.hom.app X) ≫ q2.hom.app (d.obj X) ≫ g.map (q3.hom.app X) =
        q4.hom.app (a.obj X) ≫ k.map (q5.hom.app X) ≫ q6.hom.app (h.obj X))
    (s1 : a.mapDerivedCategory ⋙ b.mapDerivedCategory ≅ d.mapDerivedCategory ⋙ e.mapDerivedCategory)
    (s2 : e.mapDerivedCategory ⋙ c.mapDerivedCategory ≅ f.mapDerivedCategory ⋙ g.mapDerivedCategory)
    (s3 : d.mapDerivedCategory ⋙ f.mapDerivedCategory ≅ h.mapDerivedCategory ⋙ i.mapDerivedCategory)
    (s4 : b.mapDerivedCategory ⋙ c.mapDerivedCategory ≅ j.mapDerivedCategory ⋙ k.mapDerivedCategory)
    (s5 : a.mapDerivedCategory ⋙ j.mapDerivedCategory ≅ h.mapDerivedCategory ⋙ m.mapDerivedCategory)
    (s6 : m.mapDerivedCategory ⋙ k.mapDerivedCategory ≅ i.mapDerivedCategory ⋙ g.mapDerivedCategory)
    (h1 : s1.hom = (Functor.mapDerivedCategorySquareIso q1).hom)
    (h2 : s2.hom = (Functor.mapDerivedCategorySquareIso q2).hom)
    (h3 : s3.hom = (Functor.mapDerivedCategorySquareIso q3).hom)
    (h4 : s4.hom = (Functor.mapDerivedCategorySquareIso q4).hom)
    (h5 : s5.hom = (Functor.mapDerivedCategorySquareIso q5).hom)
    (h6 : s6.hom = (Functor.mapDerivedCategorySquareIso q6).hom)
    (M : DerivedCategory C) :
    Adjunction.coefficientPullbackSquare s1.hom s6.hom s3 s4 s5.hom s2.hom M := by
  unfold Adjunction.coefficientPullbackSquare
  rw [h1, h2, h3, h4, h5, h6]
  exact NatTrans.congr_app (Functor.mapDerivedCategory_exactCube
    a b c d e f g h i j k m q1 q2 q3 q4 q5 q6 comm) M

-- Evaluation commutes strictly with whiskering and with the ordinary pullback square.
private theorem evaluationOrdinaryCube
    {I : Type*} [Category I] {C D E F : Type w}
    [Category.{v} C] [Category.{v} D] [Category.{v} E] [Category.{v} F]
    {a : C ⥤ D} {b : D ⥤ F} {c : C ⥤ E} {d : E ⥤ F}
    (q : a ⋙ b ≅ c ⋙ d) (N : I ⥤ C) (i : I) :
    ((evaluation I F).obj i).map
        (((Functor.whiskeringRight I C F).mapIso q).hom.app N) ≫
      𝟙 _ ≫ d.map (𝟙 _) =
      𝟙 _ ≫ b.map (𝟙 _) ≫ q.hom.app (((evaluation I C).obj i).obj N) := by
  rw [d.map_id, b.map_id]
  change q.hom.app (N.obj i) ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _ ≫ q.hom.app (N.obj i)
  simp only [CategoryTheory.Category.comp_id, CategoryTheory.Category.id_comp]

private theorem evaluatedDerivedCube
    {C D E F : Type (v + 1)}
    [Category.{v} C] [Abelian C] [HasDerivedCategory.{z} C]
    [Category.{v} D] [Abelian D] [HasDerivedCategory.{z} D]
    [Category.{v} E] [Abelian E] [HasDerivedCategory.{z} E]
    [Category.{v} F] [Abelian F] [HasDerivedCategory.{z} F]
    [HasDerivedCategory.{z} (ℕᵒᵖ ⥤ C)] [HasDerivedCategory.{z} (ℕᵒᵖ ⥤ D)]
    [HasDerivedCategory.{z} (ℕᵒᵖ ⥤ E)] [HasDerivedCategory.{z} (ℕᵒᵖ ⥤ F)]
    (a : C ⥤ D) (b : D ⥤ F) (c : C ⥤ E) (d : E ⥤ F)
    [a.Additive] [PreservesFiniteLimits a] [PreservesFiniteColimits a]
    [b.Additive] [PreservesFiniteLimits b] [PreservesFiniteColimits b]
    [c.Additive] [PreservesFiniteLimits c] [PreservesFiniteColimits c]
    [d.Additive] [PreservesFiniteLimits d] [PreservesFiniteColimits d]
    (q : a ⋙ b ≅ c ⋙ d) (i : ℕᵒᵖ)
    (s1 : (((Functor.whiskeringRight ℕᵒᵖ C D).obj a).mapDerivedCategory) ⋙
        (((Functor.whiskeringRight ℕᵒᵖ D F).obj b).mapDerivedCategory) ≅
      (((Functor.whiskeringRight ℕᵒᵖ C E).obj c).mapDerivedCategory) ⋙
        (((Functor.whiskeringRight ℕᵒᵖ E F).obj d).mapDerivedCategory))
    (s2 : (((Functor.whiskeringRight ℕᵒᵖ E F).obj d).mapDerivedCategory) ⋙
        (((evaluation ℕᵒᵖ F).obj i).mapDerivedCategory) ≅
      (((evaluation ℕᵒᵖ E).obj i).mapDerivedCategory) ⋙ d.mapDerivedCategory)
    (s3 : (((Functor.whiskeringRight ℕᵒᵖ C E).obj c).mapDerivedCategory) ⋙
        (((evaluation ℕᵒᵖ E).obj i).mapDerivedCategory) ≅
      (((evaluation ℕᵒᵖ C).obj i).mapDerivedCategory) ⋙ c.mapDerivedCategory)
    (s4 : (((Functor.whiskeringRight ℕᵒᵖ D F).obj b).mapDerivedCategory) ⋙
        (((evaluation ℕᵒᵖ F).obj i).mapDerivedCategory) ≅
      (((evaluation ℕᵒᵖ D).obj i).mapDerivedCategory) ⋙ b.mapDerivedCategory)
    (s5 : (((Functor.whiskeringRight ℕᵒᵖ C D).obj a).mapDerivedCategory) ⋙
        (((evaluation ℕᵒᵖ D).obj i).mapDerivedCategory) ≅
      (((evaluation ℕᵒᵖ C).obj i).mapDerivedCategory) ⋙ a.mapDerivedCategory)
    (s6 : a.mapDerivedCategory ⋙ b.mapDerivedCategory ≅
      c.mapDerivedCategory ⋙ d.mapDerivedCategory)
    (h1 : s1.hom = (Functor.mapDerivedCategorySquareIso
      (F₁ := (Functor.whiskeringRight ℕᵒᵖ C D).obj a)
      (F₂ := (Functor.whiskeringRight ℕᵒᵖ D F).obj b)
      (G₁ := (Functor.whiskeringRight ℕᵒᵖ C E).obj c)
      (G₂ := (Functor.whiskeringRight ℕᵒᵖ E F).obj d)
      ((Functor.whiskeringRight ℕᵒᵖ C F).mapIso q)).hom)
    (h2 : s2.hom = (Functor.mapDerivedCategorySquareIso
      (F₁ := (Functor.whiskeringRight ℕᵒᵖ E F).obj d)
      (F₂ := (evaluation ℕᵒᵖ F).obj i)
      (G₁ := (evaluation ℕᵒᵖ E).obj i) (G₂ := d) (Iso.refl _)).hom)
    (h3 : s3.hom = (Functor.mapDerivedCategorySquareIso
      (F₁ := (Functor.whiskeringRight ℕᵒᵖ C E).obj c)
      (F₂ := (evaluation ℕᵒᵖ E).obj i)
      (G₁ := (evaluation ℕᵒᵖ C).obj i) (G₂ := c) (Iso.refl _)).hom)
    (h4 : s4.hom = (Functor.mapDerivedCategorySquareIso
      (F₁ := (Functor.whiskeringRight ℕᵒᵖ D F).obj b)
      (F₂ := (evaluation ℕᵒᵖ F).obj i)
      (G₁ := (evaluation ℕᵒᵖ D).obj i) (G₂ := b) (Iso.refl _)).hom)
    (h5 : s5.hom = (Functor.mapDerivedCategorySquareIso
      (F₁ := (Functor.whiskeringRight ℕᵒᵖ C D).obj a)
      (F₂ := (evaluation ℕᵒᵖ D).obj i)
      (G₁ := (evaluation ℕᵒᵖ C).obj i) (G₂ := a) (Iso.refl _)).hom)
    (h6 : s6.hom = (Functor.mapDerivedCategorySquareIso q).hom)
    (M : DerivedCategory (ℕᵒᵖ ⥤ C)) :
    Adjunction.coefficientPullbackSquare s1.hom s6.hom s3 s4 s5.hom s2.hom M := by
  exact @localizedCube (ℕᵒᵖ ⥤ C) (ℕᵒᵖ ⥤ D) (ℕᵒᵖ ⥤ F) F
    (ℕᵒᵖ ⥤ E) E C D
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((Functor.whiskeringRight ℕᵒᵖ C D).obj a)
    ((Functor.whiskeringRight ℕᵒᵖ D F).obj b) ((evaluation ℕᵒᵖ F).obj i)
    ((Functor.whiskeringRight ℕᵒᵖ C E).obj c)
    ((Functor.whiskeringRight ℕᵒᵖ E F).obj d) ((evaluation ℕᵒᵖ E).obj i) d
    ((evaluation ℕᵒᵖ C).obj i) c ((evaluation ℕᵒᵖ D).obj i) b a
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((Functor.whiskeringRight ℕᵒᵖ C F).mapIso q)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) q
    (fun N ↦ evaluationOrdinaryCube q N i)
    s1 s2 s3 s4 s5 s6 h1 h2 h3 h4 h5 h6 M

set_option maxHeartbeats 200000 in
-- Normalize all six concrete tower faces in one generic exact cube.
private theorem evaluationCube (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' p' p g)
    (n : ℕ) (M : DTow l E Y) :
    Adjunction.coefficientPullbackSquare
      (towerPullSquare l E sq).hom (modulePullSquare l E sq).hom
      (pullEvaluation l E p n) (pullEvaluation l E p' n)
      (pullEvaluation l E g n).hom (pullEvaluation l E g' n).hom M := by
  let R := DerivedNakayama.integerRing l E
  exact evaluatedDerivedCube
    (CondensedRing.upperStar R g) (CondensedRing.upperStar R p')
    (CondensedRing.upperStar R p) (CondensedRing.upperStar R g')
    (condensedPullbackSquareFor R sq) (op n)
    (towerPullSquare l E sq) (pullEvaluation l E g' n)
    (pullEvaluation l E p n) (pullEvaluation l E p' n)
    (pullEvaluation l E g n) (modulePullSquare l E sq)
    (towerSquare_exact l E sq)
    (congrArg Iso.hom (evaluationSquare_eq l E g' n).symm)
    (congrArg Iso.hom (evaluationSquare_eq l E p n).symm)
    (congrArg Iso.hom (evaluationSquare_eq l E p' n).symm)
    (congrArg Iso.hom (evaluationSquare_eq l E g n).symm)
    (moduleSquare_exact l E sq) M


-- The counit characterization of mates turns pullback coherence into exchange coherence.
private theorem exchangeMateCube
    {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type w}
    [Category.{v} C₁] [Category.{v} C₂] [Category.{v} C₃] [Category.{v} C₄]
    [Category.{v} D₁] [Category.{v} D₂] [Category.{v} D₃] [Category.{v} D₄]
    {U : C₁ ⥤ C₂} {R₀ : C₂ ⥤ C₁} {V : C₃ ⥤ C₄} {S : C₄ ⥤ C₃}
    {Ue : D₁ ⥤ D₂} {Re : D₂ ⥤ D₁} {Ve : D₃ ⥤ D₄} {Se : D₄ ⥤ D₃}
    (a : U ⊣ R₀) (b : V ⊣ S) (ae : Ue ⊣ Re) (be : Ve ⊣ Se)
    {G : C₁ ⥤ C₃} {H : C₂ ⥤ C₄} {Ge : D₁ ⥤ D₃} {He : D₂ ⥤ D₄}
    {T₁ : C₁ ⥤ D₁} {T₂ : C₂ ⥤ D₂} {T₃ : C₃ ⥤ D₃} {T₄ : C₄ ⥤ D₄}
    (θ : G ⋙ V ⟶ U ⋙ H) (θe : Ge ⋙ Ve ⟶ Ue ⋙ He)
    (αU : U ⋙ T₂ ≅ T₁ ⋙ Ue) (αV : V ⋙ T₄ ≅ T₃ ⋙ Ve)
    (αG : G ⋙ T₃ ≅ T₁ ⋙ Ge) (αH : H ⋙ T₄ ≅ T₂ ⋙ He)
    (K : C₂)
    (hcube : Adjunction.coefficientPullbackSquare θ θe αU αV αG.hom αH.hom (R₀.obj K)) :
    αG.hom.app (R₀.obj K) ≫
      Ge.map (((mateEquiv a ae αU.inv).natTrans).app K) ≫
      ((mateEquiv ae be (TwoSquare.mk _ _ _ _ θe)).natTrans).app (T₂.obj K) =
    T₃.map (((mateEquiv a b (TwoSquare.mk _ _ _ _ θ)).natTrans).app K) ≫
      ((mateEquiv b be αV.inv).natTrans).app (H.obj K) ≫
      Se.map (αH.hom.app K) := by
  exact Adjunction.coefficient_exchange_of_counit_at a b ae be θ θe K
    ((mateEquiv a b (TwoSquare.mk _ _ _ _ θ)).natTrans.app K)
    ((mateEquiv ae be (TwoSquare.mk _ _ _ _ θe)).natTrans.app (T₂.obj K))
    (mateEquiv_counit a b (TwoSquare.mk _ _ _ _ θ) K)
    (mateEquiv_counit ae be (TwoSquare.mk _ _ _ _ θe) (T₂.obj K))
    αU αV αG.hom αH.hom
    ((mateEquiv a ae αU.inv).natTrans.app K)
    ((mateEquiv b be αV.inv).natTrans.app (H.obj K))
    (mateEquiv_counit a ae αU.inv K) (mateEquiv_counit b be αV.inv (H.obj K)) hcube

private theorem exchangeMate_isIso
    {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type w}
    [Category.{v} C₁] [Category.{v} C₂] [Category.{v} C₃] [Category.{v} C₄]
    [Category.{v} D₁] [Category.{v} D₂] [Category.{v} D₃] [Category.{v} D₄]
    {U : C₁ ⥤ C₂} {R₀ : C₂ ⥤ C₁} {V : C₃ ⥤ C₄} {S : C₄ ⥤ C₃}
    {Ue : D₁ ⥤ D₂} {Re : D₂ ⥤ D₁} {Ve : D₃ ⥤ D₄} {Se : D₄ ⥤ D₃}
    (a : U ⊣ R₀) (b : V ⊣ S) (ae : Ue ⊣ Re) (be : Ve ⊣ Se)
    {G : C₁ ⥤ C₃} {H : C₂ ⥤ C₄} {Ge : D₁ ⥤ D₃} {He : D₂ ⥤ D₄}
    {T₁ : C₁ ⥤ D₁} {T₂ : C₂ ⥤ D₂} {T₃ : C₃ ⥤ D₃} {T₄ : C₄ ⥤ D₄}
    (θ : G ⋙ V ⟶ U ⋙ H) (θe : Ge ⋙ Ve ⟶ Ue ⋙ He)
    (αU : U ⋙ T₂ ≅ T₁ ⋙ Ue) (αV : V ⋙ T₄ ≅ T₃ ⋙ Ve)
    (αG : G ⋙ T₃ ≅ T₁ ⋙ Ge) (αH : H ⋙ T₄ ≅ T₂ ⋙ He)
    (K : C₂)
    [IsIso (((mateEquiv a b (TwoSquare.mk _ _ _ _ θ)).natTrans).app K)]
    [IsIso (((mateEquiv a ae αU.inv).natTrans).app K)]
    [IsIso (((mateEquiv b be αV.inv).natTrans).app (H.obj K))]
    (hcube : Adjunction.coefficientPullbackSquare θ θe αU αV αG.hom αH.hom (R₀.obj K)) :
    IsIso (((mateEquiv ae be (TwoSquare.mk _ _ _ _ θe)).natTrans).app (T₂.obj K)) := by
  have he := exchangeMateCube a b ae be θ θe αU αV αG αH K hcube
  have : IsIso (αG.hom.app (R₀.obj K) ≫
      Ge.map (((mateEquiv a ae αU.inv).natTrans).app K) ≫
      ((mateEquiv ae be (TwoSquare.mk _ _ _ _ θe)).natTrans).app (T₂.obj K)) := by
    rw [he]
    infer_instance
  have : IsIso (Ge.map (((mateEquiv a ae αU.inv).natTrans).app K) ≫
      ((mateEquiv ae be (TwoSquare.mk _ _ _ _ θe)).natTrans).app (T₂.obj K)) :=
    IsIso.of_isIso_comp_left (αG.hom.app (R₀.obj K)) _
  exact IsIso.of_isIso_comp_left (Ge.map (((mateEquiv a ae αU.inv).natTrans).app K)) _

private theorem exchangeMate_map_isIso
    {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type w}
    [Category.{v} C₁] [Category.{v} C₂] [Category.{v} C₃] [Category.{v} C₄]
    [Category.{v} D₁] [Category.{v} D₂] [Category.{v} D₃] [Category.{v} D₄]
    {U : C₁ ⥤ C₂} {R₀ : C₂ ⥤ C₁} {V : C₃ ⥤ C₄} {S : C₄ ⥤ C₃}
    {Ue : D₁ ⥤ D₂} {Re : D₂ ⥤ D₁} {Ve : D₃ ⥤ D₄} {Se : D₄ ⥤ D₃}
    (a : U ⊣ R₀) (b : V ⊣ S) (ae : Ue ⊣ Re) (be : Ve ⊣ Se)
    {G : C₁ ⥤ C₃} {H : C₂ ⥤ C₄} {Ge : D₁ ⥤ D₃} {He : D₂ ⥤ D₄}
    {T₁ : C₁ ⥤ D₁} {T₂ : C₂ ⥤ D₂} {T₃ : C₃ ⥤ D₃} {T₄ : C₄ ⥤ D₄}
    (θ : G ⋙ V ⟶ U ⋙ H) (θe : Ge ⋙ Ve ⟶ Ue ⋙ He)
    (αU : U ⋙ T₂ ≅ T₁ ⋙ Ue) (αV : V ⋙ T₄ ≅ T₃ ⋙ Ve)
    (αG : G ⋙ T₃ ≅ T₁ ⋙ Ge) (αH : H ⋙ T₄ ≅ T₂ ⋙ He)
    (K : C₂)
    [IsIso (((mateEquiv ae be (TwoSquare.mk _ _ _ _ θe)).natTrans).app (T₂.obj K))]
    [IsIso (((mateEquiv a ae αU.inv).natTrans).app K)]
    [IsIso (((mateEquiv b be αV.inv).natTrans).app (H.obj K))]
    (hcube : Adjunction.coefficientPullbackSquare θ θe αU αV αG.hom αH.hom (R₀.obj K)) :
    IsIso (T₃.map (((mateEquiv a b (TwoSquare.mk _ _ _ _ θ)).natTrans).app K)) := by
  have he := exchangeMateCube a b ae be θ θe αU αV αG αH K hcube
  have hfull : IsIso (T₃.map (((mateEquiv a b (TwoSquare.mk _ _ _ _ θ)).natTrans).app K) ≫
      ((mateEquiv b be αV.inv).natTrans).app (H.obj K) ≫ Se.map (αH.hom.app K)) := by
    rw [← he]
    infer_instance
  have : IsIso ((T₃.map (((mateEquiv a b (TwoSquare.mk _ _ _ _ θ)).natTrans).app K) ≫
      ((mateEquiv b be αV.inv).natTrans).app (H.obj K)) ≫ Se.map (αH.hom.app K)) := by
    simpa only [Category.assoc] using hfull
  have : IsIso (T₃.map (((mateEquiv a b (TwoSquare.mk _ _ _ _ θ)).natTrans).app K) ≫
      ((mateEquiv b be αV.inv).natTrans).app (H.obj K)) :=
    IsIso.of_isIso_comp_right _ (Se.map (αH.hom.app K))
  exact IsIso.of_isIso_comp_right _ (((mateEquiv b be αV.inv).natTrans).app (H.obj K))


set_option maxHeartbeats 1000000 in
-- The concrete localized functors have large coefficient and site instances.
private theorem fixed_etale_origin (A : Type (u + 1)) [CommRing A]
    [TopologicalSpace A] [DiscreteTopology A] (X : Scheme.{u})
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (hb : ∃ b : ℤ, N.IsGE b)
    (hc : ∀ q : ℤ, IsClassical
      ((sheafCompose (Scheme.ProEt.topology X) (forget (ModuleCat.{u + 1} A))).obj
        ((DerivedCategory.homologyFunctor _ q).obj N))) :
    ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X N := by
  let Np : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) := ⟨N, hb⟩
  have hclassical : ClassicalPlus X A Np := by
    intro q
    apply classicalModule_of_iso X A ((classicalHomologyIso X A q).app N)
    intro I _ _ P
    let H := (DerivedCategory.homologyFunctor _ q).obj N
    let V := forget (ModuleCat.{u + 1} A)
    have hi : IsIso (continuityMap P (H.obj ⋙ V)) :=
      (CategoryTheory.isIso_iff_bijective _).mpr (hc q P)
    have he : (preservesColimitIso V (sectionDiagram P H.obj)).inv ≫
        V.map (continuityMap P H.obj) = continuityMap P (H.obj ⋙ V) :=
      preservesColimitIso_inv_comp_desc V (sectionDiagram P H.obj) (sectionCocone P H.obj)
    have : IsIso (V.map (continuityMap P H.obj)) := by
      apply (isIso_comp_left_iff
        (preservesColimitIso V (sectionDiagram P H.obj)).inv _).mp
      rw [he]
      exact hi
    exact isIso_of_reflects_iso (continuityMap P H.obj) V
  have hu := (boundedBelowComparison X A).1
  have he := classicalDerivedEquivalence X A (fun L ↦ by let := hu; infer_instance)
  have := he.2.1 Np hclassical
  let L := (comparisonLowerStar (ModuleCat.{u + 1} A) X).rightDerivedFunctorPlus.obj Np
  let e : (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L.obj ≅ N :=
    ((Functor.mapDerivedCategoryPlusCompatibility
      (comparisonUpperStar (ModuleCat.{u + 1} A) X)).app L).symm ≪≫
      DerivedCategory.Plus.ι.mapIso
        (asIso ((comparisonAdjunction (ModuleCat.{u + 1} A) X).derivedPlus.counit.app Np))
  exact ⟨L.obj, L.property, ⟨e⟩⟩

set_option maxHeartbeats 1000000 in
-- The concrete localized functors have large coefficient and site instances.
private theorem finiteInternalExchange_isIso (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' p' p g) [IsProper p]
    (K : DerivedCategory (FiniteDiscreteOrdinary.Internal A X))
    (hb : ∃ b : ℤ, K.IsGE b)
    (hc : ∀ q : ℤ, IsClassicalModuleSheaf
      ((InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology X)
        (condensedRingObj (FiniteDiscreteOrdinary.coefficient A) X)).functor.obj
          ((DerivedCategory.homologyFunctor _ q).obj K))) :
    IsIso ((CondensedRing.finiteProperExchange (FiniteDiscreteOrdinary.coefficient A)
      sq.toCommSq).app K) := by
  classical
  let enc := fun T : Scheme.{u} ↦ (FiniteDiscreteOrdinary.encoding_exists A T).some
  let C := Mod.comap (D := Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (coefficientMap (𝟙 (FiniteDiscreteOrdinary.coefficient A)) X)
  let F := (enc X).ordinary.functor ⋙ (enc X).fixed.functor
  let N := (F.mapDerivedCategory).obj (C.mapDerivedCategory.obj K)
  have hbN : ∃ b : ℤ, N.IsGE b := by
    obtain ⟨b, hb⟩ := hb
    let := hb
    let := C.isGE_mapDerivedCategory_obj K b
    exact ⟨b, F.isGE_mapDerivedCategory_obj _ b⟩
  let V := sheafCompose (Scheme.ProEt.topology X)
    (forget (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
  have hf (M : FiniteDiscreteOrdinary.Internal A X) :
      V.obj (F.obj (C.obj M)) ≅
        ((sheafCompose (Scheme.ProEt.topology X) (forget AddCommGrpCat.{u + 1})).obj
          ((SheafOfModules.toSheaf _).obj
            ((InternalAbelianSheafModule.sectionModuleEquivalence
              (Scheme.ProEt.topology X)
              (condensedRingObj (FiniteDiscreteOrdinary.coefficient A) X)).functor.obj M))) := by
    dsimp only [F, Functor.comp_obj]
    rw [(enc X).ordinary_functor, (enc X).fixed_functor]
    exact Iso.refl _
  have hcN : ∀ q : ℤ, IsClassical
      (V.obj ((DerivedCategory.homologyFunctor _ q).obj N)) := by
    intro q
    let e := F.mapIso ((C.mapDerivedCategoryHomologyFunctorIso q).app K) ≪≫
      (F.mapDerivedCategoryHomologyFunctorIso q).app (C.mapDerivedCategory.obj K)
    apply (isClassical_iso_iff (V.mapIso e)).mp
    apply (isClassical_iso_iff (hf ((DerivedCategory.homologyFunctor _ q).obj K))).mpr
    exact hc q
  have hN := fixed_etale_origin (ULift.{u + 1, u} A) X N hbN hcN
  have hPB : IsPullback g' p' p g :=
    IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  have hi := ProEtale.isIso_derivedBaseChangeMap_app_of_isProper
    (ULift.{u + 1, u} A) hPB N hN
  apply (FiniteDiscreteOrdinary.finiteCoefficientExchangeEncoding_isIso A
    (Iso.refl _) enc sq K).mpr
  exact hi

private theorem finiteExchange_eq
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' p' p g) :
    CondensedRing.finiteProperExchange R sq = CondensedRing.moduleObjectDerivedExchange R sq := by
  have hs : CondensedRing.finitePullbackSquare R sq =
      CondensedRing.moduleObjectDerivedPullbackSquareComparison R sq := by
    unfold CondensedRing.finitePullbackSquare
      CondensedRing.moduleObjectDerivedPullbackSquareComparison
    rw [CondensedRing.finitePullbackCongr_eqToIso]
    rfl
  rw [CondensedRing.finiteProperExchange_eq_mate, hs]
  rfl

private theorem finiteExact_transfer
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' p' p g)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj R X)))
    (hi : IsIso ((CondensedRing.finiteProperExchange R sq).app K)) :
    IsIso ((exactCondensedExchangeFor R sq).app K) := by
  have hi' : IsIso ((CondensedRing.moduleObjectDerivedExchange R sq).app K) := by
    rw [← finiteExchange_eq]
    exact hi
  exact (Arrow.isIso_iff_isIso_of_isIso
    (totalDerivedExchange_exact_comparisonFor R sq K).some.hom).mp hi'

set_option maxHeartbeats 1000000 in
-- The concrete localized functors have large coefficient and site instances.
private theorem finiteInternalExact_isIso (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' p' p g) [IsProper p]
    (K : DerivedCategory (FiniteDiscreteOrdinary.Internal A X))
    (hb : ∃ b : ℤ, K.IsGE b)
    (hc : ∀ q : ℤ, IsClassicalModuleSheaf
      ((InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology X)
        (condensedRingObj (FiniteDiscreteOrdinary.coefficient A) X)).functor.obj
          ((DerivedCategory.homologyFunctor _ q).obj K))) :
    IsIso ((exactCondensedExchangeFor (FiniteDiscreteOrdinary.coefficient A)
      sq.toCommSq).app K) := by
  exact finiteExact_transfer (FiniteDiscreteOrdinary.coefficient A) sq.toCommSq K
    (finiteInternalExchange_isIso A sq K hb hc)

private theorem coefficient_comm_symmetric
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (T : Scheme.{u}) :
    @IsCommMonObj (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) _ _
      (sheafSymmetricCategory (A := Ab.{u + 1}) T).toBraidedCategory
      (condensedRingObj R T) _ := by
  simpa only [sheafSymmetricCategory, sheafMonoidalCategory,
    GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall,
    GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall,
    ModuleObjectRingedComparison.sectionProEtaleBraiding,
    ModuleObjectRingedComparison.sectionComparisonBraiding] using
      ModuleObjectRingedComparison.sectionProEtaleRingComm R T

attribute [local instance 40000] coefficient_comm_symmetric

private theorem doubleMate_isIso
    {A B C D : Type w} [Category.{v} A] [Category.{v} B] [Category.{v} C] [Category.{v} D]
    {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B}
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (s : L₁ ⊣ R₁) (t : L₂ ⊣ R₂) (aR : F₁ ⊣ U₁) (aS : F₂ ⊣ U₂)
    (r : TwoSquare R₁ F₂ F₁ R₂)
    [IsIso (((mateEquiv s t).symm r).natTrans)] :
    IsIso ((mateEquiv aS aR r).natTrans) := by
  let χ := ((mateEquiv s t).symm r).natTrans
  let e := conjugateIsoEquiv (aR.comp t) (s.comp aS) (asIso χ).symm
  have h := iterated_mateEquiv_conjugateEquiv s t aR aS
    (TwoSquare.mk _ _ _ _ χ)
  have hm : mateEquiv s t (TwoSquare.mk _ _ _ _ χ) = r :=
    (mateEquiv s t).apply_symm_apply r
  rw [hm] at h
  have he : e.inv = (mateEquiv aS aR r).natTrans := by
    simpa only [e, conjugateIsoEquiv_apply_inv, Iso.symm_inv, asIso_hom,
      TwoSquare.natTrans] using h.symm
  rw [← he]
  infer_instance

set_option maxHeartbeats 200000 in
-- The concrete localized functors have large coefficient and site instances.
private theorem restrictionMate_isIso
    (R S : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] [IsCommMonObj S.X]
    (a : R.X ⟶ S.X) [IsMonHom a] {U V : Scheme.{u}} (f : U ⟶ V) :
    IsIso ((mateEquiv
      (CondensedRing.upperStarLowerStarAdjunction S.X f).mapDerivedCategoryRightDerivedAdjunction
      (CondensedRing.upperStarLowerStarAdjunction R.X f).mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ (CondensedRing.derivedComapUpperStarIso a f).inv)).natTrans) := by
  have hRV : IsCommMonObj (condensedRingObj R.X V) := isCommMonObj_condensedRingObj R.X V
  have hSV : IsCommMonObj (condensedRingObj S.X V) := isCommMonObj_condensedRingObj S.X V
  have hRU : IsCommMonObj (condensedRingObj R.X U) := isCommMonObj_condensedRingObj R.X U
  have hSU : IsCommMonObj (condensedRingObj S.X U) := isCommMonObj_condensedRingObj S.X U
  let s := Mod.derivedExtendMapDerivedCategoryAdjunction
    (R := condensedRingObj R.X V) (S := condensedRingObj S.X V) (coefficientMap a V)
  let t := Mod.derivedExtendMapDerivedCategoryAdjunction
    (R := condensedRingObj R.X U) (S := condensedRingObj S.X U) (coefficientMap a U)
  let r := (CondensedRing.derivedComapUpperStarIso a f).inv
  let χ := ((mateEquiv s t).symm (TwoSquare.mk _ _ _ _ r)).natTrans
  have hχ (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj R.X V))) :
      IsIso (χ.app M) := by
    unfold χ s t r
    with_unfolding_all exact FreeParameterEvaluation.scalarPullComparison_isIso R S a f M
  have : IsIso χ := NatIso.isIso_of_isIso_app χ
  exact doubleMate_isIso s t
    (CondensedRing.upperStarLowerStarAdjunction R.X f).mapDerivedCategoryRightDerivedAdjunction
    (CondensedRing.upperStarLowerStarAdjunction S.X f).mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ r)

section RestrictionCoherence

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
attribute [local instance 40000] sheafMonoidalCategory sheafBraidedCategory
attribute [local instance 3000000] Functor.LaxBraided.toLaxMonoidal

private theorem mappedCompositionSquareIso
    {C D : Type w} [Category.{v} C] [Category.{v} D] (F : C ⥤ D)
    {A B C₀ D₀ : C} {A' B' C' D' P Q : D}
    (r₁ : A ≅ B) (r₂ : C₀ ≅ D₀) (e : A ≅ C₀)
    (s₁ : A' ≅ B') (s₂ : C' ≅ D') (e' : A' ≅ C')
    (a₀ : F.obj A ⟶ A') (a₁ : F.obj C₀ ⟶ C')
    (β₁ : F.obj B ⟶ P) (γ₁ : P ⟶ B')
    (β₂ : F.obj D₀ ⟶ Q) (γ₂ : Q ⟶ D')
    (h₁ : F.map r₁.hom ≫ β₁ ≫ γ₁ = a₀ ≫ s₁.hom)
    (h₂ : F.map r₂.hom ≫ β₂ ≫ γ₂ = a₁ ≫ s₂.hom)
    (he : F.map e.hom ≫ a₁ = a₀ ≫ e'.hom) :
    F.map ((r₁.symm ≪≫ e ≪≫ r₂).hom) ≫ β₂ ≫ γ₂ =
      β₁ ≫ γ₁ ≫ (s₁.symm ≪≫ e' ≪≫ s₂).hom := by
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc] using
    FiniteDiscreteOrdinary.mappedCompositionSquare F r₁ r₂ e s₁ s₂ e'
      a₀ a₁ (β₁ ≫ γ₁) (β₂ ≫ γ₂) h₁ h₂ he

private theorem compositionCube
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type w}
    [Category.{v} C₀] [Category.{v} C₁] [Category.{v} C₂] [Category.{v} C₃]
    [Category.{v} D₀] [Category.{v} D₁] [Category.{v} D₂] [Category.{v} D₃]
    {F₁ : C₀ ⥤ C₁} {F₂ : C₁ ⥤ C₃} {F₃ : C₀ ⥤ C₂} {F₄ : C₂ ⥤ C₃}
    {G₁ : D₀ ⥤ D₁} {G₂ : D₁ ⥤ D₃} {G₃ : D₀ ⥤ D₂} {G₄ : D₂ ⥤ D₃}
    {U V : C₀ ⥤ C₃} {U' V' : D₀ ⥤ D₃}
    {T₀ : C₀ ⥤ D₀} {T₁ : C₁ ⥤ D₁} {T₂ : C₂ ⥤ D₂} {T₃ : C₃ ⥤ D₃}
    (c₁ : U ≅ F₁ ⋙ F₂) (c₂ : V ≅ F₃ ⋙ F₄) (e : U ≅ V)
    (d₁ : U' ≅ G₁ ⋙ G₂) (d₂ : V' ≅ G₃ ⋙ G₄) (e' : U' ≅ V')
    (a₀ : U ⋙ T₃ ≅ T₀ ⋙ U') (a₁ : V ⋙ T₃ ≅ T₀ ⋙ V')
    (β₁ : F₁ ⋙ T₁ ≅ T₀ ⋙ G₁) (γ₁ : F₂ ⋙ T₃ ≅ T₁ ⋙ G₂)
    (β₂ : F₃ ⋙ T₂ ≅ T₀ ⋙ G₃) (γ₂ : F₄ ⋙ T₃ ≅ T₂ ⋙ G₄)
    (θ : F₁ ⋙ F₂ ≅ F₃ ⋙ F₄) (θe : G₁ ⋙ G₂ ≅ G₃ ⋙ G₄)
    (hθ : θ = c₁.symm ≪≫ e ≪≫ c₂) (hθe : θe = d₁.symm ≪≫ e' ≪≫ d₂)
    (M : C₀)
    (h₁ : T₃.map (c₁.hom.app M) ≫ γ₁.hom.app (F₁.obj M) ≫ G₂.map (β₁.hom.app M) =
      a₀.hom.app M ≫ d₁.hom.app (T₀.obj M))
    (h₂ : T₃.map (c₂.hom.app M) ≫ γ₂.hom.app (F₃.obj M) ≫ G₄.map (β₂.hom.app M) =
      a₁.hom.app M ≫ d₂.hom.app (T₀.obj M))
    (he : T₃.map (e.hom.app M) ≫ a₁.hom.app M =
      a₀.hom.app M ≫ e'.hom.app (T₀.obj M)) :
    Adjunction.coefficientPullbackSquare θ.hom θe.hom β₂ γ₁ β₁.hom γ₂.hom M := by
  subst θ θe
  simpa only [Adjunction.coefficientPullbackSquare, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, NatTrans.comp_app, Category.assoc] using
    mappedCompositionSquareIso T₃ (c₁.app M) (c₂.app M) (e.app M)
      (d₁.app (T₀.obj M)) (d₂.app (T₀.obj M)) (e'.app (T₀.obj M))
      (a₀.hom.app M) (a₁.hom.app M)
      (γ₁.hom.app (F₁.obj M)) (G₂.map (β₁.hom.app M))
      (γ₂.hom.app (F₃.obj M)) (G₄.map (β₂.hom.app M)) h₁ h₂ he

-- The equality face of the cube is automatic for a natural family of comparisons.
private theorem familyEqualityCube
    {P : Type*} {C₀ C₃ D₀ D₃ : Type w}
    [Category.{v} C₀] [Category.{v} C₃] [Category.{v} D₀] [Category.{v} D₃]
    (F : P → C₀ ⥤ C₃) (G : P → D₀ ⥤ D₃)
    (T₀ : C₀ ⥤ D₀) (T₃ : C₃ ⥤ D₃)
    (e : ∀ x, F x ⋙ T₃ ≅ T₀ ⋙ G x)
    (x y : P) (h : x = y) (M : C₀) :
    T₃.map ((eqToIso (congrArg F h)).hom.app M) ≫ (e y).hom.app M =
      (e x).hom.app M ≫ (eqToIso (congrArg G h)).hom.app (T₀.obj M) := by
  cases h
  change T₃.map (𝟙 ((F x).obj M)) ≫ (e x).hom.app M =
    (e x).hom.app M ≫ 𝟙 ((G x).obj (T₀.obj M))
  rw [T₃.map_id, Category.id_comp]
  exact (Category.comp_id _).symm

private theorem compositionFamilyCube
    {P : Type*} {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type w}
    [Category.{v} C₀] [Category.{v} C₁] [Category.{v} C₂] [Category.{v} C₃]
    [Category.{v} D₀] [Category.{v} D₁] [Category.{v} D₂] [Category.{v} D₃]
    {F₁ : C₀ ⥤ C₁} {F₂ : C₁ ⥤ C₃} {F₃ : C₀ ⥤ C₂} {F₄ : C₂ ⥤ C₃}
    {G₁ : D₀ ⥤ D₁} {G₂ : D₁ ⥤ D₃} {G₃ : D₀ ⥤ D₂} {G₄ : D₂ ⥤ D₃}
    {T₀ : C₀ ⥤ D₀} {T₁ : C₁ ⥤ D₁} {T₂ : C₂ ⥤ D₂} {T₃ : C₃ ⥤ D₃}
    (F : P → C₀ ⥤ C₃) (G : P → D₀ ⥤ D₃)
    (e : ∀ x, F x ⋙ T₃ ≅ T₀ ⋙ G x) (x y : P) (h : x = y)
    (c₁ : F x ≅ F₁ ⋙ F₂) (c₂ : F y ≅ F₃ ⋙ F₄)
    (d₁ : G x ≅ G₁ ⋙ G₂) (d₂ : G y ≅ G₃ ⋙ G₄)
    (β₁ : F₁ ⋙ T₁ ≅ T₀ ⋙ G₁) (γ₁ : F₂ ⋙ T₃ ≅ T₁ ⋙ G₂)
    (β₂ : F₃ ⋙ T₂ ≅ T₀ ⋙ G₃) (γ₂ : F₄ ⋙ T₃ ≅ T₂ ⋙ G₄)
    (θ : F₁ ⋙ F₂ ≅ F₃ ⋙ F₄) (θe : G₁ ⋙ G₂ ≅ G₃ ⋙ G₄)
    (hθ : θ = c₁.symm ≪≫ eqToIso (congrArg F h) ≪≫ c₂)
    (hθe : θe = d₁.symm ≪≫ eqToIso (congrArg G h) ≪≫ d₂)
    (M : C₀)
    (h₁ : T₃.map (c₁.hom.app M) ≫ γ₁.hom.app (F₁.obj M) ≫ G₂.map (β₁.hom.app M) =
      (e x).hom.app M ≫ d₁.hom.app (T₀.obj M))
    (h₂ : T₃.map (c₂.hom.app M) ≫ γ₂.hom.app (F₃.obj M) ≫ G₄.map (β₂.hom.app M) =
      (e y).hom.app M ≫ d₂.hom.app (T₀.obj M)) :
    Adjunction.coefficientPullbackSquare θ.hom θe.hom β₂ γ₁ β₁.hom γ₂.hom M := by
  exact compositionCube c₁ c₂ (eqToIso (congrArg F h)) d₁ d₂
    (eqToIso (congrArg G h)) (e x) (e y) β₁ γ₁ β₂ γ₂ θ θe hθ hθe M h₁ h₂
    (familyEqualityCube F G T₀ T₃ e x y h M)

-- Combine composition coherence with localization before specializing coefficient categories.
private theorem localizedCompositionFamilyCube
    {P : Type*} {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type w}
    [Category.{v} C₀] [Abelian C₀] [HasDerivedCategory.{z} C₀]
    [Category.{v} C₁] [Abelian C₁] [HasDerivedCategory.{z} C₁]
    [Category.{v} C₂] [Abelian C₂] [HasDerivedCategory.{z} C₂]
    [Category.{v} C₃] [Abelian C₃] [HasDerivedCategory.{z} C₃]
    [Category.{v} D₀] [Abelian D₀] [HasDerivedCategory.{z} D₀]
    [Category.{v} D₁] [Abelian D₁] [HasDerivedCategory.{z} D₁]
    [Category.{v} D₂] [Abelian D₂] [HasDerivedCategory.{z} D₂]
    [Category.{v} D₃] [Abelian D₃] [HasDerivedCategory.{z} D₃]
    {F₁ : C₀ ⥤ C₁} {F₂ : C₁ ⥤ C₃} {F₃ : C₀ ⥤ C₂} {F₄ : C₂ ⥤ C₃}
    {G₁ : D₀ ⥤ D₁} {G₂ : D₁ ⥤ D₃} {G₃ : D₀ ⥤ D₂} {G₄ : D₂ ⥤ D₃}
    {T₀ : C₀ ⥤ D₀} {T₁ : C₁ ⥤ D₁} {T₂ : C₂ ⥤ D₂} {T₃ : C₃ ⥤ D₃}
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [F₃.Additive] [PreservesFiniteLimits F₃] [PreservesFiniteColimits F₃]
    [F₄.Additive] [PreservesFiniteLimits F₄] [PreservesFiniteColimits F₄]
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    [G₃.Additive] [PreservesFiniteLimits G₃] [PreservesFiniteColimits G₃]
    [G₄.Additive] [PreservesFiniteLimits G₄] [PreservesFiniteColimits G₄]
    [T₀.Additive] [PreservesFiniteLimits T₀] [PreservesFiniteColimits T₀]
    [T₁.Additive] [PreservesFiniteLimits T₁] [PreservesFiniteColimits T₁]
    [T₂.Additive] [PreservesFiniteLimits T₂] [PreservesFiniteColimits T₂]
    [T₃.Additive] [PreservesFiniteLimits T₃] [PreservesFiniteColimits T₃]
    (F : P → C₀ ⥤ C₃) (G : P → D₀ ⥤ D₃)
    (e : ∀ x, F x ⋙ T₃ ≅ T₀ ⋙ G x) (x y : P) (h : x = y)
    (c₁ : F x ≅ F₁ ⋙ F₂) (c₂ : F y ≅ F₃ ⋙ F₄)
    (d₁ : G x ≅ G₁ ⋙ G₂) (d₂ : G y ≅ G₃ ⋙ G₄)
    (β₁ : F₁ ⋙ T₁ ≅ T₀ ⋙ G₁) (γ₁ : F₂ ⋙ T₃ ≅ T₁ ⋙ G₂)
    (β₂ : F₃ ⋙ T₂ ≅ T₀ ⋙ G₃) (γ₂ : F₄ ⋙ T₃ ≅ T₂ ⋙ G₄)
    (θ : F₁ ⋙ F₂ ≅ F₃ ⋙ F₄) (θe : G₁ ⋙ G₂ ≅ G₃ ⋙ G₄)
    (hθ : θ = c₁.symm ≪≫ eqToIso (congrArg F h) ≪≫ c₂)
    (hθe : θe = d₁.symm ≪≫ eqToIso (congrArg G h) ≪≫ d₂)
    (h₁ : ∀ M : C₀, T₃.map (c₁.hom.app M) ≫ γ₁.hom.app (F₁.obj M) ≫ G₂.map (β₁.hom.app M) =
      (e x).hom.app M ≫ d₁.hom.app (T₀.obj M))
    (h₂ : ∀ M : C₀, T₃.map (c₂.hom.app M) ≫ γ₂.hom.app (F₃.obj M) ≫ G₄.map (β₂.hom.app M) =
      (e y).hom.app M ≫ d₂.hom.app (T₀.obj M))
    (s1 : F₁.mapDerivedCategory ⋙ F₂.mapDerivedCategory ≅
      F₃.mapDerivedCategory ⋙ F₄.mapDerivedCategory)
    (s2 : F₄.mapDerivedCategory ⋙ T₃.mapDerivedCategory ≅
      T₂.mapDerivedCategory ⋙ G₄.mapDerivedCategory)
    (s3 : F₃.mapDerivedCategory ⋙ T₂.mapDerivedCategory ≅
      T₀.mapDerivedCategory ⋙ G₃.mapDerivedCategory)
    (s4 : F₂.mapDerivedCategory ⋙ T₃.mapDerivedCategory ≅
      T₁.mapDerivedCategory ⋙ G₂.mapDerivedCategory)
    (s5 : F₁.mapDerivedCategory ⋙ T₁.mapDerivedCategory ≅
      T₀.mapDerivedCategory ⋙ G₁.mapDerivedCategory)
    (s6 : G₁.mapDerivedCategory ⋙ G₂.mapDerivedCategory ≅
      G₃.mapDerivedCategory ⋙ G₄.mapDerivedCategory)
    (hs1 : s1.hom = (Functor.mapDerivedCategorySquareIso θ).hom)
    (hs2 : s2.hom = (Functor.mapDerivedCategorySquareIso γ₂).hom)
    (hs3 : s3.hom = (Functor.mapDerivedCategorySquareIso β₂).hom)
    (hs4 : s4.hom = (Functor.mapDerivedCategorySquareIso γ₁).hom)
    (hs5 : s5.hom = (Functor.mapDerivedCategorySquareIso β₁).hom)
    (hs6 : s6.hom = (Functor.mapDerivedCategorySquareIso θe).hom)
    (M : DerivedCategory C₀) :
    Adjunction.coefficientPullbackSquare s1.hom s6.hom s3 s4 s5.hom s2.hom M := by
  exact localizedCube F₁ F₂ T₃ F₃ F₄ T₂ G₄ T₀ G₃ T₁ G₂ G₁
    θ γ₂ β₂ γ₁ β₁ θe
    (fun N ↦ compositionFamilyCube F G e x y h c₁ c₂ d₁ d₂
      β₁ γ₁ β₂ γ₂ θ θe hθ hθe N (h₁ N) (h₂ N))
    s1 s2 s3 s4 s5 s6 hs1 hs2 hs3 hs4 hs5 hs6 M

attribute [-instance] ModuleObjectRingedComparison.coefficientMonoid in
private theorem restrictionComposition
    (R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W)
    (N : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj S W)) :
    (Mod.comap (coefficientMap a U)).map ((CondensedRing.upperStarComp S f g).hom.app N) ≫
      (CondensedRing.comapUpperStarIso a f).hom.app ((CondensedRing.upperStar S g).obj N) ≫
      (CondensedRing.upperStar R f).map ((CondensedRing.comapUpperStarIso a g).hom.app N) =
    (CondensedRing.comapUpperStarIso a (f ≫ g)).hom.app N ≫
      (CondensedRing.upperStarComp R f g).hom.app
        ((Mod.comap (coefficientMap a W)).obj N) := by
  exact (((CondensedRing.comapUpperStarIso a (f ≫ g)).app N).inv_comp_eq).mp
    (CondensedRing.comapUpperStarIso_comp a f g N).symm
set_option maxHeartbeats 1000000 in
-- The concrete localized functors have large coefficient and site instances.
attribute [-instance] ModuleObjectRingedComparison.coefficientMonoid in
private theorem restrictionExchange_isIso
    (R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' p' p g)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj S X)))
    [IsIso ((exactCondensedExchangeFor S sq).app M)] :
    IsIso ((exactCondensedExchangeFor R sq).app
      ((Mod.comap (coefficientMap a X)).mapDerivedCategory.obj M)) := by
  let α {U V : Scheme.{u}} (f : U ⟶ V) := CondensedRing.derivedComapUpperStarIso a f
  let δ {U V : Scheme.{u}} (f : U ⟶ V) := (mateEquiv
    (CondensedRing.upperStarLowerStarAdjunction S f).mapDerivedCategoryRightDerivedAdjunction
    (CondensedRing.upperStarLowerStarAdjunction R f).mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (α f).inv)).natTrans
  have hi {U V : Scheme.{u}} (f : U ⟶ V) : IsIso (δ f) :=
    restrictionMate_isIso (Mon.mk R) (Mon.mk S) a f
  let := hi p
  let := hi p'
  have hcube := localizedCompositionFamilyCube
    (CondensedRing.upperStar S) (CondensedRing.upperStar R)
    (fun f ↦ CondensedRing.comapUpperStarIso a f) (p' ≫ g) (g' ≫ p) sq.w.symm
    (CondensedRing.upperStarComp S p' g) (CondensedRing.upperStarComp S g' p)
    (CondensedRing.upperStarComp R p' g) (CondensedRing.upperStarComp R g' p)
    (CondensedRing.comapUpperStarIso a g) (CondensedRing.comapUpperStarIso a p')
    (CondensedRing.comapUpperStarIso a p) (CondensedRing.comapUpperStarIso a g')
    (condensedPullbackSquareFor S sq) (condensedPullbackSquareFor R sq)
    (by unfold condensedPullbackSquareFor; rfl) (by unfold condensedPullbackSquareFor; rfl)
    (fun N ↦ restrictionComposition R S a p' g N)
    (fun N ↦ restrictionComposition R S a g' p N)
    (Functor.mapDerivedCategorySquareIso (condensedPullbackSquareFor S sq))
    (α g') (α p) (α p') (α g)
    (Functor.mapDerivedCategorySquareIso (condensedPullbackSquareFor R sq))
    rfl rfl rfl rfl rfl rfl
  unfold exactCondensedExchangeFor at *
  exact exchangeMate_isIso
    (CondensedRing.upperStarLowerStarAdjunction S p).mapDerivedCategoryRightDerivedAdjunction
    (CondensedRing.upperStarLowerStarAdjunction S p').mapDerivedCategoryRightDerivedAdjunction
    (CondensedRing.upperStarLowerStarAdjunction R p).mapDerivedCategoryRightDerivedAdjunction
    (CondensedRing.upperStarLowerStarAdjunction R p').mapDerivedCategoryRightDerivedAdjunction
    (Functor.mapDerivedCategorySquareIso (condensedPullbackSquareFor S sq)).hom
    (Functor.mapDerivedCategorySquareIso (condensedPullbackSquareFor R sq)).hom
    (α p) (α p') (α g) (α g') M
    (hcube ((CondensedRing.lowerStar S p).rightDerivedFunctor.obj M))

end RestrictionCoherence

set_option maxHeartbeats 1000000 in
-- The concrete localized functors have large coefficient and site instances.
private theorem moduleExchange_exact (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' p' p g) :
    moduleExchange l E sq = exactCondensedExchangeFor
      (DerivedNakayama.integerRing l E) sq := by
  unfold moduleExchange exactCondensedExchangeFor moduleAdjunction
  rw [moduleSquare_exact]

private theorem forallType_heq {A B : Sort v} {P : A → Sort w} {Q : B → Sort w}
    (hAB : A = B) (h : ∀ a b, HEq a b → P a = Q b) :
    HEq ((a : A) → P a) ((b : B) → Q b) := by
  cases hAB
  have hp : P = Q := funext fun a ↦ h a a (HEq.refl a)
  cases hp
  rfl

-- The localization models differ in proof arguments to their category instances.
-- Build explicit congruences using proof irrelevance instead of asking the kernel to
-- repeatedly unfold the full module and tower constructions at each theorem boundary.
-- Every cast is justified by an equality proof; the resulting term is checked normally.
local elab "exact_structural " t:term : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let e ← Lean.Elab.Term.elabTermAndSynthesize t none
    let e ← Lean.instantiateMVars e
    let memo ← IO.mkRef ({} : Std.HashMap (Lean.Expr × Lean.Expr) Lean.Expr)
    let toEq (h : Lean.Expr) : Lean.MetaM Lean.Expr :=
      Lean.Meta.mkAppM ``eq_of_heq #[h]
    let toHEq (h : Lean.Expr) : Lean.MetaM Lean.Expr := do
      if (← Lean.Meta.whnf (← Lean.Meta.inferType h)).getAppFn.isConstOf ``Eq then
        Lean.Meta.mkAppM ``heq_of_eq #[h]
      else pure h
    let rec expandHead (t : Lean.Expr) : Lean.MetaM Lean.Expr := do
      match t with
      | .mdata _ e => expandHead e
      | .app f a => return Lean.mkApp (← expandHead f) a
      | .proj sn idx a =>
        let some info := Lean.getStructureInfo? (← Lean.getEnv) sn
          | Lean.throwError "Unknown structure"
        Lean.Expr.mkDirectProjection a info.fieldNames[idx]!
      | t => return t
    let rec go (fuel : Nat) (x₀ y₀ : Lean.Expr) : Lean.MetaM Lean.Expr := do
      let x ← expandHead x₀
      let y ← expandHead y₀
      if x == y then return ← Lean.Meta.mkHEqRefl x
      if let some h := (← memo.get).get? (x, y) then return h
      match fuel with
      | 0 => Lean.throwError "Structural congruence exhausted its depth"
      | fuel + 1 =>
        let objComp (e : Lean.Expr) : Lean.MetaM Lean.Expr := do
          let args := e.getAppArgs
          if e.getAppFn.isConstOf ``Functor.obj && args.size == 6 then
            let f := args[4]!
            let fs := f.getAppArgs
            if f.getAppFn.isConstOf ``Functor.comp && fs.size == 8 then
              let inner ← Lean.Meta.mkAppM ``Functor.obj #[fs[6]!, args[5]!]
              return ← Lean.Meta.mkAppM ``Functor.obj #[fs[7]!, inner]
          return e
        let x' ← objComp x
        let y' ← objComp y
        if x' != x || y' != y then return ← go fuel x' y'
        let h ← if (← Lean.Meta.isProof x) && (← Lean.Meta.isProof y) then
          pure (Lean.mkApp4 (.const ``proof_irrel_heq [])
            (← Lean.Meta.inferType x) (← Lean.Meta.inferType y) x y)
        else if x.isApp && y.isApp && x.getAppFn == y.getAppFn &&
            x.getAppNumArgs == y.getAppNumArgs then do
          try
            let xs := x.getAppArgs
            let ys := y.getAppArgs
            let th ← Lean.Meta.mkHCongrWithArity x.getAppFn xs.size
            let mut args : Array Lean.Expr := #[]
            for xa in xs, ya in ys, kind in th.argKinds do
              let p ← go fuel xa ya
              match kind with
              | .eq => args := args.push xa |>.push ya |>.push (← toEq p)
              | .heq => args := args.push xa |>.push ya |>.push p
              | _ => Lean.throwError "Unexpected congruence argument kind"
            toHEq (Lean.mkAppN th.proof args)
          catch err =>
            let x' ← expandHead (← Lean.Meta.withTransparency .default (Lean.Meta.whnf x))
            let y' ← expandHead (← Lean.Meta.withTransparency .default (Lean.Meta.whnf y))
            if x' != x || y' != y then go fuel x' y'
            else throw err
        else if x.isLambda && y.isLambda then do
          let xt ← Lean.Meta.whnf (← Lean.Meta.inferType x)
          let yt ← Lean.Meta.whnf (← Lean.Meta.inferType y)
          let dx := xt.bindingDomain!
          let dy := yt.bindingDomain!
          let hd ← toEq (← go fuel dx dy)
          let hp ← Lean.Meta.withLocalDeclD `a dx fun a =>
            Lean.Meta.withLocalDeclD `b dy fun b => do
              let hab ← Lean.Meta.mkAppM ``HEq #[a, b]
              Lean.Meta.withLocalDeclD `hab hab fun hab => do
                memo.modify (·.insert (a, b) hab)
                let hb ← go fuel (Lean.mkApp x a) (Lean.mkApp y b)
                Lean.Meta.mkLambdaFVars #[a, b, hab] hb
          let px := Lean.Expr.lam xt.bindingName! dx xt.bindingBody! .default
          let py := Lean.Expr.lam yt.bindingName! dy yt.bindingBody! .default
          Lean.Meta.mkAppOptM ``Function.hfunext
            #[some dx, some dy, some px, some py, some x, some y, some hd, some hp]
        else if x.isForall && y.isForall then do
          let dx := x.bindingDomain!
          let dy := y.bindingDomain!
          let hd ← toEq (← go fuel dx dy)
          let px := Lean.Expr.lam x.bindingName! dx x.bindingBody! .default
          let py := Lean.Expr.lam y.bindingName! dy y.bindingBody! .default
          let hp ← Lean.Meta.withLocalDeclD `a dx fun a =>
            Lean.Meta.withLocalDeclD `b dy fun b => do
              let hab ← Lean.Meta.mkAppM ``HEq #[a, b]
              Lean.Meta.withLocalDeclD `hab hab fun hab => do
                memo.modify (·.insert (a, b) hab)
                let hb ← toEq (← go fuel (Lean.mkApp px a) (Lean.mkApp py b))
                Lean.Meta.mkLambdaFVars #[a, b, hab] hb
          Lean.Meta.mkAppOptM ``forallType_heq
            #[some dx, some dy, some px, some py, some hd, some hp]
        else do
          let expand (t : Lean.Expr) : Lean.MetaM Lean.Expr := do
            if let .proj sn idx a := t then
              let some info := Lean.getStructureInfo? (← Lean.getEnv) sn
                | Lean.throwError "Unknown structure"
              Lean.Expr.mkDirectProjection a info.fieldNames[idx]!
            else Lean.Meta.withTransparency .default (Lean.Meta.whnf t)
          let x' ← expandHead (← expand x)
          let y' ← expandHead (← expand y)
          if x' != x || y' != y then go fuel x' y'
          else if ← Lean.Meta.isDefEq x y then Lean.Meta.mkHEqRefl x
          else Lean.throwError m!"Cannot prove structural congruence: {x} versus {y}"
        memo.modify (·.insert (x, y) h)
        return h
    let mut out := e.getAppFn
    let mut ty ← Lean.Meta.inferType out
    for arg in e.getAppArgs do
      ty ← Lean.Meta.whnf ty
      let dom := ty.bindingDomain!
      let actual ← Lean.Meta.inferType arg
      let arg ← if actual == dom then pure arg else do
        let h ← toEq (← go 500 actual dom)
        let casted ← Lean.Meta.mkAppM ``cast #[h, arg]
        let hc ← Lean.Meta.mkAppM ``cast_heq #[h, arg]
        memo.modify (·.insert (casted, arg) hc)
        let hc' ← Lean.Meta.mkAppM ``HEq.symm #[hc]
        memo.modify (·.insert (arg, casted) hc')
        pure casted
      out := Lean.mkApp out arg
      ty := ty.bindingBody!.instantiate1 arg
    let goal ← Lean.Elab.Tactic.getMainGoal
    let wanted ← goal.getType
    let actual ← Lean.Meta.inferType out
    let h ← toEq (← go 500 actual wanted)
    let solved ← Lean.Meta.mkAppM ``Eq.mp #[h, out]
    goal.assign solved
    Lean.Elab.Tactic.replaceMainGoal []

set_option maxHeartbeats 1000000 in
-- Transport along the actual reduction-tower evaluation isomorphism.
private theorem reductionModuleExchange_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' p' p g)
    (K : DerivedCategory (AdicCompletion.Modules l E X)) (n : ℕ)
    (h : IsIso ((moduleExchange l E sq).app
      ((AdicCompletion.derivedReduction l E X n ⋙ AdicCompletion.restrict l E X n).obj K))) :
    IsIso ((moduleExchange l E sq).app ((dev l E X n).obj ((red l E X).obj K))) := by
  obtain ⟨_, _, _, _, _, _, _, _, heval, _⟩ :=
    completeDerivedCompletion l E X X (𝟙 X)
  obtain ⟨ρ⟩ := heval n
  exact_structural ((@NatTrans.isIso_app_iff_of_iso _ _ _ _ _ _ (moduleExchange l E sq) _ _
    (@Iso.app _ _ _ _ _ _ ρ K)).mpr h)

set_option maxHeartbeats 1000000 in
-- Keep the finite reduction object out of the mate normalization.
private theorem towerExchangeEvaluation_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' p' p g)
    (n : ℕ) (M : DTow l E X)
    [IsIso ((moduleExchange l E sq).app ((dev l E X n).obj M))] :
    IsIso ((dev l E Y' n).map ((towerExchange l E sq).app M)) := by
  have hp := (directImage_limits l E p).1 n
  have hp' := (directImage_limits l E p').1 n
  unfold moduleExchange at *
  unfold pushEvaluationMap at hp hp'
  exact_structural (exchangeMate_map_isIso
    (towerAdjunction l E p) (towerAdjunction l E p')
    (moduleAdjunction l E p) (moduleAdjunction l E p')
    (towerPullSquare l E sq).hom (modulePullSquare l E sq).hom
    (pullEvaluation l E p n) (pullEvaluation l E p' n)
    (pullEvaluation l E g n) (pullEvaluation l E g' n) M
    (evaluationCube l E sq n ((rpush l E p).obj M)))




set_option maxHeartbeats 1000000 in
-- Assemble the concrete coefficient, reduction and evaluation comparisons.
/-- Each evaluated finite reduction exchange is invertible under the stated lower-bound and
classicality hypotheses.

The proof transports the reduction through the exact section-action equivalence and the normalized
finite-discrete coefficient encoding, obtains an étale-origin witness from the classical derived
comparison, applies finite proper base change, and identifies the resulting mate with the
specified evaluated tower exchange by coefficient-restriction and evaluation cubes and the
reduction-tower identification of `completeDerivedCompletion`. This is steps 1--9 and the
evaluation part of step 10 of the former plan of `det-pbc-complete-exchange-iso`, now the proof
of `det-pbc-complete-exchange-iso-finite-reduction`; no uniform lower bound in the level is
required.
Source: Stacks Project, Tags 09C8 and 0D6J; blueprint
`det-pbc-complete-exchange-iso-finite-reduction`.
(blueprint: det-pbc-complete-exchange-iso-finite-reduction).
-/
theorem finiteReductionExchange_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' p' p g) [IsProper p]
    (K : DerivedCategory (AdicCompletion.Modules l E X))
    (hK : ∀ n : ℕ,
      (∃ b : ℤ, ((AdicCompletion.derivedReduction l E X n).obj K).IsGE b) ∧
      ∀ q : ℤ, IsClassicalModuleSheaf
        ((InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology X)
          (AdicCompletion.finiteRing l E X n)).functor.obj
            ((DerivedCategory.homologyFunctor _ q).obj
              ((AdicCompletion.derivedReduction l E X n).obj K))))
    (n : ℕ) :
    IsIso ((dev l E Y' n).map
      ((towerExchange l E sq.toCommSq).app ((red l E X).obj K))) := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let : TopologicalSpace A := by
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    infer_instance
  let : IsTopologicalRing A := by
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    infer_instance
  let : DiscreteTopology A := DerivedNakayama.quotientDiscrete l E (n + 1)
  let Kn := (AdicCompletion.derivedReduction l E X n).obj K
  have hfinite := finiteInternalExact_isIso A sq Kn (hK n).1 (hK n).2
  have hintegral := restrictionExchange_isIso (DerivedNakayama.integerRing l E)
    (DerivedNakayama.quotientRing l E (n + 1))
    (DerivedNakayama.reductionRing l E (n + 1)) sq.toCommSq Kn
  rw [← moduleExchange_exact l E sq.toCommSq] at hintegral
  have hmodule : IsIso ((moduleExchange l E sq.toCommSq).app
      ((dev l E X n).obj ((red l E X).obj K))) := by
    exact_structural (reductionModuleExchange_isIso l E sq.toCommSq K n hintegral)
  exact towerExchangeEvaluation_isIso l E sq.toCommSq n ((red l E X).obj K)

end AlgebraicGeometry.ProEtale.CompleteDerivedCompletion
