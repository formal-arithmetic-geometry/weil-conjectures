/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q108
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.SupportCohomology
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.Paper.SupportedCohomologyHom
public import Sheaf.AlgebraicGeometry.ClosedSupportHom
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.Yoneda
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Sheaf.AlgebraicGeometry.SupportLongExact
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import WeilConjectures.SixFunctors.ProEtale.Comparison

import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.Paper.ComparisonPullbackExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
import Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
import WeilConjectures.SixFunctors.BaseChange.Square
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Sheaf.CategoryTheory.Abelian.RHomDerivedRoof
import WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution
import Sheaf.Algebra.Homology.KInjectiveComparisonPrinciple
import Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange
import Sheaf.AlgebraicGeometry.ProEtaleSupportedConstantPresentation

/-!
# Supported Hom and pullback of closed pairs

Source: Milne, Lectures on Etale Cohomology, Section 9, Theorem 9.4 and Example 9.5,
pp. 66--67; the kernel-of-restriction construction and its pullback functoriality
(blueprint: lem-pur-supported-hom-pullback).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex.HomComplex

namespace AlgebraicGeometry

/-- Site data used to spell out the same normalized identification in both topologies.
The site, restriction arrow, supported constant, and its actual restriction map are data,
not a replacement definition of supported sections.
Source: Milne, Section 9, Ext proof (blueprint: lem-pur-supported-hom-pullback). -/
structure SupportHomPair (A : Type (u + 1)) [CommRing A] where
  Site : Type (u + 1)
  [category : Category.{u} Site]
  topology : GrothendieckTopology Site
  [sheafify : HasSheafify topology (ModuleCat.{u + 1} A)]
  [grothendieck : IsGrothendieckAbelian.{u + 1}
    (Sheaf topology (ModuleCat.{u + 1} A))]
  terminal : Site
  isTerminal : IsTerminal terminal
  complement : Site
  restriction : complement ⟶ terminal
  supported : Sheaf topology (ModuleCat.{u + 1} A)
  constantRestriction :
    (constantSheaf topology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶ supported

attribute [instance] SupportHomPair.category SupportHomPair.sheafify SupportHomPair.grothendieck

namespace SupportHomPair

variable {A : Type (u + 1)} [CommRing A] (S : SupportHomPair A)

/-- The already defined support kernel in the given pair.
Source: Milne, Section 9 (blueprint: lem-pur-supported-hom-pullback). -/
abbrev sections :=
  Sheaf.supportedSectionsFunctor S.topology (ModuleCat.{u + 1} A) S.restriction

/-- The degree-a cohomology of the published bounded-below right derived support functor.
Source: Milne, Theorem 9.4 (blueprint: lem-pur-supported-hom-pullback). -/
abbrev group (K : DerivedCategory.Plus (Sheaf S.topology (ModuleCat.{u + 1} A))) (a : ℤ) :=
  (S.sections.rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) a).obj K

/-- Termwise support on an injective representative, using the existing kernel functor.
Source: Milne, Ext proof (blueprint: lem-pur-supported-hom-pullback). -/
abbrev complex (I : CochainComplex.Plus (Sheaf S.topology (ModuleCat.{u + 1} A))) :=
  (S.sections.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj

/-- Image of a supported cocycle under the canonical right-derived-unit comparison.
Source: Milne, Ext proof (blueprint: lem-pur-supported-hom-pullback). -/
def cycleClass (I : CochainComplex.Plus (Sheaf S.topology (ModuleCat.{u + 1} A)))
    [∀ n : ℤ, Injective (I.obj.X n)] (a : ℤ) (x : (S.complex I).cycles a) :
    S.group (DerivedCategory.Plus.Q.obj I) a :=
  (Sheaf.supportSequenceModelIso S.topology (ModuleCat.{u + 1} A) S.sections I
    (DerivedCategory.Plus.Q.obj I) (Iso.refl _) a).hom ((S.complex I).homologyπ a x)

/-- The localized map defined by a Hom cocycle, with the canonical cochain shift.
Source: Stacks 06XR, 070I; Milne, Ext proof
(blueprint: lem-pur-supported-hom-pullback). -/
def cocycleMorphism
    (I : CochainComplex.Plus (Sheaf S.topology (ModuleCat.{u + 1} A))) (a : ℤ)
    (f : S.supported ⟶ I.obj.X a) (hf : f ≫ I.obj.d a (a + 1) = 0) :
    (DerivedCategory.singleFunctor (Sheaf S.topology (ModuleCat.{u + 1} A)) 0).obj
      S.supported ⟶ (DerivedCategory.Plus.Q.obj I).obj⟦a⟧ :=
  ShiftedHom.map (Cocycle.equivHomShift.symm
      (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf)) DerivedCategory.Q ≫
    ((DerivedCategory.quotientCompQhIso _).hom.app I.obj)⟦a⟧'

/-- The normalized supported-Hom identification. The cocycle clause fixes its value by
`f ↦ (f ρ)(1)` on every injective representative, so no arbitrary natural isomorphism
can satisfy this interface. Its source is the actual derived support group.
Source: Milne, Theorem 9.4, Example 9.5 and Ext proof
(blueprint: lem-pur-supported-hom-pullback). -/
structure Identification where
  chi : ∀ (K : DerivedCategory.Plus (Sheaf S.topology (ModuleCat.{u + 1} A))) (a : ℤ),
    S.group K a ≃+
      ((DerivedCategory.singleFunctor (Sheaf S.topology (ModuleCat.{u + 1} A)) 0).obj
        S.supported ⟶ K.obj⟦a⟧)
  naturality : ∀ (K L : DerivedCategory.Plus (Sheaf S.topology (ModuleCat.{u + 1} A)))
      (b : K ⟶ L) (a : ℤ) (x : S.group K a),
    chi L a ((S.sections.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) a).map b x) =
        chi K a x ≫ (DerivedCategory.Plus.ι.map b)⟦a⟧'
  normalization : ∀ (I : CochainComplex.Plus (Sheaf S.topology (ModuleCat.{u + 1} A)))
      [∀ n : ℤ, Injective (I.obj.X n)] (a : ℤ)
      (f : S.supported ⟶ I.obj.X a) (hf : f ≫ I.obj.d a (a + 1) = 0)
      (x : (S.complex I).cycles a),
    kernel.ι ((I.obj.X a).obj.map S.restriction.op) ((S.complex I).iCycles a x) =
      ((constantSheafAdj S.topology (ModuleCat.{u + 1} A) S.isTerminal).homEquiv _ _
        (S.constantRestriction ≫ f)) 1 →
      chi (DerivedCategory.Plus.Q.obj I) a (S.cycleClass I a x) =
        S.cocycleMorphism I a f hf

end SupportHomPair

end AlgebraicGeometry

namespace AlgebraicGeometry

/-- Constant restriction along a continuous site functor: sheafify the constant
presheaf unit and then restrict it. This sends each scalar to that same constant scalar.
Source: Milne, Example 9.5 (blueprint: lem-pur-supported-hom-pullback). -/
def supportHomConstantDirectImage {A : Type (u + 1)} [CommRing A]
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (J' : GrothendieckTopology D)
    [HasSheafify J (ModuleCat.{u + 1} A)] [HasSheafify J' (ModuleCat.{u + 1} A)]
    (B : C ⥤ D) [B.IsContinuous J J'] :
    (constantSheaf J (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A) ⟶
      (B.sheafPushforwardContinuous (ModuleCat.{u + 1} A) J J').obj
        ((constantSheaf J' (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)) :=
  ((sheafificationAdjunction J (ModuleCat.{u + 1} A)).homEquiv _ _).symm
    (Functor.whiskerLeft B.op
      (toSheafify J' ((Functor.const Dᵒᵖ).obj (ModuleCat.of A A))))

namespace SupportHomPair

variable {A : Type (u + 1)} [CommRing A] (S T : SupportHomPair A)
variable (B : S.Site ⥤ T.Site) [hB : B.IsContinuous S.topology T.topology]
variable (L : Sheaf S.topology (ModuleCat.{u + 1} A) ⥤
  Sheaf T.topology (ModuleCat.{u + 1} A))
variable (adj : L ⊣ B.sheafPushforwardContinuous (ModuleCat.{u + 1} A) S.topology T.topology)

/-- The three canonical comparisons used in the statement, in one interface.
`constantIso` is fixed by its adjoint constant sections, `closedIso` by the epic
constant restriction, and `supportUnit` by its kernel inclusion. The terminal and open
arrows are actual site arrows, so the last formula is the unit-induced section map.
Source: Milne, Theorem 9.4, Ext proof and kernel construction
(blueprint: lem-pur-supported-hom-pullback). -/
structure Transport where
  terminalMap : T.terminal ⟶ B.obj S.terminal
  complementMap : T.complement ⟶ B.obj S.complement
  restriction_square : complementMap ≫ B.map S.restriction = T.restriction ≫ terminalMap
  constantIso :
    L.obj ((constantSheaf S.topology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)) ≅
      (constantSheaf T.topology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)
  constantIso_spec : adj.homEquiv _ _ constantIso.hom =
    supportHomConstantDirectImage S.topology T.topology B
  closedIso : L.obj S.supported ≅ T.supported
  closedIso_spec : L.map S.constantRestriction ≫ closedIso.hom =
    constantIso.hom ≫ T.constantRestriction
  supportUnit : S.sections ⟶ L ⋙ T.sections
  supportUnit_spec : ∀ F : Sheaf S.topology (ModuleCat.{u + 1} A),
    supportUnit.app F ≫ kernel.ι ((L.obj F).obj.map T.restriction.op) =
      kernel.ι (F.obj.map S.restriction.op) ≫
        (adj.unit.app F).hom.app (op S.terminal) ≫ (L.obj F).obj.map terminalMap.op

variable {S T B L adj}

variable [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]

/-- The actual derived kernel pullback, through the existing right-derived base-change
construction; it does not assume inverse image preserves injectives.
Source: Milne, Theorem 9.4 (blueprint: lem-pur-supported-hom-pullback). -/
def Transport.derivedMap (e : Transport S T B L adj) :
    S.sections.rightDerivedFunctorPlus ⟶
      L.mapDerivedCategoryPlus ⋙ T.sections.rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _
      (Functor.mapDerivedCategoryPlusIdIso (ModuleCat.{u + 1} A))).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange
      (G := S.sections) (G' := T.sections) (β := L) (γ := 𝟭 (ModuleCat.{u + 1} A))
      ((Functor.rightUnitor _).hom ≫ e.supportUnit)

/-- Pull a derived Hom back and precompose with closed exchange inverse, with the
published single-object and shift comparisons.
Source: Milne, Ext proof (blueprint: lem-pur-supported-hom-pullback). -/
def Transport.homMap (e : Transport S T B L adj)
    (K : DerivedCategory.Plus (Sheaf S.topology (ModuleCat.{u + 1} A))) (a : ℤ)
    (f : (DerivedCategory.singleFunctor (Sheaf S.topology (ModuleCat.{u + 1} A)) 0).obj
      S.supported ⟶ K.obj⟦a⟧) :
    (DerivedCategory.singleFunctor (Sheaf T.topology (ModuleCat.{u + 1} A)) 0).obj
      T.supported ⟶ (L.mapDerivedCategoryPlus.obj K).obj⟦a⟧ :=
  (DerivedCategory.singleFunctor (Sheaf T.topology (ModuleCat.{u + 1} A)) 0).map
      e.closedIso.inv ≫
    (L.mapDerivedCategorySingleFunctor 0).inv.app S.supported ≫
    L.mapDerivedCategory.map f ≫ (L.mapDerivedCategory.commShiftIso a).hom.app K.obj

/-- The displayed equality for every supported class in the indicated coefficient object.
Source: Milne, Theorem 9.4 and Example 9.5
(blueprint: lem-pur-supported-hom-pullback). -/
def Transport.Compatible (e : Transport S T B L adj)
    (chi : S.Identification) (chi' : T.Identification)
    (K : DerivedCategory.Plus (Sheaf S.topology (ModuleCat.{u + 1} A))) (a : ℤ) : Prop :=
  ∀ x : S.group K a,
    chi'.chi (L.mapDerivedCategoryPlus.obj K) a
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) a).map
          ((e.derivedMap).app K) x) =
      e.homMap K a (chi.chi K a x)

end SupportHomPair

/-- The etale pair uses the recorded scheme site, open complement, underived direct
image and constant sheaf. Source: Milne, Section 9
(blueprint: lem-pur-supported-hom-pullback). -/
abbrev etaleSupportHomPair (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    SupportHomPair P.Coefficient where
  Site := X.Etale
  topology := X.smallEtaleTopology
  terminal := Scheme.Etale.mk (𝟙 X)
  isTerminal := MorphismProperty.Over.mkIdTerminal _ _
  complement := Scheme.Etale.mk i.openComplement.ι
  restriction := Etale.supportRestrictionArrow i
  supported := (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constantEtale Z)
  constantRestriction := by
    letI : (MorphismProperty.Over.pullback @Etale ⊤ i).IsContinuous
        X.smallEtaleTopology Z.smallEtaleTopology := Etale.isContinuous_overPullback i
    exact supportHomConstantDirectImage X.smallEtaleTopology Z.smallEtaleTopology
      (MorphismProperty.Over.pullback @Etale ⊤ i)

/-- The identical kernel construction in the pro-etale topology, with its ordinary
constant module. Source: Milne, Section 9 and the pro-etale supported-Hom node
(blueprint: lem-pur-supported-hom-pullback). -/
abbrev proEtaleSupportHomPair (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    SupportHomPair P.Coefficient where
  Site := X.ProEt
  topology := Scheme.ProEt.topology X
  terminal := Scheme.ProEt.mk (𝟙 X)
  isTerminal := MorphismProperty.Over.mkIdTerminal _ _
  complement := Scheme.ProEt.mk i.openComplement.ι
  restriction := ProEtale.supportRestrictionArrow i
  supported := (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z)
  constantRestriction := by
    letI := Scheme.ProEt.isContinuous_overPullback i
    exact supportHomConstantDirectImage (Scheme.ProEt.topology X)
      (Scheme.ProEt.topology Z) (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i) ≫
        (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).map
          (ProEtale.comparisonUpperStarUnitIso P.Coefficient Z).inv

end AlgebraicGeometry

namespace AlgebraicGeometry

/-- Etale inverse image and its actual adjunction in the normalized transport interface.
Source: Milne, Section 9 (blueprint: lem-pur-supported-hom-pullback). -/
abbrev etaleSupportHomTransport (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ X') [IsClosedImmersion i'] (h : X' ⟶ X) : Type (u + 2) := by
  letI : (MorphismProperty.Over.pullback @Etale ⊤ h).IsContinuous
      (etaleSupportHomPair P i).topology (etaleSupportHomPair P i').topology :=
    Etale.isContinuous_overPullback h
  exact SupportHomPair.Transport (etaleSupportHomPair P i) (etaleSupportHomPair P i')
    (MorphismProperty.Over.pullback @Etale ⊤ h)
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) h)
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) h)

/-- Pro-etale inverse image and its actual adjunction, on the original small sites.
Source: Milne, Section 9; pro-etale constant presentation
(blueprint: lem-pur-supported-hom-pullback). -/
abbrev proEtaleSupportHomTransport (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ X') [IsClosedImmersion i'] (h : X' ⟶ X) : Type (u + 2) := by
  letI : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ h).IsContinuous
      (proEtaleSupportHomPair P i).topology (proEtaleSupportHomPair P i').topology :=
    Scheme.ProEt.isContinuous_overPullback h
  exact SupportHomPair.Transport (proEtaleSupportHomPair P i) (proEtaleSupportHomPair P i')
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ h)
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) h)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) h)

/-- The comparison inverse image and its actual adjunction in the same interface.
Source: Milne, Section 9; Stacks 099R
(blueprint: lem-pur-supported-hom-pullback). -/
abbrev siteSupportHomTransport (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] : Type (u + 2) := by
  letI : (Scheme.toProEt X).IsContinuous
      (etaleSupportHomPair P i).topology (proEtaleSupportHomPair P i).topology :=
    Scheme.isContinuous_toProEt X
  exact SupportHomPair.Transport (etaleSupportHomPair P i) (proEtaleSupportHomPair P i)
    (Scheme.toProEt X)
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X)
    (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} P.Coefficient) X)

/-- The published comparison of the two composite pullbacks, restricted canonically to D+.
Source: blueprint comparison-pullback coherence; Stacks 099R
(blueprint: lem-pur-supported-hom-pullback). -/
def supportHomDerivedComparison (P : WeilConjectures.PurityFiniteSetting.{u})
    {X' X : Scheme.{u}} (h : X' ⟶ X) :
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) h).mapDerivedCategoryPlus ⋙
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X').mapDerivedCategoryPlus ≅
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategoryPlus ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) h).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) h)
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X')).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (F := Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) h ⋙
        ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X')
      (G := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) h)
      (ProEtale.supportSiteComparisonCoefficientPullbackIso
        (ModuleCat.{u + 1} P.Coefficient) h) ≪≫
    Functor.mapDerivedCategoryPlusCompIso
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X)
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) h)

/-- Site comparison commutes with supported pullback and with the supported-constant
exchange. The first equation is in the actual derived support objects; the second uses
exactly the published inverse-image comparison, evaluated on the supported constant.
Source: Milne, Ext proof; blueprint affine-line orientation, etale-origin transport
(blueprint: lem-pur-supported-hom-pullback). -/
def SupportHomSquareCoherent (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (i' : Z' ⟶ X') [IsClosedImmersion i'] (h : X' ⟶ X)
    (e : etaleSupportHomTransport P i i' h) (p : proEtaleSupportHomTransport P i i' h)
    (v : siteSupportHomTransport P i) (v' : siteSupportHomTransport P i') : Prop :=
  (∀ K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)),
    (v.derivedMap (hB := Scheme.isContinuous_toProEt X)).app K ≫
      (p.derivedMap (hB := Scheme.ProEt.isContinuous_overPullback h)).app
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategoryPlus.obj K) =
      (e.derivedMap (hB := Etale.isContinuous_overPullback h)).app K ≫
        (v'.derivedMap (hB := Scheme.isContinuous_toProEt X')).app
          ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) h).mapDerivedCategoryPlus.obj K) ≫
        (proEtaleSupportHomPair P i').sections.rightDerivedFunctorPlus.map
          ((supportHomDerivedComparison P h).hom.app K)) ∧
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X').map
      (e.closedIso (hB := Etale.isContinuous_overPullback h)).hom ≫
      (v'.closedIso (hB := Scheme.isContinuous_toProEt X')).hom =
    (ProEtale.supportSiteComparisonCoefficientPullbackIso
      (ModuleCat.{u + 1} P.Coefficient) h).hom.app (etaleSupportHomPair P i).supported ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) h).map
          (v.closedIso (hB := Scheme.isContinuous_toProEt X)).hom ≫
          (p.closedIso (hB := Scheme.ProEt.isContinuous_overPullback h)).hom

/-- The canonical supported-Hom identifications commute with arbitrary pullback of a
closed pair in the etale topology and, for etale-origin coefficients, in the pro-etale
 topology. They also commute with comparison on both schemes, and the comparison
squares for supported groups and closed constants commute. Each identification is
normalized on every supported cocycle; each transport is fixed by the inverse-image
unit and the epic constant restriction. Thus the existential data introduce the
canonical maps, rather than allowing any choice of maps or identifications.

Source: Milne, Lectures on Etale Cohomology, Section 9, Theorem 9.4 and Example 9.5,
pp. 66--67, Ext proof; blueprint affine-line orientation, etale-origin transport
(blueprint: lem-pur-supported-hom-pullback).

Proof plan, following all nine node steps:
1. Use exact inverse image for h on the two sites and for nu. Termwise application
   gives the derived functors and their canonical shift comparisons.
2. The etale open-closed constant sequence and the pro-etale constant presentation
   express the supported constant as the cokernel of the open constant counit. No
   quasi-compactness of the open complement is used.
3. Open extension-by-zero base change, respectively site comparison, identifies the
   pulled-back counit with the target counit. Cokernel uniqueness gives closedIso,
   normalized by closedIso_spec; its adjoint sends 1 to 1, so it is closed exchange.
4. Evaluation of f after constant restriction at 1 identifies Hom from the supported
   constant with the restriction kernel. The inverse is the sectionwise scalar action.
5. The inverse-image unit sends 1 to 1 and commutes with restriction. Consequently
   evaluation intertwines pullback/precomposition with precisely supportUnit_spec.
6. Small-site module sheaves are Grothendieck and have enough injectives. Derive the
   evaluation isomorphism by the bounded-below right-derived universal property, then
   use lem-sc-p1-rhom-hom-derived-roof. This gives Identification with its normalization;
   in the two topologies it is lem-amb-closed-support-hom and lem-pur-supported-hom.
7. Choose bounded-below injective representatives and a comparison LI to J extending
   the coefficient map up to homotopy (lem-sp-kinjective-comparison-principle). Applying
   step 5 termwise identifies the induced supported map with f mapped to t Lf d-inverse.
   The right-derived universal property identifies the former with derivedMap, hence
   with the localization-sequence pullback; L need not preserve injectives.
8. The cocycle roof formula cancels the two resolution isomorphisms and gives Compatible
   for all integer degrees. Homotopies and boundaries give the same derived morphism.
9. Use lem-weil-pbc-comparison-pullback for the canonical comparison of composite inverse
   images. The two constant maps agree after the twice-pulled-back epic restriction,
   since both send 1 to 1. Section maps agree by composition of inverse-image units.
   Right-derived uniqueness gives SupportHomSquareCoherent, transporting the etale
   equality to the pro-etale one. No finiteness of h or X', and no purity, is used. -/
theorem supportedHom_pullback (P : WeilConjectures.PurityFiniteSetting.{u}) :
    ∃ chiE : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i],
        (etaleSupportHomPair P i).Identification,
    ∃ chiP : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i],
        (proEtaleSupportHomPair P i).Identification,
    ∀ {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      (i' : Z' ⟶ X') [IsClosedImmersion i'] (h : X' ⟶ X) (g : Z' ⟶ Z)
      (_sq : ChosenCartesianSquare g i' i h),
    ∃ e : etaleSupportHomTransport P i i' h,
    ∃ p : proEtaleSupportHomTransport P i i' h,
    ∃ v : siteSupportHomTransport P i,
    ∃ v' : siteSupportHomTransport P i',
      SupportHomSquareCoherent P i i' h e p v v' ∧
      ∀ (F : DerivedCategory.Plus
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))) (a : ℤ),
        e.Compatible (hB := Etale.isContinuous_overPullback h) (chiE i) (chiE i') F a ∧
        p.Compatible (hB := Scheme.ProEt.isContinuous_overPullback h) (chiP i) (chiP i')
          ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategoryPlus.obj F) a ∧
        v.Compatible (hB := Scheme.isContinuous_toProEt X) (chiE i) (chiP i) F a ∧
        v'.Compatible (hB := Scheme.isContinuous_toProEt X') (chiE i') (chiP i')
          ((Etale.upperStar
            (ModuleCat.{u + 1} P.Coefficient) h).mapDerivedCategoryPlus.obj F) a := by
  sorry

end AlgebraicGeometry
