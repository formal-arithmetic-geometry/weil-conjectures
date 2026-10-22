/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q16
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.SupportCohomology
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.BaseChange.Square
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Sheaf.AlgebraicGeometry.ProEtaleSupportedConstantPresentation

import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization
import Sheaf.Paper.LocalizeRingedSiteMorphismGeneral
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

/-!
# Canonically normalized closed constant exchange

Source: Stacks Project, Tags 03S6 and 095L; Milne, Lectures on Etale Cohomology,
Section 9, Theorem 9.4 (blueprint: lem-pur-supported-constant-exchange-normalization).
The Boolean parameter only selects the etale (`false`) or pro-etale (`true`) site.
All sheaves are ordinary fixed-scalar modules over the given constant ring.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.SupportedConstantNormalization

/-- The existing small site, selected without changing either universe.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
abbrev Site (pro : Bool) (X : Scheme.{u}) : Type (u + 1) :=
  match pro with
  | false => X.Etale
  | true => X.ProEt

/-- The category structure of the selected existing site.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
instance siteCategory (pro : Bool) (X : Scheme.{u}) : Category.{u} (Site pro X) :=
  match pro with
  | false => inferInstance
  | true => inferInstance

/-- The selected existing topology.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def topology (pro : Bool) (X : Scheme.{u}) : GrothendieckTopology (Site pro X) :=
  match pro with
  | false => X.smallEtaleTopology
  | true => Scheme.ProEt.topology X

/-- Ordinary module sheaves on the selected site, with the usual larger coefficients.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
abbrev Modules (A : Type (u + 1)) [CommRing A] (pro : Bool) (X : Scheme.{u}) :=
  Sheaf (topology pro X) (ModuleCat.{u + 1} A)

variable (A : Type (u + 1)) [CommRing A]

/-- Sheafification on either existing small site.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
instance sheafify (pro : Bool) (X : Scheme.{u}) :
    HasSheafify (topology pro X) (ModuleCat.{u + 1} A) :=
  match pro with
  | false => inferInstance
  | true => inferInstance

/-- The already defined constant sheaf of the coefficient module.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
abbrev constant (pro : Bool) (X : Scheme.{u}) : Modules A pro X :=
  (constantSheaf (topology pro X) (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)

/-- Inverse image along an arbitrary scheme morphism.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
abbrev pull (pro : Bool) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Modules A pro Y ⥤ Modules A pro X :=
  match pro with
  | false => Etale.upperStar (ModuleCat.{u + 1} A) f
  | true => ProEtale.upperStar (ModuleCat.{u + 1} A) f

/-- Direct image along an arbitrary scheme morphism.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
abbrev push (pro : Bool) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Modules A pro X ⥤ Modules A pro Y :=
  match pro with
  | false => Etale.lowerStar (ModuleCat.{u + 1} A) f
  | true => ProEtale.lowerStar (ModuleCat.{u + 1} A) f

/-- The actual inverse-image adjunction, on either site.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def adj (pro : Bool) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pull A pro f ⊣ push A pro f :=
  match pro with
  | false => Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  | true => ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f

/-- The existing scalar-preserving constant identification on either site.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def unitIso (pro : Bool) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pull A pro f).obj (constant A pro Y) ≅ constant A pro X :=
  match pro with
  | false => (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).app
      (ModuleCat.of A A)
  | true => (ProEtale.constantSheafCompUpperStarIso (ModuleCat.{u + 1} A) f).app
      (ModuleCat.of A A)

/-- The supported constant is the recorded closed direct image.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
abbrev supported (pro : Bool) {Z X : Scheme.{u}} (i : Z ⟶ X) :=
  (push A pro i).obj (constant A pro Z)

/-- Reuse constant restriction; the pro-etale arrow is the sheafified scalar map.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def restriction (pro : Bool) {Z X : Scheme.{u}} (i : Z ⟶ X) :
    constant A pro X ⟶ supported A pro i :=
  match pro with
  | false => (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).homEquiv _ _
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) i).app
        (ModuleCat.of A A)).hom
  | true => Scheme.proEtaleConstantDirectImageMap i (ModuleCat.{u + 1} A)
      (ModuleCat.of A A)

/-- The existing extension by zero along an open immersion.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
abbrev shriek (pro : Bool) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Modules A pro U ⥤ Modules A pro X :=
  match pro with
  | false => Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j
  | true => ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j

/-- The open adjunction with inverse image, in its recorded normalization.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def openAdj (pro : Bool) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    shriek A pro j ⊣ pull A pro j :=
  match pro with
  | false => Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j
  | true => ProEtale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j

/-- The actual open counit, with the canonical constant coefficient identification.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def epsilon (pro : Bool) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (shriek A pro j).obj (constant A pro U) ⟶ constant A pro X :=
  ((openAdj A pro j).homEquiv _ _).symm (unitIso A pro j).inv

/-- The specified pullback comparison; pro-etale uses its recorded coherent square.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def square (pro : Bool) {Z' Z X' X : Scheme.{u}}
    {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {h : X' ⟶ X}
    (sq : ChosenCartesianSquare g i' i h) :
    pull A pro h ⋙ pull A pro i' ≅ pull A pro i ⋙ pull A pro g :=
  match pro with
  | false => Etale.squareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq
  | true => ProEtale.supportSiteProEtaleComparisonSquare (ModuleCat.{u + 1} A) sq

/-- The canonical closed exchange, defined by its actual adjunction mate.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def exchange (pro : Bool) {Z' Z X' X : Scheme.{u}}
    {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {h : X' ⟶ X}
    (sq : ChosenCartesianSquare g i' i h) :
    (pull A pro h).obj (supported A pro i) ⟶ supported A pro i' :=
  match pro with
  | false => (Etale.baseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
      (constant A false Z) ≫ (Etale.lowerStar (ModuleCat.{u + 1} A) i').map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) g).app
          (ModuleCat.of A A)).hom
  | true => (adj A true i').homEquiv _ _
      ((square A true sq).hom.app (supported A true i) ≫
        (pull A true g).map ((adj A true i).counit.app (constant A true Z)) ≫
        (unitIso A true g).hom)

/-- The inverse of the open comparison, as the transpose of the localized unit.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def openBackward (pro : Bool) {U' U X' X : Scheme.{u}}
    {g : U' ⟶ U} {j' : U' ⟶ X'} {j : U ⟶ X} {h : X' ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : ChosenCartesianSquare g j' j h) :
    (shriek A pro j').obj (constant A pro U') ⟶
      (pull A pro h).obj ((shriek A pro j).obj (constant A pro U)) :=
  ((openAdj A pro j').homEquiv _ _).symm
    ((unitIso A pro g).inv ≫
      (pull A pro g).map ((openAdj A pro j).unit.app (constant A pro U)) ≫
      (square A pro sq).inv.app ((shriek A pro j).obj (constant A pro U)))

/-- The actual terminal object of the selected site.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def terminal (pro : Bool) (X : Scheme.{u}) : Site pro X :=
  match pro with
  | false => Scheme.Etale.mk (𝟙 X)
  | true => Scheme.ProEt.mk (𝟙 X)

/-- Restriction to the complementary open, using the published support arrow.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def supportArrow (pro : Bool) {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    Site pro X :=
  match pro with
  | false => Scheme.Etale.mk i.openComplement.ι
  | true => Scheme.ProEt.mk i.openComplement.ι

/-- The restriction arrow selecting the published support kernel.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def supportRestriction (pro : Bool) {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] : supportArrow pro i ⟶ terminal pro X :=
  match pro with
  | false => Etale.supportRestrictionArrow i
  | true => ProEtale.supportRestrictionArrow i

/-- The existing kernel of restriction, for all ordinary module sheaves.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
abbrev sections (pro : Bool) {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :=
  Sheaf.supportedSectionsFunctor (topology pro X) (ModuleCat.{u + 1} A)
    (supportRestriction pro i)

/-- The inverse-image unit on global sections, with the actual terminal base change.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def sigma (pro : Bool) {X' X : Scheme.{u}} (h : X' ⟶ X) (M : Modules A pro X) :
    M.obj.obj (op (terminal pro X)) ⟶
      ((pull A pro h).obj M).obj.obj (op (terminal pro X')) :=
  match pro with
  | false => ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).unit.app M).hom.app
      (op (Scheme.Etale.mk (𝟙 X))) ≫
      ((Etale.upperStar (ModuleCat.{u + 1} A) h).obj M).obj.map
        (MorphismProperty.Over.isoMk (P := @Etale) (Q := ⊤)
          (asIso (pullback.snd (𝟙 X) h)) (Category.comp_id _)).inv.op
  | true => ((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).unit.app M).hom.app
      (op (Scheme.ProEt.mk (𝟙 X))) ≫
      ((ProEtale.upperStar (ModuleCat.{u + 1} A) h).obj M).obj.map
        (ProEtale.overPullbackObjMkIdIso h).inv.op

/-- The etale-to-pro-etale inverse image, with the recorded adjunction.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
abbrev compare (X : Scheme.{u}) :=
  ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X

/-- The scalar-preserving constant-unit identification for site comparison.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
abbrev compareUnit (X : Scheme.{u}) := ProEtale.comparisonUpperStarUnitIso A X

/-- The recorded coherent comparison, with exactly the orientation in the node.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
abbrev comparePullback {X' X : Scheme.{u}} (h : X' ⟶ X) :=
  ProEtale.supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) h

/-- The closed site exchange is the adjunction mate of that coherent comparison.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def gamma {Z X : Scheme.{u}} (i : Z ⟶ X) :
    (compare A X).obj (supported A false i) ⟶ supported A true i :=
  (adj A true i).homEquiv _ _
    ((comparePullback A i).inv.app (supported A false i) ≫
      (compare A Z).map ((adj A false i).counit.app (constant A false Z)) ≫
      (compareUnit A Z).hom)

/-- The canonical comparison on the open constants, with inverse orientation.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def compareOpenBackward {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (shriek A true j).obj (constant A true U) ⟶
      (compare A X).obj ((shriek A false j).obj (constant A false U)) :=
  ((openAdj A true j).homEquiv _ _).symm
    ((compareUnit A U).inv ≫
      (compare A U).map ((openAdj A false j).unit.app (constant A false U)) ≫
      (comparePullback A j).hom.app ((shriek A false j).obj (constant A false U)))

/-- The site-comparison unit on global sections, before taking its support kernel.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def compareSigma (X : Scheme.{u}) (M : Modules A false X) :
    M.obj.obj (op (terminal false X)) ⟶
      ((compare A X).obj M).obj.obj (op (terminal true X)) :=
  ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X).unit.app M).hom.app
    (op (Scheme.Etale.mk (𝟙 X)))

/-- Restriction is the cokernel of the open constant counit in both topologies.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization).
Proof: Apply the exact inverse-image adjunctions and the constant-module inverse-image
lemma (step 1). The etale open/closed sequence and the pro-etale constant presentation
identify restriction as the cokernel of the open constant counit (step 2); no compactness
of the complement is used. Transpose the canonical open comparison: the triangle identity
identifies its composite with the pulled-back counit with the target counit (step 3).
Transpose the closed mate: naturality of the square comparison, the closed triangle
identity and scalar-preserving constant coherence give d L rho = rho' q (step 4).
The cokernel universal property constructs a two-sided inverse to d and proves uniqueness
by cancellation with L rho (step 5). -/
theorem presentation (P : WeilConjectures.PurityFiniteSetting.{u}) (pro : Bool)
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃ w : epsilon P.Coefficient pro i.openComplement.ι ≫
        restriction P.Coefficient pro i = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ (restriction P.Coefficient pro i) w)) := by
  sorry

/-- Exact pullback, the actual open counit comparison, and the canonical closed mate.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization).
Proof: Apply the exact inverse-image adjunctions and the constant-module inverse-image
lemma (step 1). The etale open/closed sequence and the pro-etale constant presentation
identify restriction as the cokernel of the open constant counit (step 2); no compactness
of the complement is used. Transpose the canonical open comparison: the triangle identity
identifies its composite with the pulled-back counit with the target counit (step 3).
Transpose the closed mate: naturality of the square comparison, the closed triangle
identity and scalar-preserving constant coherence give d L rho = rho' q (step 4).
The cokernel universal property constructs a two-sided inverse to d and proves uniqueness
by cancellation with L rho (step 5). -/
theorem scheme_normalization (P : WeilConjectures.PurityFiniteSetting.{u}) (pro : Bool)
    {Z' Z X' X : Scheme.{u}} {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {h : X' ⟶ X}
    [IsClosedImmersion i] [IsClosedImmersion i']
    (sq : ChosenCartesianSquare g i' i h) :
    PreservesFiniteLimits (pull P.Coefficient pro h) ∧
    PreservesFiniteColimits (pull P.Coefficient pro h) ∧
    (∀ (gU : i'.openComplement.toScheme ⟶ i.openComplement.toScheme)
      (sqU : ChosenCartesianSquare gU i'.openComplement.ι i.openComplement.ι h),
      IsIso (openBackward P.Coefficient pro sqU) ∧
      openBackward P.Coefficient pro sqU ≫
          (pull P.Coefficient pro h).map (epsilon P.Coefficient pro i.openComplement.ι) ≫
            (unitIso P.Coefficient pro h).hom =
        epsilon P.Coefficient pro i'.openComplement.ι) ∧
    IsIso (exchange P.Coefficient pro sq) ∧
    (pull P.Coefficient pro h).map (restriction P.Coefficient pro i) ≫
        exchange P.Coefficient pro sq =
      (unitIso P.Coefficient pro h).hom ≫ restriction P.Coefficient pro i' ∧
    (∀ d : (pull P.Coefficient pro h).obj (supported P.Coefficient pro i) ⟶
        supported P.Coefficient pro i',
      (pull P.Coefficient pro h).map (restriction P.Coefficient pro i) ≫ d =
        (unitIso P.Coefficient pro h).hom ≫ restriction P.Coefficient pro i' →
      d = exchange P.Coefficient pro sq) := by
  sorry

/-- The same normalization for the prescribed site-comparison mate.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization).
Proof: Apply the exact inverse-image adjunctions and the constant-module inverse-image
lemma (step 1). The etale open/closed sequence and the pro-etale constant presentation
identify restriction as the cokernel of the open constant counit (step 2); no compactness
of the complement is used. Transpose the canonical open comparison: the triangle identity
identifies its composite with the pulled-back counit with the target counit (step 3).
Transpose the closed mate: naturality of the square comparison, the closed triangle
identity and scalar-preserving constant coherence give d L rho = rho' q (step 4).
The cokernel universal property constructs a two-sided inverse to d and proves uniqueness
by cancellation with L rho (step 5). -/
theorem site_normalization (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    PreservesFiniteLimits (compare P.Coefficient X) ∧
    PreservesFiniteColimits (compare P.Coefficient X) ∧
    IsIso (compareOpenBackward P.Coefficient i.openComplement.ι) ∧
    compareOpenBackward P.Coefficient i.openComplement.ι ≫
        (compare P.Coefficient X).map (epsilon P.Coefficient false i.openComplement.ι) ≫
          (compareUnit P.Coefficient X).hom = epsilon P.Coefficient true i.openComplement.ι ∧
    IsIso (gamma P.Coefficient i) ∧
    (compare P.Coefficient X).map (restriction P.Coefficient false i) ≫
        gamma P.Coefficient i =
      (compareUnit P.Coefficient X).hom ≫ restriction P.Coefficient true i ∧
    (∀ d : (compare P.Coefficient X).obj (supported P.Coefficient false i) ⟶
        supported P.Coefficient true i,
      (compare P.Coefficient X).map (restriction P.Coefficient false i) ≫ d =
        (compareUnit P.Coefficient X).hom ≫ restriction P.Coefficient true i →
      d = gamma P.Coefficient i) := by
  sorry

/-- Normalization of the supported-section transformation by its kernel inclusion.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def SectionCondition (pro : Bool) {Z' Z X' X : Scheme.{u}}
    {i : Z ⟶ X} {i' : Z' ⟶ X'} [IsClosedImmersion i] [IsClosedImmersion i']
    (h : X' ⟶ X)
    (l : sections A pro i ⟶ pull A pro h ⋙ sections A pro i') : Prop :=
  ∀ M : Modules A pro X,
    l.app M ≫ kernel.ι (((pull A pro h).obj M).obj.map (supportRestriction pro i').op) =
      kernel.ι (M.obj.map (supportRestriction pro i).op) ≫ sigma A pro h M

/-- The supported inverse-image section transformation exists and is uniquely normalized.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization).
Proof: Evaluate the inverse-image unit at the terminal object. The localized direct-image
identity of Stacks 04J0 makes its restrictions on X and U commute (node step 7).
Consequently it sends the kernel of restriction into the target kernel. Apply the kernel
universal property on each module sheaf. Naturality follows from naturality of the unit;
uniqueness follows from the monic kernel inclusion. This works for every module sheaf,
without a compactness or finiteness assumption. -/
theorem sectionMap_existsUnique (P : WeilConjectures.PurityFiniteSetting.{u}) (pro : Bool)
    {Z' Z X' X : Scheme.{u}} {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {h : X' ⟶ X}
    [IsClosedImmersion i] [IsClosedImmersion i']
    (_sq : ChosenCartesianSquare g i' i h) :
    ∃! l : sections P.Coefficient pro i ⟶
        pull P.Coefficient pro h ⋙ sections P.Coefficient pro i',
      SectionCondition P.Coefficient pro h l := by
  sorry

/-- The canonical kernel restriction of the inverse-image unit, determined uniquely.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def sectionMap (P : WeilConjectures.PurityFiniteSetting.{u}) (pro : Bool)
    {Z' Z X' X : Scheme.{u}} {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {h : X' ⟶ X}
    [IsClosedImmersion i] [IsClosedImmersion i']
    (sq : ChosenCartesianSquare g i' i h) :
    sections P.Coefficient pro i ⟶
      pull P.Coefficient pro h ⋙ sections P.Coefficient pro i' :=
  (sectionMap_existsUnique P pro sq).choose

/-- Normalization of the site-comparison section transformation.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def CompareSectionCondition {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (l : sections A false i ⟶ compare A X ⋙ sections A true i) : Prop :=
  ∀ M : Modules A false X,
    l.app M ≫ kernel.ι (((compare A X).obj M).obj.map (supportRestriction true i).op) =
      kernel.ι (M.obj.map (supportRestriction false i).op) ≫ compareSigma A X M

/-- The uniquely normalized supported-section map for the site comparison.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization).
Proof: Evaluate the inverse-image unit at the terminal object. The localized direct-image
identity of Stacks 04J0 makes its restrictions on X and U commute (node step 7).
Consequently it sends the kernel of restriction into the target kernel. Apply the kernel
universal property on each module sheaf. Naturality follows from naturality of the unit;
uniqueness follows from the monic kernel inclusion. This works for every module sheaf,
without a compactness or finiteness assumption. -/
theorem compareSectionMap_existsUnique (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    ∃! l : sections P.Coefficient false i ⟶
        compare P.Coefficient X ⋙ sections P.Coefficient true i,
      CompareSectionCondition P.Coefficient i l := by
  sorry

/-- The canonical site-comparison map on kernels of restriction, for every module.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def compareSectionMap (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    sections P.Coefficient false i ⟶
      compare P.Coefficient X ⋙ sections P.Coefficient true i :=
  (compareSectionMap_existsUnique P i).choose

/-- Both canonical underived comparison squares commute, with the prescribed k.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization).
Proof: Precompose the two closed-exchange composites with the twice-pulled-back
constant restriction (node step 6). The closed normalization identifies them with the
two scalar-preserving constant units. Coherence of the recorded comparison makes those
equal. Exactness preserves the cokernel, hence its epimorphism can be cancelled.
For sections, use the composite adjunctions (step 8). Their right adjoints identify
sectionwise on each etale object with evaluation on its base change. The recorded
comparison is their conjugate, so the conjugate-isomorphism unit equation makes the
two composite section maps agree after applying k. Step 7 restricts this equality to
support kernels, and their monic inclusions give the displayed equation for all M.
This argument uses neither quasi-compactness of the open complement nor finiteness
of h or X'. -/
theorem comparison_square (P : WeilConjectures.PurityFiniteSetting.{u})
    {Z' Z X' X : Scheme.{u}} {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {h : X' ⟶ X}
    [IsClosedImmersion i] [IsClosedImmersion i']
    (sq : ChosenCartesianSquare g i' i h) :
    ((compare P.Coefficient X').map (exchange P.Coefficient false sq) ≫
        gamma P.Coefficient i' =
      (comparePullback P.Coefficient h).hom.app (supported P.Coefficient false i) ≫
        (pull P.Coefficient true h).map (gamma P.Coefficient i) ≫
          exchange P.Coefficient true sq) ∧
    (∀ M : Modules P.Coefficient false X,
      (sectionMap P false sq).app M ≫
          (compareSectionMap P i').app ((pull P.Coefficient false h).obj M) ≫
            (sections P.Coefficient true i').map
              ((comparePullback P.Coefficient h).hom.app M) =
        (compareSectionMap P i).app M ≫
          (sectionMap P true sq).app ((compare P.Coefficient X).obj M)) := by
  sorry

end AlgebraicGeometry.SupportedConstantNormalization
