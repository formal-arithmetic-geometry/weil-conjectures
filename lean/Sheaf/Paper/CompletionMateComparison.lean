/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Sheaf.CategoryTheory.DiagramSiteRealization
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Limits
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit
public import Sheaf.Paper.RingedExchangeTensorCoherence
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SiteDerivedTensorDescent
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import Sheaf.CategoryTheory.RingedToposMorphism
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.Paper.ProjectionFormulaArrows
import Sheaf.Paper.ProjectionFormulaTotalization
import Sheaf.Paper.ProjectionMateExact
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.Paper.QuotientTowerEvaluationComplex
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import Sheaf.Paper.CompletedPullbackAdjunction
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Sheaf.Paper.LocalHomTowerCriterion
import Sheaf.CategoryTheory.RingedSiteCompleteElementsIdeal
import Sheaf.CategoryTheory.RingedKoszulCompletionReflector
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction

/-!
# Strict quotient towers and the completed-adjunction mate

Source: smooth-purity blueprint, `fix-lem-exchanges`, Proof Step 4;
Stacks Project, Tags 099M, 099N, 0E48 and 0941
(blueprint: lem-sp-completion-mate-comparison).

## Main definitions and statements

- `towerExchange`: the strict quotient-tower adjunction mate.
- `completeExchange`: the independently defined completed-adjunction mate.
- `projectionComparison`, `comparisonS`, `comparisonT`: the prescribed comparison maps.
- `completionMateComparison`: their natural equality and finite-coefficient formulas.

The auxiliary declarations specify the canonical maps appearing in the statement.
Reduction is a functor to the derived category of strict towers, never a family
of unrelated derived level objects. Every choice below is fixed by a universal
property or a unique representative formula.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.AdicSites

/-- A small site, with its given topology.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
structure Site where
  objects : Type u
  [category : SmallCategory objects]
  topology : GrothendieckTopology objects

attribute [instance] Site.category

/-- The constant coefficient ring sheaf.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.ring (T : Site.{u}) (A : Type u) [CommRing A] :=
  ConstantCompletion.constant T.topology A

/-- Module sheaves over the constant coefficient ring, with Mathlib's category.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.modules (T : Site.{u}) (A : Type u) [CommRing A] :=
  ConstantCompletion.Mod (T.ring A)

/-- Unbounded derived module sheaves, using the standard localization universe.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.derived (T : Site.{u}) (A : Type u) [CommRing A] :=
  ConstantCompletion.D (T.ring A)

/-- Strict inverse sequences, indexed by n for the positive exponent n+1.
Source: Stacks 0941, 099M (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.towers (T : Site.{u}) (A : Type u) [CommRing A] :=
  ℕᵒᵖ ⥤ T.modules A

/-- Derived category of strict inverse sequences, derived before evaluation.
Source: Stacks 0941, 099M (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.towerDerived (T : Site.{u}) (A : Type u) [CommRing A] :=
  ConstantCompletion.TD (T.ring A)

/-- The derived quotient tower, with its fixed universal K-flat comparison.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.reduction (T : Site.{u}) (A : Type u) [CommRing A] (I : Ideal A) :=
  (ConstantCompletion.quotientPresentation T.topology A I false).tower

/-- Total right derived strict inverse limit, retaining its universal comparison.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.rlim (T : Site.{u}) (A : Type u) [CommRing A] :=
  ConstantCompletion.rlim (T.ring A)

/-- Quotient-tower derived completion, not an unspecified reflector.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.completion (T : Site.{u}) (A : Type u) [CommRing A] (I : Ideal A) :=
  ConstantCompletion.completion T.topology A I false

/-- Its prescribed quotient-tower unit.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.unit (T : Site.{u}) (A : Type u) [CommRing A] (I : Ideal A) :=
  ConstantCompletion.completionUnit T.topology A I false

/-- Local derived internal-Hom completeness at every section of the constant ideal.
Source: Stacks 0999, 099M (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.IsComplete (T : Site.{u}) (A : Type u) [CommRing A] (I : Ideal A) :=
  ConstantCompletion.IsComplete (ConstantCompletion.quotient T.topology A I 0)

/-- The full subcategory of locally derived complete objects.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.Complete (T : Site.{u}) (A : Type u) [CommRing A] (I : Ideal A) :=
  ObjectProperty.FullSubcategory (T.IsComplete A I)

/-- The actual geometric adjunction, with its canonical algebraic inverse-image lift.
The lift records all ring and module operations on generalized sections and the
natural constant-ring identifications; it is not an arbitrary module functor.
Source: Stacks 099N, 00YV, 03D2
(blueprint: lem-sp-completion-mate-comparison). -/
structure Morphism (V U : Site.{u}) where
  inverse : Sheaf V.topology (Type u) ⥤ Sheaf U.topology (Type u)
  direct : Sheaf U.topology (Type u) ⥤ Sheaf V.topology (Type u)
  adjunction : inverse ⊣ direct
  [finiteLimits : PreservesFiniteLimits inverse]
  algebra : ConstantCompletion.InverseImageData inverse

attribute [instance] Morphism.finiteLimits

/-- Constant-coefficient module inverse image, via the canonical constant-ring map.
Source: Stacks 099N, 03D2 (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Morphism.modulePull {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : V.modules A ⥤ U.modules A :=
  ConstantCompletion.pull f.algebra (ConstantCompletion.constantMap f.algebra A)

/-- Additivity of the constant-coefficient inverse image, as a named instance.
Source: Stacks 099N, 03D2 (blueprint: lem-sp-completion-mate-comparison).
Proof: unfold the specified inverse image. Scalar extension and ringed inverse image
are additive, so the existing additive-functor instance applies. -/
instance Morphism.modulePull_additive {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : (f.modulePull A).Additive := by
  dsimp only [Morphism.modulePull]
  infer_instance

/-- Exactness and existence of the right adjoint of the specified module inverse image.
Source: Stacks 099N, 03D7 (blueprint: lem-sp-completion-mate-comparison).
Proof: the algebraic lift preserves finite limits and colimits on underlying additive
sheaves. The constant-ring map is an isomorphism, so extension of scalars along it is
an equivalence and exact. Transport the original topos adjunction through the algebraic
operations; the tensor-unit insertion gives the module hom-set bijection. -/
theorem Morphism.modulePull_properties {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] :
    PreservesFiniteLimits (f.modulePull A) ∧ PreservesFiniteColimits (f.modulePull A) ∧
      (f.modulePull A).IsLeftAdjoint := by
  sorry

/-- Finite limits for the exact module inverse image.
Source: Stacks 099N (blueprint: lem-sp-completion-mate-comparison). -/
instance Morphism.modulePull_finiteLimits {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : PreservesFiniteLimits (f.modulePull A) :=
  (f.modulePull_properties A).1

/-- Finite colimits for the exact module inverse image.
Source: Stacks 099N (blueprint: lem-sp-completion-mate-comparison). -/
instance Morphism.modulePull_finiteColimits {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : PreservesFiniteColimits (f.modulePull A) :=
  (f.modulePull_properties A).2.1

/-- The right adjoint is specified by the module hom-functor it represents.
Source: Stacks 099N, 03D7 (blueprint: lem-sp-completion-mate-comparison). -/
instance Morphism.modulePull_leftAdjoint {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : (f.modulePull A).IsLeftAdjoint :=
  (f.modulePull_properties A).2.2

/-- The module direct image, as the representing right adjoint to the actual inverse image.
Source: Stacks 099N, 03D7 (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Morphism.modulePush {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : U.modules A ⥤ V.modules A :=
  Functor.rightAdjoint (f.modulePull A)

/-- The fixed module adjunction; all later mates use these same units and counits.
Source: Stacks 099N, 03D7 (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Morphism.moduleAdjunction {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : f.modulePull A ⊣ f.modulePush A :=
  Adjunction.ofIsLeftAdjoint (f.modulePull A)

/-- Direct image is additive, as the right adjoint of an additive functor.
Source: Stacks 099N (blueprint: lem-sp-completion-mate-comparison). -/
instance Morphism.modulePush_additive {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : (f.modulePush A).Additive :=
  (f.moduleAdjunction A).right_adjoint_additive

/-- Standard localization of the actual module category.
Source: Stacks 099N (blueprint: lem-sp-completion-mate-comparison). -/
instance Site.hasDerived (T : Site.{u}) (A : Type u) [CommRing A] :
    HasDerivedCategory (T.modules A) := HasDerivedCategory.standard _

/-- Standard localization of strict module towers.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
instance Site.towersHasDerived (T : Site.{u}) (A : Type u) [CommRing A] :
    HasDerivedCategory (T.towers A) := HasDerivedCategory.standard _

/-- K-injective resolutions on the small ringed site.
Source: Stacks 079P, 099N (blueprint: lem-sp-completion-mate-comparison).
Proof: module sheaves on a small site form a Grothendieck category, hence have
functorial K-injective resolutions. -/
@[instance]
theorem Site.hasKInjectives (T : Site.{u}) (A : Type u) [CommRing A] :
    Abelian.HasKInjectiveResolutions (T.modules A) := by
  sorry

/-- K-injective resolutions in strict towers, by their small diagram-site realization.
Source: Stacks 079P, 0941 (blueprint: lem-sp-completion-mate-comparison).
Proof: smallModuleDiagrams_isGrothendieckAbelian supplies the Grothendieck property;
apply the K-injective resolution theorem to this abelian category. -/
@[instance]
theorem Site.towersHasKInjectives (T : Site.{u}) (A : Type u) [CommRing A] :
    Abelian.HasKInjectiveResolutions (T.towers A) := by
  sorry

/-- Exact inverse image on unbounded derived categories.
Source: Stacks 099N (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Morphism.pull {V U : Site.{u}} (f : Morphism V U) (A : Type u) [CommRing A] :=
  (f.modulePull A).mapDerivedCategory

/-- K-injective total right derived module direct image.
Source: Stacks 099N (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Morphism.push {V U : Site.{u}} (f : Morphism V U) (A : Type u) [CommRing A] :=
  (f.modulePush A).rightDerivedFunctor

/-- The canonical derived adjunction induced from the fixed ordinary module adjunction.
Source: Stacks 099N (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.adj {V U : Site.{u}} (f : Morphism V U) (A : Type u) [CommRing A] :
    f.pull A ⊣ f.push A :=
  (f.moduleAdjunction A).mapDerivedCategoryRightDerivedAdjunction

/-- Completion has complete output and its quotient unit has the reflection property.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison).
Proof: choose finite generators of I by Noetherianity. Apply
ConstantCompletion.koszul_quotient_reflector to this list. Its unit-preserving
Koszul/quotient comparison gives output completeness and the hom-set bijection;
its last clause identifies the complete inputs. This includes the empty list. -/
theorem Site.completion_properties (T : Site.{u}) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    (∀ M : T.derived A, T.IsComplete A I ((T.completion A I).obj M)) ∧
      (∀ (M L : T.derived A), T.IsComplete A I L →
        Function.Bijective (fun a : (T.completion A I).obj M ⟶ L ↦
          (T.unit A I).app M ≫ a)) ∧
      (∀ M : T.derived A, IsIso ((T.unit A I).app M) ↔ T.IsComplete A I M) := by
  sorry

/-- Completion as a functor to the actual full complete subcategory.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
def Site.reflector (T : Site.{u}) (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) : T.derived A ⥤ T.Complete A I :=
  ObjectProperty.lift (T.IsComplete A I) (T.completion A I)
    ((T.completion_properties A I).1)

/-- The specified representative or unit normalization for this comparison.
Source: Stacks 099M, 099N, 0941 and 0E48
(blueprint: lem-sp-completion-mate-comparison). -/
def Site.reflectorAdjunction_normalized (T : Site.{u}) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (adj : T.reflector A I ⊣ ObjectProperty.ι (T.IsComplete A I)) : Prop :=
  ∀ (M : T.derived A) (L : T.Complete A I) (a : (T.reflector A I).obj M ⟶ L),
    adj.homEquiv M L a = (T.unit A I).app M ≫ a.hom

/-- The completion adjunction is uniquely fixed by precomposition with its quotient unit.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison).
Proof: the preceding bijection is natural in both arguments by naturality of the
quotient unit. It supplies the adjunction hom equivalence. Surjectivity constructs
its inverse; injectivity proves its inverse identities and uniqueness. -/
theorem Site.reflectorAdjunction_existsUnique (T : Site.{u}) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    ∃! adj : T.reflector A I ⊣ ObjectProperty.ι (T.IsComplete A I),
      Site.reflectorAdjunction_normalized T A I adj := by
  sorry

/-- The unit-normalized completion adjunction.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
def Site.reflectorAdjunction (T : Site.{u}) (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    T.reflector A I ⊣ ObjectProperty.ι (T.IsComplete A I) :=
  (T.reflectorAdjunction_existsUnique A I).exists.choose

/-- Derived direct image preserves local derived completeness.
Source: Stacks 099N(1) (blueprint: lem-sp-completion-mate-comparison).
Proof: apply ConstantCompletion.completedPullbackAdjunction to the given geometric
adjunction. The generalized-section operation identities identify its algebraic lift
with f.algebra. The module hom-set normalization and universal derived comparison
identify its direct image with f.push A; transport its completeness-preservation
clause across that canonical isomorphism. Equivalently, on each slice, adjunction
and localization identify internal Hom from A[1/a] into Rf_*L with direct image
of the corresponding internal Hom into L, which vanishes for complete L. -/
theorem Morphism.push_complete {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (L : U.derived A) (hL : U.IsComplete A I L) :
    V.IsComplete A I ((f.push A).obj L) := by
  sorry

/-- Direct image restricted to the full complete subcategories.
Source: Stacks 099N(1) (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.completePush {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    U.Complete A I ⥤ V.Complete A I :=
  ObjectProperty.lift (V.IsComplete A I)
    (ObjectProperty.ι (U.IsComplete A I) ⋙ f.push A)
    (fun L ↦ f.push_complete A I L.obj L.property)

/-- Completed inverse image is ordinary inverse image followed by the specified reflector.
Source: Stacks 099N(2) (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.completePull {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    V.Complete A I ⥤ U.Complete A I :=
  ObjectProperty.ι (V.IsComplete A I) ⋙ f.pull A ⋙ U.reflector A I

/-- The specified representative or unit normalization for this comparison.
Source: Stacks 099M, 099N, 0941 and 0E48
(blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.completeAdjunction_normalized {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (adj : f.completePull A I ⊣ f.completePush A I) : Prop :=
  ∀ (M : V.Complete A I) (L : U.Complete A I)
    (a : (f.completePull A I).obj M ⟶ L),
    (adj.homEquiv M L a).hom = (f.adj A).homEquiv M.obj L.obj
      ((U.unit A I).app ((f.pull A).obj M.obj) ≫ a.hom)

/-- Completed adjunction, with exactly the composite ordinary and completion hom bijections.
Source: Stacks 099N(2) (blueprint: lem-sp-completion-mate-comparison).
Proof: transpose a map from C_U f^*M to L first under the completion adjunction,
then under f^* ⊣ Rf_*. Completeness of Rf_*L lets the result be regarded as a
map in the full complete subcategory. The two inverse identities and naturality
follow from those of the two hom bijections. This also proves uniqueness. -/
theorem Morphism.completeAdjunction_existsUnique {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    ∃! adj : f.completePull A I ⊣ f.completePush A I,
      Morphism.completeAdjunction_normalized f A I adj := by
  sorry

/-- The completed adjunction with the prescribed hom-set normalization.
Source: Stacks 099N(2) (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.completeAdjunction {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    f.completePull A I ⊣ f.completePush A I :=
  (f.completeAdjunction_existsUnique A I).exists.choose


variable {Y X Y' X' : Site.{u}}

/-- Termwise inverse image on the strict sequence category.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Morphism.towerModulePull {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : V.towers A ⥤ U.towers A :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (f.modulePull A)

/-- Termwise direct image before derivation.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Morphism.towerModulePush {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : U.towers A ⥤ V.towers A :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (f.modulePush A)

/-- Termwise inverse image is exact, because kernels and cokernels are levelwise.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison).
Proof: evaluate a finite limiting or colimiting cone at each index. Exactness of
modulePull makes the image cone limiting or colimiting at every index, hence in
the functor category. -/
theorem Morphism.towerModulePull_exact {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] :
    PreservesFiniteLimits (f.towerModulePull A) ∧
      PreservesFiniteColimits (f.towerModulePull A) := by
  sorry

/-- Finite limits of the termwise inverse image.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
instance Morphism.towerModulePull_finiteLimits {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : PreservesFiniteLimits (f.towerModulePull A) :=
  (f.towerModulePull_exact A).1

/-- Finite colimits of the termwise inverse image.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
instance Morphism.towerModulePull_finiteColimits {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : PreservesFiniteColimits (f.towerModulePull A) :=
  (f.towerModulePull_exact A).2

/-- Exact derived inverse image of strict towers.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Morphism.towerPull {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] := (f.towerModulePull A).mapDerivedCategory

/-- The total right derived functor of termwise module direct image.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Morphism.towerPush {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] := (f.towerModulePush A).rightDerivedFunctor

/-- The derived termwise adjunction, from the same ordinary module adjunction.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.towerAdjunction {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] : f.towerPull A ⊣ f.towerPush A :=
  (Adjunction.whiskerRight ℕᵒᵖ (f.moduleAdjunction A)).mapDerivedCategoryRightDerivedAdjunction

/-- A specified commutation isomorphism of the original geometric inverse images.
Source: Stacks 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Square (f : Morphism Y X) (g : Morphism Y Y')
    (h : Morphism X X') (k : Morphism Y' X') :=
  g.inverse ⋙ k.inverse ≅ f.inverse ⋙ h.inverse

/-- The specified representative or unit normalization for this comparison.
Source: Stacks 099M, 099N, 0941 and 0E48
(blueprint: lem-sp-completion-mate-comparison). -/
def moduleSquare_normalized
    {f : Morphism Y X} {g : Morphism Y Y'} {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A]
    (e : g.modulePull A ⋙ k.modulePull A ≅ f.modulePull A ⋙ h.modulePull A) : Prop :=
  ∀ M : Y.modules A,
    k.inverse.map (ConstantCompletion.pullInsertion g.algebra
        (ConstantCompletion.constantMap g.algebra A) M) ≫
      ConstantCompletion.pullInsertion k.algebra
        (ConstantCompletion.constantMap k.algebra A) ((g.modulePull A).obj M) ≫
      (ConstantCompletion.underlying (X'.ring A)).map (e.hom.app M) =
    sq.hom.app ((ConstantCompletion.underlying (Y.ring A)).obj M) ≫
      h.inverse.map (ConstantCompletion.pullInsertion f.algebra
        (ConstantCompletion.constantMap f.algebra A) M) ≫
      ConstantCompletion.pullInsertion h.algebra
        (ConstantCompletion.constantMap h.algebra A) ((f.modulePull A).obj M)

/-- The canonical module square is uniquely fixed on scalar insertions.
Source: Stacks 03D2, 0E48 (blueprint: lem-sp-completion-mate-comparison).
Proof: apply the given set-sheaf square to inverse-image modules. Naturality on
generalized sections makes it additive and compatible with the constant A-action.
Extension of scalars sends a generator to its image tensored with 1. These generators
locally generate, so the insertion formula gives uniqueness. Apply the inverse square
to get the inverse map. -/
theorem moduleSquare_existsUnique
    {f : Morphism Y X} {g : Morphism Y Y'} {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A] :
    ∃! e : g.modulePull A ⋙ k.modulePull A ≅ f.modulePull A ⋙ h.modulePull A,
      moduleSquare_normalized sq A e := by
  sorry

/-- The ordinary module comparison with its scalar-insertion normalization.
Source: Stacks 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def moduleSquare {f : Morphism Y X} {g : Morphism Y Y'}
    {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A] :=
  (moduleSquare_existsUnique sq A).exists.choose

/-- The ordinary derived square, obtained by exact localization of that module square.
Source: Stacks 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def derivedSquare {f : Morphism Y X} {g : Morphism Y Y'}
    {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A] :
    g.pull A ⋙ k.pull A ≅ f.pull A ⋙ h.pull A :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (moduleSquare sq A) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The strict module square is the pointwise extension of the original module square.
Source: Stacks 0941, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def towerModuleSquare {f : Morphism Y X} {g : Morphism Y Y'}
    {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A] :
    g.towerModulePull A ⋙ k.towerModulePull A ≅
      f.towerModulePull A ⋙ h.towerModulePull A :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (moduleSquare sq A)

/-- The canonical square on derived strict towers.
Source: Stacks 0941, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def towerSquare {f : Morphism Y X} {g : Morphism Y Y'}
    {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A] :
    g.towerPull A ⋙ k.towerPull A ≅ f.towerPull A ⋙ h.towerPull A :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (towerModuleSquare sq A) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The strict tower exchange, using Mathlib's mate equivalence.
Source: Stacks 0941, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def towerExchange {f : Morphism Y X} {g : Morphism Y Y'}
    {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A] :
    f.towerPush A ⋙ g.towerPull A ⟶ h.towerPull A ⋙ k.towerPush A :=
  (mateEquiv (f.towerAdjunction A) (k.towerAdjunction A)
    (TwoSquare.mk _ _ _ _ (towerSquare sq A).hom)).natTrans

/-- The ordinary coefficient exchange for any commutative coefficient ring.
Source: Stacks 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def ordinaryExchange {f : Morphism Y X} {g : Morphism Y Y'}
    {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A] :
    f.push A ⋙ g.pull A ⟶ h.pull A ⋙ k.push A :=
  (mateEquiv (f.adj A) (k.adj A)
    (TwoSquare.mk _ _ _ _ (derivedSquare sq A).hom)).natTrans

/-- The right-adjoint square is the adjunction conjugate of the canonical left square.
Source: Stacks 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def rightSquare {f : Morphism Y X} {g : Morphism Y Y'}
    {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A] :
    h.push A ⋙ f.push A ≅ k.push A ⋙ g.push A :=
  conjugateIsoEquiv ((f.adj A).comp (h.adj A)) ((g.adj A).comp (k.adj A))
    (derivedSquare sq A)

/-- Restrict the same right-adjoint square to complete objects, with no new normalization.
Source: Stacks 099N, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def completeRightSquare {f : Morphism Y X} {g : Morphism Y Y'}
    {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    h.completePush A I ⋙ f.completePush A I ≅
      k.completePush A I ⋙ g.completePush A I :=
  NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk _ ((rightSquare sq A).app M.obj))
    (fun a ↦ by ext; exact (rightSquare sq A).hom.naturality a.hom)

/-- The completed pullback square is precisely the conjugate of the prescribed
right-adjoint square through the two composite completed adjunctions.
Source: Stacks 099N, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def completeSquare {f : Morphism Y X} {g : Morphism Y Y'}
    {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    g.completePull A I ⋙ k.completePull A I ≅
      f.completePull A I ⋙ h.completePull A I :=
  (conjugateIsoEquiv
    ((f.completeAdjunction A I).comp (h.completeAdjunction A I))
    ((g.completeAdjunction A I).comp (k.completeAdjunction A I))).symm
      (completeRightSquare sq A I)

/-- The exchange defined by the completed adjunctions, not by taking a tower limit.
Source: Stacks 099N, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def completeExchange {f : Morphism Y X} {g : Morphism Y Y'}
    {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    f.completePush A I ⋙ g.completePull A I ⟶
      h.completePull A I ⋙ k.completePush A I :=
  (mateEquiv (f.completeAdjunction A I) (k.completeAdjunction A I)
    (TwoSquare.mk _ _ _ _ (completeSquare sq A I).hom)).natTrans


/-- Exact derived constant towers, used only to normalize the strict-limit adjunction.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.delta (T : Site.{u}) (A : Type u) [CommRing A] :=
  (ConstantCompletion.constantTower T.topology (T.ring A)).mapDerivedCategory

/-- The specified representative or unit normalization for this comparison.
Source: Stacks 099M, 099N, 0941 and 0E48
(blueprint: lem-sp-completion-mate-comparison). -/
def Site.deltaAdjunction_normalized (T : Site.{u}) (A : Type u) [CommRing A]
    (adj : T.delta A ⊣ T.rlim A) : Prop :=
  ∀ P : CochainComplex (T.modules A) ℤ,
    adj.unit.app ((ConstantCompletion.Q (T.ring A)).obj P) ≫
        (T.rlim A).map ((ConstantCompletion.constantTower T.topology
          (T.ring A)).mapDerivedCategoryFactors.hom.app P) =
      (ConstantCompletion.Q (T.ring A)).map
        ((NatTrans.mapHomologicalComplex
          (constLimAdj : ConstantCompletion.constantTower T.topology (T.ring A) ⊣
            (lim : T.towers A ⥤ T.modules A)).unit (.up ℤ)).app P) ≫
      (ConstantCompletion.limitComparison (T.ring A)).app
        (((ConstantCompletion.constantTower T.topology (T.ring A)).mapHomologicalComplex
          (.up ℤ)).obj P)

/-- The constant/derived-limit adjunction has the unit computed by the actual
ordinary limit unit and the specified right-derived comparison on every complex.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison).
Proof: derive the exact constant-tower/limit adjunction. The universal right-derived
property identifies its right adjoint with ConstantCompletion.rlim. Transport the
adjunction through that unique comparison. The displayed unit equation is the
derived-adjunction fraction formula and fixes its hom equivalence uniquely. -/
theorem Site.deltaAdjunction_existsUnique (T : Site.{u}) (A : Type u) [CommRing A] :
    ∃! adj : T.delta A ⊣ T.rlim A,
      Site.deltaAdjunction_normalized T A adj := by
  sorry

/-- The fixed constant-tower/derived-limit adjunction.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
def Site.deltaAdjunction (T : Site.{u}) (A : Type u) [CommRing A] :=
  (T.deltaAdjunction_existsUnique A).exists.choose

/-- Constant towers commute with termwise inverse image by identity components.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.constantModulePullIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] :
    ConstantCompletion.constantTower V.topology (V.ring A) ⋙ f.towerModulePull A ≅
      f.modulePull A ⋙ ConstantCompletion.constantTower U.topology (U.ring A) :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (fun _ ↦ by simp)) (fun _ ↦ by ext n; simp)

/-- Its canonical exact derived counterpart.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.constantPullIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] :
    V.delta A ⋙ f.towerPull A ≅ f.pull A ⋙ U.delta A :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (f.constantModulePullIso A) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The canonical direct-image/derived-limit comparison. It is the adjunction
conjugate of the identity-component constant/inverse-image comparison.
Thus its K-injective computation is the ordinary identity u_* lim = lim u_*.
Source: Stacks 0941, 0A07 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.directLimitIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] :
    U.rlim A ⋙ f.push A ≅ f.towerPush A ⋙ V.rlim A :=
  conjugateIsoEquiv ((f.adj A).comp (U.deltaAdjunction A))
    ((V.deltaAdjunction A).comp (f.towerAdjunction A)) (f.constantPullIso A)

/-- The specified representative or unit normalization for this comparison.
Source: Stacks 099M, 099N, 0941 and 0E48
(blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.moduleReductionPullIso_normalized {V U : Site.{u}}
    (f : Morphism V U) (A : Type u) [CommRing A] (I : Ideal A)
    (e : ConstantCompletion.reductionTower V.topology A I false ⋙ f.towerModulePull A ≅
        f.modulePull A ⋙ ConstantCompletion.reductionTower U.topology A I false) : Prop :=
  ∀ (M : V.modules A) (n : ℕ),
    f.inverse.map (ConstantCompletion.insertion
        (ConstantCompletion.quotient V.topology A I n) M) ≫
      ConstantCompletion.pullInsertion f.algebra (ConstantCompletion.constantMap f.algebra A)
        ((ConstantCompletion.reduction V.topology A I false n).obj M) ≫
      (ConstantCompletion.underlying (U.ring A)).map ((e.hom.app M).app (op n)) =
    ConstantCompletion.pullInsertion f.algebra
        (ConstantCompletion.constantMap f.algebra A) M ≫
      ConstantCompletion.insertion (ConstantCompletion.quotient U.topology A I n)
        ((f.modulePull A).obj M)

/-- The ordinary strict reduction/pullback comparison is fixed on quotient-unit
insertions at every level. Its source and target are actual strict diagrams.
Source: Stacks 07A4, 099N(5) (blueprint: lem-sp-completion-mate-comparison).
Proof: scalar extension and exact inverse image preserve the balanced quotient
relations. Send an inverse-image quotient tensor to the same quotient tensor.
Naturality of the coefficient quotient maps makes these maps commute with all
transitions. The insertion equation and linearity determine them uniquely;
the reverse tensor reassociation is inverse. -/
theorem Morphism.moduleReductionPullIso_existsUnique {V U : Site.{u}}
    (f : Morphism V U) (A : Type u) [CommRing A] (I : Ideal A) :
    ∃! e : ConstantCompletion.reductionTower V.topology A I false ⋙ f.towerModulePull A ≅
        f.modulePull A ⋙ ConstantCompletion.reductionTower U.topology A I false,
      Morphism.moduleReductionPullIso_normalized f A I e := by
  sorry

/-- The prescribed strict ordinary reduction/pullback isomorphism.
Source: Stacks 07A4, 099N(5) (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.moduleReductionPullIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) :=
  (f.moduleReductionPullIso_existsUnique A I).exists.choose

/-- The ordinary pullback/reduction composite preserves zero morphisms.
Source: Stacks 07A4 (blueprint: lem-sp-completion-mate-comparison). -/
instance Morphism.moduleReductionPull_preservesZero {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) :
    (f.modulePull A ⋙ ConstantCompletion.reductionTower U.topology A I false
      ).PreservesZeroMorphisms := by
  let := ConstantCompletion.reductionTower_additive U.topology A I false
  infer_instance

/-- The ordinary strict reduction comparison applied to a whole complex.
The iterated complex functors are explicit endpoints of the lifted square.
Its hom component is the original ordinary comparison applied degreewise.
Source: Stacks 07A4, 0941 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.moduleReductionPullComplexIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) :
    (ConstantCompletion.reductionTower V.topology A I false).mapHomologicalComplex (.up ℤ) ⋙
        (f.towerModulePull A).mapHomologicalComplex (.up ℤ) ≅
      (f.modulePull A).mapHomologicalComplex (.up ℤ) ⋙
        (ConstantCompletion.reductionTower U.topology A I false).mapHomologicalComplex (.up ℤ) :=
  letI := ConstantCompletion.reductionTower_additive V.topology A I false
  letI := ConstantCompletion.reductionTower_additive U.topology A I false
  letI := f.modulePull_additive A
  ConstantCompletion.mapComplexSquare
    (C := V.modules A) (D := V.towers A) (D' := U.modules A) (E := U.towers A)
    (ConstantCompletion.reductionTower V.topology A I false) (f.towerModulePull A)
    (f.modulePull A) (ConstantCompletion.reductionTower U.topology A I false)
    (f.moduleReductionPullIso A I)

/-- The specified representative or unit normalization for this comparison.
Source: Stacks 099M, 099N, 0941 and 0E48
(blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.reductionPullIso_normalized {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A)
    (e : V.reduction A I ⋙ f.towerPull A ≅ f.pull A ⋙ U.reduction A I) : Prop :=
  ∀ P : CochainComplex (V.modules A) ℤ, P.IsAcyclicTensorKFlat →
    (∀ q : ℤ, (P.X q).IsFlat) →
    e.hom.app ((ConstantCompletion.Q (V.ring A)).obj P) ≫
      (U.reduction A I).map ((f.modulePull A).mapDerivedCategoryFactors.hom.app P) ≫
      (ConstantCompletion.quotientPresentation U.topology A I false).comparison.app
        (((f.modulePull A).mapHomologicalComplex (.up ℤ)).obj P) =
    (f.towerPull A).map
        ((ConstantCompletion.quotientPresentation V.topology A I false).comparison.app P) ≫
      (f.towerModulePull A).mapDerivedCategoryFactors.hom.app
        (ConstantCompletion.reductionComplex V.topology A I false P) ≫
      (ConstantCompletion.TQ (U.ring A)).map
        ((f.moduleReductionPullComplexIso A I).hom.app P)

/-- The strict derived comparison is uniquely characterized on a single flat-term
K-flat representative, with the entire strict ordinary comparison applied termwise.
Source: Stacks 07A4, 099N(5) (blueprint: lem-sp-completion-mate-comparison).
Proof: exact inverse image preserves flat K-flat representatives. The diagonal of
one such representative is K-flat on the diagram site, so it computes reduction
against the whole quotient diagram. Apply moduleReductionPullIso termwise, insert
the universal reduction comparisons and the exact-pullback factorizations, then
descend along localization. Every object has such a representative, proving uniqueness. -/
theorem Morphism.reductionPullIso_existsUnique {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) :
    ∃! e : V.reduction A I ⋙ f.towerPull A ≅ f.pull A ⋙ U.reduction A I,
      Morphism.reductionPullIso_normalized f A I e := by
  sorry

/-- The uniquely normalized derived reduction/pullback comparison.
Source: Stacks 07A4, 099N(5) (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.reductionPullIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) :=
  (f.reductionPullIso_existsUnique A I).exists.choose

/-- The whole-diagram projection is the tower adjunct of counit tensored with identity.
The preceding reduction comparison is the canonical tensor/pullback identification.
Source: Stacks 0B56, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.towerProjection {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (K : U.derived A) :
    (V.reduction A I).obj ((f.push A).obj K) ⟶
      (f.towerPush A).obj ((U.reduction A I).obj K) :=
  (f.towerAdjunction A).homEquiv _ _
    ((f.reductionPullIso A I).hom.app ((f.push A).obj K) ≫
      (U.reduction A I).map ((f.adj A).counit.app K))

/-- The comparison H is inverse horizontal pullback/reduction comparison followed by
horizontal pullback of the strict projection adjunct, exactly in the specified direction.
Source: Stacks 0B56, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def projectionComparison {f : Morphism Y X} {g : Morphism Y Y'}
    (A : Type u) [CommRing A] (I : Ideal A) (K : X.derived A) :
    (Y'.reduction A I).obj ((g.pull A).obj ((f.push A).obj K)) ⟶
      (g.towerPull A).obj ((f.towerPush A).obj ((X.reduction A I).obj K)) :=
  (g.reductionPullIso A I).inv.app ((f.push A).obj K) ≫
    (g.towerPull A).map (f.towerProjection A I K)

/-- Each positive quotient is perfect as an A-complex: bounded finite projectives.
Source: smooth-purity blueprint, fix-lem-exchanges Step 4
(blueprint: lem-sp-completion-mate-comparison). -/
def PerfectQuotients (A : Type u) [CommRing A] (I : Ideal A) : Prop :=
  letI := HasDerivedCategory.standard (ModuleCat.{u} A)
  ∀ n : ℕ, DerivedCategory.IsPerfectRingComplex
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      (ModuleCat.of A (A ⧸ I ^ (n + 1))))


/-- Exact evaluation of a strict tower, before localization.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.evaluateModule (T : Site.{u}) (A : Type u) [CommRing A] (n : ℕ) :=
  (evaluation ℕᵒᵖ (T.modules A)).obj (op n)

/-- Exact evaluation after deriving the strict diagram category.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.evaluate (T : Site.{u}) (A : Type u) [CommRing A] (n : ℕ) :=
  (T.evaluateModule A n).mapDerivedCategory

/-- Termwise inverse image commutes with ordinary evaluation by identity components.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.evaluateModulePullIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (n : ℕ) :
    f.towerModulePull A ⋙ U.evaluateModule A n ≅ V.evaluateModule A n ⋙ f.modulePull A :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by rfl)

/-- The canonical derived evaluation/inverse-image comparison.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.evaluatePullIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (n : ℕ) :
    f.towerPull A ⋙ U.evaluate A n ≅ V.evaluate A n ⋙ f.pull A :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (f.evaluateModulePullIso A n) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The complex-level universal derived-direct-image unit, from the existing K-injective
right-derived functor, with no new choice.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.pushUnit {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (P : CochainComplex (U.modules A) ℤ) :
    (ConstantCompletion.Q (V.ring A)).obj (((f.modulePush A).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      (f.push A).obj ((ConstantCompletion.Q (U.ring A)).obj P) :=
  (f.modulePush A).rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)

/-- The same universal unit for derived termwise direct image of strict towers.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.towerPushUnit {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (P : CochainComplex (U.towers A) ℤ) :
    (ConstantCompletion.TQ (V.ring A)).obj
        (((f.towerModulePush A).mapHomologicalComplex (.up ℤ)).obj P) ⟶
      (f.towerPush A).obj ((ConstantCompletion.TQ (U.ring A)).obj P) :=
  (f.towerModulePush A).rightDerivedFunctorUnit.app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)

/-- The specified representative or unit normalization for this comparison.
Source: Stacks 099M, 099N, 0941 and 0E48
(blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.evaluatePushIso_normalized {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (n : ℕ)
    (e : f.towerPush A ⋙ V.evaluate A n ≅ U.evaluate A n ⋙ f.push A) : Prop :=
  ∀ P : CochainComplex (U.towers A) ℤ,
    (V.evaluate A n).map (f.towerPushUnit A P) ≫
        e.hom.app ((ConstantCompletion.TQ (U.ring A)).obj P) ≫
        (f.push A).map ((U.evaluateModule A n).mapDerivedCategoryFactors.hom.app P) =
      (V.evaluateModule A n).mapDerivedCategoryFactors.hom.app
        (((f.towerModulePush A).mapHomologicalComplex (.up ℤ)).obj P) ≫
      f.pushUnit A (((U.evaluateModule A n).mapHomologicalComplex (.up ℤ)).obj P)

/-- Evaluation/direct-image comparison with its universal-unit normalization on all
strict tower complexes, and therefore its prescribed K-injective computation.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison).
Proof: evaluation has an exact left adjoint, so preserves K-injectives. A K-injective
tower thus computes both direct images after evaluation. The ordinary composites
are identical. Their universal derived units give the displayed square; localization
and K-injective representatives make the resulting natural isomorphism unique. -/
theorem Morphism.evaluatePushIso_existsUnique {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (n : ℕ) :
    ∃! e : f.towerPush A ⋙ V.evaluate A n ≅ U.evaluate A n ⋙ f.push A,
      Morphism.evaluatePushIso_normalized f A n e := by
  sorry

/-- The specified derived evaluation/direct-image isomorphism.
Source: Stacks 0941 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.evaluatePushIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (n : ℕ) :=
  (f.evaluatePushIso_existsUnique A n).exists.choose

/-- The finite quotient ring and its original coefficient action.
Source: smooth-purity blueprint, fix-lem-exchanges Step 4
(blueprint: lem-sp-completion-mate-comparison). -/
abbrev quotientRing (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :=
  A ⧸ I ^ (n + 1)

/-- Reduction retaining the finite quotient coefficient category.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.finiteReduction (T : Site.{u}) (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) :=
  ConstantCompletion.extend (ConstantCompletion.quotient T.topology A I n)

/-- Restriction from the finite coefficient category to the original A-coefficients.
Source: Stacks 099M (blueprint: lem-sp-completion-mate-comparison). -/
abbrev Site.finiteRestriction (T : Site.{u}) (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) :=
  ConstantCompletion.dres (ConstantCompletion.quotient T.topology A I n)

/-- The specified representative or unit normalization for this comparison.
Source: Stacks 099M, 099N, 0941 and 0E48
(blueprint: lem-sp-completion-mate-comparison). -/
def Site.finiteModuleAdjunction_normalized (T : Site.{u}) (A : Type u)
    [CommRing A] (I : Ideal A) (n : ℕ)
    (adj : ConstantCompletion.change (ConstantCompletion.quotient T.topology A I n) ⊣
        ConstantCompletion.res (ConstantCompletion.quotient T.topology A I n)) : Prop :=
  ∀ (M : T.modules A) (N : T.modules (quotientRing A I n))
    (a : (ConstantCompletion.change
      (ConstantCompletion.quotient T.topology A I n)).obj M ⟶ N),
    (ConstantCompletion.underlying (T.ring A)).map (adj.homEquiv M N a) =
      ConstantCompletion.insertion (ConstantCompletion.quotient T.topology A I n) M ≫
        (ConstantCompletion.underlying (T.ring (quotientRing A I n))).map a

/-- The normalized ordinary scalar-extension adjunction, fixed by insertion of 1.
Source: Stacks 03CU (blueprint: lem-sp-completion-mate-comparison).
Proof: the tensor/sheafification universal property sends a linear map out of a
scalar extension to its restriction along m mapped to 1 tensor m. The inverse sends
s tensor m to s times the image of m. The balanced relations and sheafification
prove the inverse identities. This determines the hom bijection uniquely. -/
theorem Site.finiteModuleAdjunction_existsUnique (T : Site.{u}) (A : Type u)
    [CommRing A] (I : Ideal A) (n : ℕ) :
    ∃! adj : ConstantCompletion.change (ConstantCompletion.quotient T.topology A I n) ⊣
        ConstantCompletion.res (ConstantCompletion.quotient T.topology A I n),
      Site.finiteModuleAdjunction_normalized T A I n adj := by
  sorry

/-- The tensor-unit normalized module extension/restriction adjunction.
Source: Stacks 03CU (blueprint: lem-sp-completion-mate-comparison). -/
def Site.finiteModuleAdjunction (T : Site.{u}) (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) :=
  (T.finiteModuleAdjunction_existsUnique A I n).exists.choose

/-- The specified representative or unit normalization for this comparison.
Source: Stacks 099M, 099N, 0941 and 0E48
(blueprint: lem-sp-completion-mate-comparison). -/
def Site.finiteAdjunction_normalized (T : Site.{u}) (A : Type u)
    [CommRing A] (I : Ideal A) (n : ℕ)
    (adj : T.finiteReduction A I n ⊣ T.finiteRestriction A I n) : Prop :=
  ∀ P : CochainComplex (T.modules A) ℤ, P.IsAcyclicTensorKFlat →
    adj.unit.app ((ConstantCompletion.Q (T.ring A)).obj P) ≫
        (T.finiteRestriction A I n).map
          ((ConstantCompletion.extendComparison
            (ConstantCompletion.quotient T.topology A I n)).app P) =
      (ConstantCompletion.Q (T.ring A)).map ((NatTrans.mapHomologicalComplex
        (T.finiteModuleAdjunction A I n).unit (.up ℤ)).app P) ≫
      (ConstantCompletion.resFactors (ConstantCompletion.quotient T.topology A I n)).hom.app
        (((ConstantCompletion.change (ConstantCompletion.quotient T.topology A I n)
          ).mapHomologicalComplex (.up ℤ)).obj P)

/-- Derived extension/restriction adjunction with its unit fixed on K-flat representatives.
Source: Stacks 06YY (blueprint: lem-sp-completion-mate-comparison).
Proof: derive the tensor-unit normalized ordinary adjunction. Exact restriction and
K-flat scalar-extension computation give the displayed equation for its unit. Every
object has a K-flat representative, so this equation determines the unit and hence
the adjunction uniquely. -/
theorem Site.finiteAdjunction_existsUnique (T : Site.{u}) (A : Type u)
    [CommRing A] (I : Ideal A) (n : ℕ) :
    ∃! adj : T.finiteReduction A I n ⊣ T.finiteRestriction A I n,
      Site.finiteAdjunction_normalized T A I n adj := by
  sorry

/-- The specified derived finite scalar-extension adjunction.
Source: Stacks 06YY (blueprint: lem-sp-completion-mate-comparison). -/
def Site.finiteAdjunction (T : Site.{u}) (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) :=
  (T.finiteAdjunction_existsUnique A I n).exists.choose

/-- The specified representative or unit normalization for this comparison.
Source: Stacks 099M, 099N, 0941 and 0E48
(blueprint: lem-sp-completion-mate-comparison). -/
def Site.finiteEvaluationIso_normalized (T : Site.{u}) (A : Type u)
    [CommRing A] (I : Ideal A) (n : ℕ)
    (e : T.reduction A I ⋙ T.evaluate A n ≅
        T.finiteReduction A I n ⋙ T.finiteRestriction A I n) : Prop :=
  ∀ P : CochainComplex (T.modules A) ℤ, P.IsAcyclicTensorKFlat →
    (∀ q : ℤ, (P.X q).IsFlat) →
    e.hom.app ((ConstantCompletion.Q (T.ring A)).obj P) ≫
      (T.finiteRestriction A I n).map
        ((ConstantCompletion.extendComparison
          (ConstantCompletion.quotient T.topology A I n)).app P) =
    (T.evaluate A n).map
        ((ConstantCompletion.quotientPresentation T.topology A I false).comparison.app P) ≫
      ((T.evaluateModule A n).mapDerivedCategoryFactors.hom.app
          (ConstantCompletion.reductionComplex T.topology A I false P) ≫
        (ConstantCompletion.Q (T.ring A)).map
          ((ConstantCompletion.quotientEvaluationComplexIso T.topology A I n).hom.app P)) ≫
      (ConstantCompletion.resFactors (ConstantCompletion.quotient T.topology A I n)).hom.app
        (((ConstantCompletion.change (ConstantCompletion.quotient T.topology A I n)
          ).mapHomologicalComplex (.up ℤ)).obj P)

/-- The evaluated strict quotient object is the restricted finite scalar extension,
with its comparison fixed by the two universal reduction counits.
Source: Stacks 0941, 099M (blueprint: lem-sp-completion-mate-comparison).
Proof: on a single K-flat complex, evaluation of its strict quotient diagram is
its finite quotient tensor complex. Compose the universal comparison maps and the
exact restriction factorization. Descend; K-flat resolutions prove uniqueness. -/
theorem Site.finiteEvaluationIso_existsUnique (T : Site.{u}) (A : Type u)
    [CommRing A] (I : Ideal A) (n : ℕ) :
    ∃! e : T.reduction A I ⋙ T.evaluate A n ≅
        T.finiteReduction A I n ⋙ T.finiteRestriction A I n,
      Site.finiteEvaluationIso_normalized T A I n e := by
  sorry

/-- The canonical evaluation/finite-restriction comparison.
Source: Stacks 0941, 099M (blueprint: lem-sp-completion-mate-comparison). -/
def Site.finiteEvaluationIso (T : Site.{u}) (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) :=
  (T.finiteEvaluationIso_existsUnique A I n).exists.choose

/-- The specified representative or unit normalization for this comparison.
Source: Stacks 099M, 099N, 0941 and 0E48
(blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.finitePullIso_normalized {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ)
    (e : f.pull A ⋙ U.finiteReduction A I n ≅
        V.finiteReduction A I n ⋙ f.pull (quotientRing A I n)) : Prop :=
  ∀ P : CochainComplex (V.modules A) ℤ, P.IsAcyclicTensorKFlat →
    (∀ q : ℤ, (P.X q).IsFlat) →
    (U.finiteReduction A I n).map ((f.modulePull A).mapDerivedCategoryFactors.hom.app P) ≫
      (ConstantCompletion.extendComparison (ConstantCompletion.quotient U.topology A I n)).app
        (((f.modulePull A).mapHomologicalComplex (.up ℤ)).obj P) ≫
      (ConstantCompletion.Q (U.ring (quotientRing A I n))).map
        ((ConstantCompletion.mapComplexSquare (f.modulePull A)
          (ConstantCompletion.change (ConstantCompletion.quotient U.topology A I n))
          (ConstantCompletion.change (ConstantCompletion.quotient V.topology A I n))
          (f.modulePull (quotientRing A I n))
          (ConstantCompletion.ordinaryFinitePull f.algebra f.direct f.adjunction A I n)
          ).hom.app P) =
    e.hom.app ((ConstantCompletion.Q (V.ring A)).obj P) ≫
      (f.pull (quotientRing A I n)).map
        ((ConstantCompletion.extendComparison
          (ConstantCompletion.quotient V.topology A I n)).app P) ≫
      (f.modulePull (quotientRing A I n)).mapDerivedCategoryFactors.hom.app
        (((ConstantCompletion.change (ConstantCompletion.quotient V.topology A I n)
          ).mapHomologicalComplex (.up ℤ)).obj P)

/-- The finite coefficient tensor/pullback comparison, fixed by ordinary tensor
reassociation on flat-term K-flat representatives.
Source: Stacks 07A4, 099N (blueprint: lem-sp-completion-mate-comparison).
Proof: apply ConstantCompletion.ordinaryFinitePull on a K-flat representative.
Exact pullback and scalar extension preserve these representatives. Insert the
universal counits on each side, then descend by localization. The representative
formula determines the natural isomorphism uniquely. -/
theorem Morphism.finitePullIso_existsUnique {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    ∃! e : f.pull A ⋙ U.finiteReduction A I n ≅
        V.finiteReduction A I n ⋙ f.pull (quotientRing A I n),
      Morphism.finitePullIso_normalized f A I n e := by
  sorry

/-- The canonical derived finite tensor/pullback comparison.
Source: Stacks 07A4, 099N (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.finitePullIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :=
  (f.finitePullIso_existsUnique A I n).exists.choose

/-- Direct image commutes with finite scalar restriction by adjunction conjugation
of the canonical scalar-extension/pullback comparison.
Source: Stacks 06YY, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.finiteRestrictionPushIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    U.finiteRestriction A I n ⋙ f.push A ≅
      f.push (quotientRing A I n) ⋙ V.finiteRestriction A I n :=
  conjugateIsoEquiv ((f.adj A).comp (U.finiteAdjunction A I n))
    ((V.finiteAdjunction A I n).comp (f.adj (quotientRing A I n)))
      (f.finitePullIso A I n).symm


/-- The specified representative or unit normalization for this comparison.
Source: Stacks 099M, 099N, 0941 and 0E48
(blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.finiteModuleRestrictionPullIso_normalized {V U : Site.{u}}
    (f : Morphism V U) (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ)
    (e : ConstantCompletion.res (ConstantCompletion.quotient V.topology A I n) ⋙
        f.modulePull A ≅ f.modulePull (quotientRing A I n) ⋙
          ConstantCompletion.res (ConstantCompletion.quotient U.topology A I n)) : Prop :=
  ∀ M : V.modules (quotientRing A I n),
    ConstantCompletion.pullInsertion f.algebra (ConstantCompletion.constantMap f.algebra A)
        ((ConstantCompletion.res (ConstantCompletion.quotient V.topology A I n)).obj M) ≫
      (ConstantCompletion.underlying (U.ring A)).map (e.hom.app M) =
    ConstantCompletion.pullInsertion f.algebra
      (ConstantCompletion.constantMap f.algebra (quotientRing A I n)) M

/-- Ordinary inverse image commutes with finite scalar restriction, fixing its map
on every inverse-image generator, not merely its objects.
Source: Stacks 03D2, 0E48 (blueprint: lem-sp-completion-mate-comparison).
Proof: both sides have the same underlying inverse-image additive sheaf and the
same restricted constant A-action. The map is identity on its generalized sections.
Its inverse is the same identity. The displayed insertion formula fixes it uniquely. -/
theorem Morphism.finiteModuleRestrictionPullIso_existsUnique {V U : Site.{u}}
    (f : Morphism V U) (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    ∃! e : ConstantCompletion.res (ConstantCompletion.quotient V.topology A I n) ⋙
        f.modulePull A ≅ f.modulePull (quotientRing A I n) ⋙
          ConstantCompletion.res (ConstantCompletion.quotient U.topology A I n),
      Morphism.finiteModuleRestrictionPullIso_normalized f A I n e := by
  sorry

/-- The normalized ordinary inverse-image/scalar-restriction comparison.
Source: Stacks 03D2, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.finiteModuleRestrictionPullIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :=
  (f.finiteModuleRestrictionPullIso_existsUnique A I n).exists.choose

/-- Its exact derived comparison, retaining the finite quotient coefficient ring.
Source: Stacks 03D2, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.finiteRestrictionPullIso {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) :
    V.finiteRestriction A I n ⋙ f.pull A ≅
      f.pull (quotientRing A I n) ⋙ U.finiteRestriction A I n :=
  letI := (siteRestrictScalars_exact (ConstantCompletion.quotient V.topology A I n)).1
  letI := (siteRestrictScalars_exact (ConstantCompletion.quotient V.topology A I n)).2
  letI := (siteRestrictScalars_exact (ConstantCompletion.quotient U.topology A I n)).1
  letI := (siteRestrictScalars_exact (ConstantCompletion.quotient U.topology A I n)).2
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (f.finiteModuleRestrictionPullIso A I n) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The canonical finite-coefficient realization of the evaluated source B.
It uses evaluation of direct image, quotient evaluation, and the actual finite
restriction comparisons. It does not refer to either exchange transformation.
Source: Stacks 0941, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def finiteSourceIso {f : Morphism Y X} {g : Morphism Y Y'}
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) (K : X.derived A) :
    (Y'.evaluate A n).obj
        ((g.towerPull A).obj ((f.towerPush A).obj ((X.reduction A I).obj K))) ≅
      (Y'.finiteRestriction A I n).obj
        ((g.pull (quotientRing A I n)).obj
          ((f.push (quotientRing A I n)).obj ((X.finiteReduction A I n).obj K))) :=
  (g.evaluatePullIso A n).app ((f.towerPush A).obj ((X.reduction A I).obj K)) ≪≫
    (g.pull A).mapIso ((f.evaluatePushIso A n).app ((X.reduction A I).obj K)) ≪≫
    (g.pull A).mapIso ((f.push A).mapIso ((X.finiteEvaluationIso A I n).app K)) ≪≫
    (g.pull A).mapIso ((f.finiteRestrictionPushIso A I n).app
      ((X.finiteReduction A I n).obj K)) ≪≫
    (g.finiteRestrictionPullIso A I n).app
      ((f.push (quotientRing A I n)).obj ((X.finiteReduction A I n).obj K))

/-- The analogous finite-coefficient realization of the evaluated target D,
constructed independently of the exchange maps.
Source: Stacks 0941, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def finiteTargetIso {h : Morphism X X'} {k : Morphism Y' X'}
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) (K : X.derived A) :
    (Y'.evaluate A n).obj
        ((k.towerPush A).obj ((h.towerPull A).obj ((X.reduction A I).obj K))) ≅
      (Y'.finiteRestriction A I n).obj
        ((k.push (quotientRing A I n)).obj
          ((h.pull (quotientRing A I n)).obj ((X.finiteReduction A I n).obj K))) :=
  (k.evaluatePushIso A n).app ((h.towerPull A).obj ((X.reduction A I).obj K)) ≪≫
    (k.push A).mapIso ((h.evaluatePullIso A n).app ((X.reduction A I).obj K)) ≪≫
    (k.push A).mapIso ((h.pull A).mapIso ((X.finiteEvaluationIso A I n).app K)) ≪≫
    (k.push A).mapIso ((h.finiteRestrictionPullIso A I n).app
      ((X.finiteReduction A I n).obj K)) ≪≫
    (k.finiteRestrictionPushIso A I n).app
      ((h.pull (quotientRing A I n)).obj ((X.finiteReduction A I n).obj K))

/-- The finite projection map with coefficients retained in A/I^(n+1), obtained by
transposing finite tensor/pullback comparison followed by the ordinary derived counit.
Source: Stacks 0B56, 0944 (blueprint: lem-sp-completion-mate-comparison). -/
def Morphism.finiteProjection {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) (K : U.derived A) :
    (V.finiteReduction A I n).obj ((f.push A).obj K) ⟶
      (f.push (quotientRing A I n)).obj ((U.finiteReduction A I n).obj K) :=
  (f.adj (quotientRing A I n)).homEquiv _ _
    ((f.finitePullIso A I n).inv.app ((f.push A).obj K) ≫
      (U.finiteReduction A I n).map ((f.adj A).counit.app K))

/-- The finite projection comparison corresponding to H, before scalar restriction.
Source: Stacks 0B56, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def finiteProjectionComparison {f : Morphism Y X} {g : Morphism Y Y'}
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ) (K : X.derived A) :
    (Y'.finiteReduction A I n).obj ((g.pull A).obj ((f.push A).obj K)) ⟶
      (g.pull (quotientRing A I n)).obj
        ((f.push (quotientRing A I n)).obj ((X.finiteReduction A I n).obj K)) :=
  (g.finitePullIso A I n).hom.app ((f.push A).obj K) ≫
    (g.pull (quotientRing A I n)).map (f.finiteProjection A I n K)

/-- Naturality needed to form s as an actual natural transformation.
Source: Stacks 0B56, 099M (blueprint: lem-sp-completion-mate-comparison).
Proof: reductionPullIso is natural, the derived counit is natural, and transposition
is natural in both arguments. Hence towerProjection and H are natural in K. Apply
the limit functor and restrict to the complete full subcategory. -/
theorem comparisonS_naturality {f : Morphism Y X} {g : Morphism Y Y'}
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (K L : X.Complete A I) (a : K ⟶ L) :
    (f.completePush A I ⋙ g.completePull A I ⋙
        ObjectProperty.ι (Y'.IsComplete A I)).map a ≫
        (Y'.rlim A).map (projectionComparison (f := f) (g := g) A I L.obj) =
      (Y'.rlim A).map (projectionComparison (f := f) (g := g) A I K.obj) ≫
        (ObjectProperty.ι (X.IsComplete A I) ⋙ X.reduction A I ⋙
          f.towerPush A ⋙ g.towerPull A ⋙ Y'.rlim A).map a := by
  sorry

/-- The specified map s, namely total derived inverse limit of H.
Source: Stacks 099M, 0E48 (blueprint: lem-sp-completion-mate-comparison). -/
def comparisonS {f : Morphism Y X} {g : Morphism Y Y'}
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    f.completePush A I ⋙ g.completePull A I ⋙ ObjectProperty.ι (Y'.IsComplete A I) ⟶
      ObjectProperty.ι (X.IsComplete A I) ⋙ X.reduction A I ⋙
        f.towerPush A ⋙ g.towerPull A ⋙ Y'.rlim A where
  app K := (Y'.rlim A).map (projectionComparison (f := f) (g := g) A I K.obj)
  naturality K L a := comparisonS_naturality A I K L a

/-- The prescribed direct-image/limit comparison at K, with the reduction/pullback
identification inserted. Its definition is independent of either exchange map.
Source: Stacks 0941, 0A07 (blueprint: lem-sp-completion-mate-comparison). -/
def comparisonTComponent {h : Morphism X X'} {k : Morphism Y' X'}
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (K : X.Complete A I) :
    ((h.completePull A I ⋙ k.completePush A I ⋙
      ObjectProperty.ι (Y'.IsComplete A I)).obj K) ≅
    ((ObjectProperty.ι (X.IsComplete A I) ⋙ X.reduction A I ⋙
      h.towerPull A ⋙ k.towerPush A ⋙ Y'.rlim A).obj K) :=
  (k.directLimitIso A).app ((X'.reduction A I).obj ((h.pull A).obj K.obj)) ≪≫
    (Y'.rlim A).mapIso ((k.towerPush A).mapIso ((h.reductionPullIso A I).symm.app K.obj))

/-- Naturality of the specified t components.
Source: Stacks 0941, 0A07 (blueprint: lem-sp-completion-mate-comparison).
Proof: directLimitIso and reductionPullIso are natural isomorphisms. Their
whiskerings and composite remain natural; restrict this equality to complete inputs. -/
theorem comparisonT_naturality {h : Morphism X X'} {k : Morphism Y' X'}
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (K L : X.Complete A I) (a : K ⟶ L) :
    (h.completePull A I ⋙ k.completePush A I ⋙
        ObjectProperty.ι (Y'.IsComplete A I)).map a ≫
        (comparisonTComponent (h := h) (k := k) A I L).hom =
      (comparisonTComponent (h := h) (k := k) A I K).hom ≫
        (ObjectProperty.ι (X.IsComplete A I) ⋙ X.reduction A I ⋙
          h.towerPull A ⋙ k.towerPush A ⋙ Y'.rlim A).map a := by
  sorry

/-- The specified natural direct-image/limit comparison t.
Source: Stacks 0941, 0A07 (blueprint: lem-sp-completion-mate-comparison). -/
def comparisonT {h : Morphism X X'} {k : Morphism Y' X'}
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    h.completePull A I ⋙ k.completePush A I ⋙ ObjectProperty.ι (Y'.IsComplete A I) ≅
      ObjectProperty.ι (X.IsComplete A I) ⋙ X.reduction A I ⋙
        h.towerPull A ⋙ k.towerPush A ⋙ Y'.rlim A :=
  NatIso.ofComponents (comparisonTComponent A I)
    (fun a ↦ comparisonT_naturality A I _ _ a)

/-- The whole-diagram mate comparison, including invertibility and the two finite
coefficient normalization clauses.

Source: smooth-purity blueprint, fix-lem-exchanges Proof Step 4; ingredient sources
Stacks 099M, 099N, 0E48, 0941, 0B56, 0944
(blueprint: lem-sp-completion-mate-comparison).

Proof, following the ten steps of the DAG node:
1. Realize the strict sequence category on the diagram site. Use one flat-term
K-flat model for K and tensor it with the whole strict quotient diagram; its diagonal
is K-flat by levelwise acyclicity. This identifies the reduction/pullback comparisons.
2. The constant-tower functor preserves K-injectives, since evaluation at its terminal
index is exact and left adjoint to it. Its derived units and counits are the ordinary
ones termwise. The derived quotient augmentation therefore gives exactly the fixed
completion unit.
3. Evaluation of the strict projection adjunct gives finiteProjection. Each quotient
is perfect, hence has a bounded finite-projective model. Constant sheafification and
inverse image preserve its finite-free retracts. The finite total projection formula
makes every evaluated projection invertible; levelwise cohomology detects its cone.
Thus H is invertible and has the stated finite evaluation.
4. The identity-component constant/pullback square gives directLimitIso by adjunction
conjugation. On a K-injective strict tower it is the ordinary direct-image/limit map;
its projections are the direct images of the tower projections. This is t.
5. Apply ringedExchangeTensorCoherence on the diagram sites with the diagonal of K
and the whole quotient diagram. The diagram exchange on the diagonal is the diagonal
of the ordinary mate. The resulting equality holds before any evaluation or limit.
6. Naturality of the projection adjunct in the coefficient, and its tensor-unit
normalization, identify its composition with the quotient augmentation with direct
image of that augmentation. Apply total derived limit to obtain the corresponding
completion-unit equation.
7. The strict expression t inverse followed by limit(v) followed by s extends the
ordinary mate followed by the completed target unit. Completeness of that target
and direct-image preservation give uniqueness of this extension.
8. For each pair of edges, transpose under the ordinary and completion adjunctions.
The comparison C(v^* unit) is invertible by reflection and preservation of complete
objects under direct image. This calculation identifies the completed pullback square
with the conjugate of the prescribed right-adjoint square, including units and counits.
9. Transpose the completed mate and precompose with the completion unit. The triangle
identities give the same extension as in step 7. Uniqueness proves the displayed
natural-transformation equality, not merely equality of evaluated tower maps.
10. Evaluate the strict derived adjunction on a K-injective tower and use its exact
left adjoint. Finite scalar restriction commutes with direct image by adjunction
conjugation and with inverse image on generalized sections. These comparisons turn
the evaluated tower mate into ordinaryExchange over the original quotient ring.
No properness, smoothness, constructibility, boundedness or etale-origin condition
is used. Empty sites, the zero ideal and the unit ideal are included. -/
theorem completionMateComparison
    {f : Morphism Y X} {g : Morphism Y Y'} {h : Morphism X X'} {k : Morphism Y' X'}
    (sq : Square f g h k) (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (_hperfect : PerfectQuotients A I) :
    (∀ K : X.Complete A I,
      IsIso (projectionComparison (f := f) (g := g) A I K.obj)) ∧
    (∀ (K : X.Complete A I) (n : ℕ),
      (Y'.evaluate A n).map (projectionComparison (f := f) (g := g) A I K.obj) ≫
          (finiteSourceIso (f := f) (g := g) A I n K.obj).hom =
        (Y'.finiteEvaluationIso A I n).hom.app ((g.pull A).obj ((f.push A).obj K.obj)) ≫
          (Y'.finiteRestriction A I n).map
            (finiteProjectionComparison (f := f) (g := g) A I n K.obj)) ∧
    (Functor.whiskerRight (completeExchange sq A I) (ObjectProperty.ι (Y'.IsComplete A I)) ≫
        (comparisonT (h := h) (k := k) A I).hom =
      comparisonS (f := f) (g := g) A I ≫
        Functor.whiskerRight
          (Functor.whiskerLeft (ObjectProperty.ι (X.IsComplete A I) ⋙ X.reduction A I)
            (towerExchange sq A)) (Y'.rlim A)) ∧
    (∀ (K : X.Complete A I) (n : ℕ),
      (Y'.evaluate A n).map ((towerExchange sq A).app ((X.reduction A I).obj K.obj)) ≫
          (finiteTargetIso (h := h) (k := k) A I n K.obj).hom =
        (finiteSourceIso (f := f) (g := g) A I n K.obj).hom ≫
          (Y'.finiteRestriction A I n).map
            ((ordinaryExchange sq (quotientRing A I n)).app
              ((X.finiteReduction A I n).obj K.obj))) := by
  sorry

end CategoryTheory.AdicSites
