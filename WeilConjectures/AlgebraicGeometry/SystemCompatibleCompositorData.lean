/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.SemilinearDerivedSections
public import WeilConjectures.SixFunctors.SemilinearProperOpenMatePasting
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleEncoding
public import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstructibleOrigin
public import WeilConjectures.AlgebraicGeometry.CanonicalOriginCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.CompatibleCompactificationTriangle
public import WeilConjectures.AlgebraicGeometry.CompactSupportNativeSystemEvaluation
public import WeilConjectures.AlgebraicGeometry.CompactSupportSiteCoherence
public import WeilConjectures.AlgebraicGeometry.FiniteSiteTowerPaste
public import WeilConjectures.AlgebraicGeometry.FiniteConstantCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.StrictConstantTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.StrictTowerOpenExtension
public import WeilConjectures.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
public import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
public import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsSupplement
public import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.RingedToposRingData
public import WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.GeometricRingTransport
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
public import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
public import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-! # Compatible-triangle normalization of the system compositor

Source: Stacks Project, more-etale.tex, Tag 0F7J, lemma-shriek-composition,
first paragraph and four displayed identifications; simultaneous-system construction
(blueprint: lem-pur-system-compatible-compositor-normalization).
-/

@[expose] public noncomputable section
attribute [-instance] WeilConjectures.scalarReductionSiteSmall
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen

variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)

/-- The actual three-factor proper/open word, on the ordinary derived system category.
Source: Stacks 0F7J, the four displayed identifications
(blueprint: lem-pur-system-compatible-compositor-normalization). -/
def compatibleCompositorWord {X V XB Y YB Z : Scheme.{u}}
    (j : X ⟶ V) (b : V ⟶ XB) (q : V ⟶ Y) (p : XB ⟶ YB)
    (i : Y ⟶ YB) (s : YB ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion b] [IsOpenImmersion i]
    [QuasiCompact b] [QuasiCompact i] [IsProper q] [IsProper p]
    (h : b ≫ p = q ≫ i) :
    (J C τ j ⋙ R C τ q) ⋙ (J C τ i ⋙ R C τ s) ⟶
      J C τ (j ≫ b) ⋙ R C τ (p ≫ s) :=
  (Functor.associator (J C τ j) (R C τ q) (J C τ i ⋙ R C τ s)).hom ≫
    Functor.whiskerLeft (J C τ j)
      ((Functor.associator (R C τ q) (J C τ i) (R C τ s)).inv ≫
        Functor.whiskerRight (gamma C τ b q p i h) (R C τ s) ≫
        (Functor.associator (J C τ b) (R C τ p) (R C τ s)).hom ≫
        Functor.whiskerLeft (J C τ b) (sComp C τ p s).hom) ≫
    (Functor.associator (J C τ j) (J C τ b) (R C τ (p ≫ s))).inv ≫
    Functor.whiskerRight (jComp C τ j b).hom (R C τ (p ≫ s))

/-- The n-th level in the same constant-ring module presentation used by the mate API.
Source: Zheng 4.1, 4.10; Stacks 0F7J
(blueprint: lem-pur-system-compatible-compositor-normalization). -/
abbrev compositorLevel (X : Scheme.{u}) (n : ℕ) :=
  E C τ n X ⋙ StrictTower.ev (C n) X 0

end AlgebraicGeometry.ProEtale.SemilinearProperOpen

namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen

variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)

/-- Open evaluation, including the constant-tower presentation comparison.
Source: Zheng 4.10; Stacks 03DI
(blueprint: lem-pur-system-compatible-compositor-normalization). -/
def compositorLevelJ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    J C τ j ⋙ compositorLevel C τ X n ≅ compositorLevel C τ U n ⋙
      (StrictTower.moduleJ (C n) j).mapDerivedCategory :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (evalJ C τ n j) (StrictTower.ev (C n) X 0) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (E C τ n U) (StrictTower.evalJ (C n) j 0) ≪≫
    (Functor.associator _ _ _).symm

/-- Direct-image evaluation with its prescribed adjunction mate.
Source: Zheng 4.10; Stacks 07A4
(blueprint: lem-pur-system-compatible-compositor-normalization). -/
def compositorLevelR {U X : Scheme.{u}} (q : U ⟶ X) (n : ℕ) :
    R C τ q ⋙ compositorLevel C τ X n ≅ compositorLevel C τ U n ⋙
      (StrictTower.moduleDirectImage (C n) q).rightDerivedFunctor :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (@asIso _ _ _ _ (evalR C τ n q) (evalR_isIso C τ n q))
      (StrictTower.ev (C n) X 0) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (E C τ n U)
      (@asIso _ _ _ _ (StrictTower.evalR (C n) q 0) (StrictTower.evalR_isIso (C n) q 0)) ≪≫
    (Functor.associator _ _ _).symm

/-- The canonical comparison for one compact-support factor, retaining both evaluations.
Source: Stacks 0F7J; Zheng 4.10
(blueprint: lem-pur-system-compatible-compositor-normalization). -/
def compositorSupportEvaluation {X V Y : Scheme.{u}} (j : X ⟶ V) (q : V ⟶ Y)
    [IsOpenImmersion j] (n : ℕ) :
    (J C τ j ⋙ R C τ q) ⋙ compositorLevel C τ Y n ≅
      compositorLevel C τ X n ⋙ ((StrictTower.moduleJ (C n) j).mapDerivedCategory ⋙
        (StrictTower.moduleDirectImage (C n) q).rightDerivedFunctor) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (J C τ j) (compositorLevelR C τ q n) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (compositorLevelJ C τ j n)
      (StrictTower.moduleDirectImage (C n) q).rightDerivedFunctor ≪≫
    Functor.associator _ _ _

/-- Transport one compact-support factor using the canonical proper mate and open unit.
The supplied input identification is propagated functorially, never replaced by a choice.
Source: Stacks 099R, 09AF and 0F7J
(blueprint: lem-pur-system-compatible-compositor-normalization). -/
def compositorSupportTransport {X V Y : Scheme.{u}} (j : X ⟶ V) (q : V ⟶ Y)
    [IsOpenImmersion j] [IsProper q] (n : ℕ)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]
    (φ : C n →+* Λ) (L : FiniteSiteTower.DE Λ X) (M : Derived C τ X)
    (e : (StrictTower.HD (C n) X Λ φ).obj L ≅ (compositorLevel C τ X n).obj M) :
    (StrictTower.HD (C n) Y Λ φ).obj
        ((FiniteSiteTower.PE Λ q).obj ((FiniteSiteTower.JE Λ j).obj L)) ≅
      (compositorLevel C τ Y n).obj ((J C τ j ⋙ R C τ q).obj M) :=
  (@asIso _ _ _ _ (StrictTower.hR (C n) q Λ φ)
      (StrictTower.hR_isIso (C n) q Λ φ)).app ((FiniteSiteTower.JE Λ j).obj L) ≪≫
    (StrictTower.moduleDirectImage (C n) q).rightDerivedFunctor.mapIso
      ((StrictTower.hJ (C n) j Λ φ).app L) ≪≫
    ((StrictTower.moduleJ (C n) j).mapDerivedCategory ⋙
      (StrictTower.moduleDirectImage (C n) q).rightDerivedFunctor).mapIso e ≪≫
    (compositorSupportEvaluation C τ j q n).symm.app M

end AlgebraicGeometry.ProEtale.SemilinearProperOpen

namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen

variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)

/-- Input transport for the iterated compact-support word, with all four geometric factors.
Source: Stacks 0F7J, 099R and 09AF
(blueprint: lem-pur-system-compatible-compositor-normalization). -/
def compositorFiniteSource {X V Y YB Z : Scheme.{u}}
    (j : X ⟶ V) (q : V ⟶ Y) (i : Y ⟶ YB) (s : YB ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion i] [IsProper q] [IsProper s]
    (n : ℕ) (M : Derived C τ X)
    (w : StrictTower.ScalarEtaleOrigin (C n) X ((compositorLevel C τ X n).obj M)) :=
  compositorSupportTransport C τ i s n w.Λ w.φ
    ((FiniteSiteTower.PE w.Λ q).obj ((FiniteSiteTower.JE w.Λ j).obj w.origin.L))
    ((J C τ j ⋙ R C τ q).obj M)
    (compositorSupportTransport C τ j q n w.Λ w.φ w.origin.L M
      (StrictTower.originIso (C n) w))

/-- Output transport for the composite compactification, using the very same origin witness.
Source: Stacks 0F7J, 099R and 09AF
(blueprint: lem-pur-system-compatible-compositor-normalization). -/
def compositorFiniteTarget {X V XB YB Z : Scheme.{u}}
    (j : X ⟶ V) (b : V ⟶ XB) (p : XB ⟶ YB) (s : YB ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion b] [IsProper p] [IsProper s]
    (n : ℕ) (M : Derived C τ X)
    (w : StrictTower.ScalarEtaleOrigin (C n) X ((compositorLevel C τ X n).obj M)) :=
  compositorSupportTransport C τ (j ≫ b) (p ≫ s) n w.Λ w.φ w.origin.L M
    (StrictTower.originIso (C n) w)

end AlgebraicGeometry.ProEtale.SemilinearProperOpen

namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen

/-- Bounded constructibility at one level, using the recorded fixed-module predicate.
The interval belongs to this level only. Source: blueprint, the domain of the compositor
(blueprint: lem-pur-system-compatible-compositor-normalization). -/
def compositorBoundedConstructible (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (K : _root_.DerivedCategory (StrictTower.Modules (ULift.{u + 1, u} A) X)) : Prop :=
  (∀ r : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf X (ULift.{u + 1, u} A)
    ((Scheme.proEtaleModuleRestriction X A).obj
      ((_root_.DerivedCategory.homologyFunctor _ r).obj K))) ∧
    ∃ a b : ℤ, a ≤ b ∧ ∀ r : ℤ, (r < a ∨ b < r) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ r).obj K)

variable (l : ℕ) [Fact l.Prime] (E₀ : Type u) [Field E₀]
  [Algebra (Padic l) E₀] [FiniteDimensional (Padic l) E₀]

/-- The full levelwise bounded constructible domain; there is no uniform bound,
normalization or Tor-amplitude requirement. Source: blueprint, final sentence
(blueprint: lem-pur-system-compatible-compositor-normalization). -/
def compatibleCompositorDomain (X : Scheme.{u})
    (M : Derived (compactSupportSystemLevel l E₀) (compactSupportSystemQuotient l E₀) X) :
    Prop :=
  ∀ n : ℕ, @compositorBoundedConstructible X
    (Padic.coefficientExtensionRing l E₀ (n + 1)) _
    (Padic.finite_coefficientExtensionRing l E₀ (n + 1) (Nat.succ_pos n))
    ((compositorLevel (compactSupportSystemLevel l E₀)
      (compactSupportSystemQuotient l E₀) X n).obj M)

end AlgebraicGeometry.ProEtale.SemilinearProperOpen
