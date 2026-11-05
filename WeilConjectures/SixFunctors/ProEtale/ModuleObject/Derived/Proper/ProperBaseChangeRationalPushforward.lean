/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructibleBaseChange
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap

public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ChangeOfCoefficients

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizedDirectImageComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.Compatibility

/-!
# Proper direct image with rational condensed coefficients: coefficient comparisons

Source: current blueprint, sec-six-functors-basics,
sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-rational.md, clauses 1--2
(blueprint: det-thm-sfb-proper-base-change-rational).

The first part of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeRational`,
split off for compile time: the
canonical rationalization push comparison, the named preservation proofs for the two rational
coefficient cases, the three bounded-below coefficient comparisons of clause 1 and preservation
of bounded constructibility (clause 2).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStarFromPoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  derivedPushSource derivedPushTarget derivedPushHom
  moduleObjectProjectionMap
  DerivedCategory HasDerivedCategory.standard CategoryTheory.Mod.monoidalCategory

/-- The canonical push comparison for the coefficient inclusion O_E -> E. Its definition
only supplies the flatness proof to the recorded `derivedPushHom`; it does not choose a map.
Source: blueprint rational proper direct image, clause 1, and its proof steps 1--2
(blueprint: det-thm-sfb-proper-base-change-rational). -/
def rationalizationPushHom (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) {X Y : Scheme.{u}} (p : X ⟶ Y) :
    (lowerStar (Profinite.padicIntegersRingObj ℓ E.1) p).rightDerivedFunctor ⋙
        (Mod.extendScalars (padicIntegersToPadicSubfield Y ℓ E)).leftDerivedFunctor ⟶
      (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor ⋙
        (lowerStar (Profinite.continuousMapRingObj E) p).rightDerivedFunctor :=
  letI : ∀ Z : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (padicIntegersRingObjToContinuousMapRingObj ℓ E) Z)) :=
    fun Z ↦ Exists.elim (padicIntegers_invertEll Z ℓ E) fun _ hj ↦
      Exists.elim hj.2 fun _ ht ↦ Exists.elim ht.2.2 fun _ hα ↦ hα.2.2.2
  derivedPushHom (padicIntegersRingObjToContinuousMapRingObj ℓ E) p

/-- The existing finiteness preservation proof for `ℚ̄_ℓ`, named to avoid repeated expansion
in the canonical restricted base-change map. This supplies a proof, never extra map data.
Source: blueprint rational proper direct image, clauses 2--3
(blueprint: det-thm-sfb-proper-base-change-rational). -/
abbrev rationalFinitenessPushforwardPreservation (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] :
    PreservesBoundedConstructiblePushforwards (Profinite.padicAlgClRingObj ℓ) k :=
  fun f K ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ f K

/-- The existing finiteness preservation proof for a finite subextension `E`, named to avoid
repeated expansion in the canonical restricted base-change map.
Source: blueprint rational proper direct image, clauses 2--3
(blueprint: det-thm-sfb-proper-base-change-rational). -/
abbrev ContinuousMapRingObj.rationalFinitenessPushforwardPreservation (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] :
    PreservesBoundedConstructiblePushforwards (Profinite.continuousMapRingObj E) k :=
  fun f K ↦ ContinuousMapRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ E f K

attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

attribute [local irreducible] rationalizationPushHom
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  Functor.mapDerivedCategory

/-- The named preservation proof for precisely the two rational coefficient cases.
The bundled ring equality fixes multiplication as well as the underlying coefficient sheaf.
Source: blueprint rational proper direct image, clauses 2--3
(blueprint: det-thm-sfb-proper-base-change-rational). -/
abbrev rationalCoefficientPushforwardPreservation
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Λ = Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] :
    PreservesBoundedConstructiblePushforwards Λ.X k := by
  rcases hΛ with ⟨E, hE⟩ | hQ
  · subst Λ
    exact ContinuousMapRingObj.rationalFinitenessPushforwardPreservation ℓ E
  · subst Λ
    exact rationalFinitenessPushforwardPreservation ℓ

set_option allowUnsafeReducibility true in
attribute [local irreducible] rationalCoefficientPushforwardPreservation
  rationalFinitenessPushforwardPreservation
  ContinuousMapRingObj.rationalFinitenessPushforwardPreservation

attribute [local irreducible] derivedTensor moduleObjectProjectionData

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (p : X ⟶ Y) [IsProper p.left]

end AlgebraicGeometry.ProEtale.CondensedRing
