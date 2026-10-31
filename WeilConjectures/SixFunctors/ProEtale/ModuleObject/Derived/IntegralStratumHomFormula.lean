/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralDerivedCoefficientData
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Triangulated.Triangulated
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Data.Fin.Tuple.Basic
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportSheaves
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableShortExact
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLisseProEtaleLocality
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoverRestrictionConservative
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstantModelLocalResolution
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteConstantModelsCommonStratification
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteConstantModelStrataGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Integral stratum filtrations and the global derived Hom formula

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-int-ext,
sk-lem-int-ext-formula.md and its proof, clauses (1)--(2)
(blueprint: det-lem-int-ext-formula).

The coefficients, constructibility, ordinary relative derived tensor and internal Hom
are the recorded constructions. Global sections are Hom from the regular module,
as in the ringed-site hypercohomology definition, here in the module-object encoding.
The inverse-limit clause uses strict towers of complexes and the recorded Roos triangle.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types true
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u v w w'

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj
open ZeroObject

attribute [local irreducible] DerivedCategory.monoidalClosed Mod.monoidalClosed

attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStar lowerStar upperStarComp lowerStarComp
  openImmersionLowerShriek




/-- Derived global sections for modules over a condensed coefficient ring.
Source: blueprint det-lem-int-ext-formula, global-sections convention
(blueprint: det-lem-int-ext-formula). -/
abbrev stratumModuleDerivedSections
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] (X : Scheme.{u}) :=
  (preadditiveCoyoneda.obj (op (Mod.regular (condensedRingObj Λ X))) :
    supportModules Λ X ⥤ Ab.{u + 1}).rightDerivedFunctor

/-- The uncompleted derived dual, with the coefficient ring kept abstract.
Source: blueprint det-lem-int-ext-formula, clause (2)
(blueprint: det-lem-int-ext-formula). -/
def stratumModuleDual
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (S : Scheme.{u}) (L : supportModules Λ S) :=
  ((derivedHom Λ S).obj (op ((DerivedCategory.singleFunctor _ 0).obj L))).obj
    (𝟙_ (DerivedCategory (supportModules Λ S)))

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
