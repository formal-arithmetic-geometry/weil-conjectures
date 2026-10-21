/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.Paper.SectionDerivedRealization
public import Sheaf.Paper.CondensedModuleDerivedPushpull
import Sheaf.Topology.ProfiniteCondensedRing
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.Paper.SectionModuleOperationsData
import Sheaf.Paper.RingedTopoiDerivedPullback
import Sheaf.Paper.ProjectionMateExact
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
import Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.SixFunctors.ResolvingDerivedAdjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-! # Normalization of derived section push-pull

Source: Stacks Project, `derived.tex`, Tags 09T5 and 08BJ, and
`sites-cohomology.tex`, Tags 07A6 and 0FPI
(blueprint: lem-pd-section-derived-pushpull-normalization).

The statement records the comparison of the fixed internal module operations with
the section-module operations after passage to derived categories.  All functors,
equivalences, and comparison maps are the constructions imported from the preceding
section-module modules.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.all false
set_option linter.unusedVariables false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)]

/-- The existing internal derived adjunction with its two functor types fixed explicitly.
Source: Stacks 09T5 and 07A6
(blueprint: lem-pd-section-derived-pushpull-normalization). -/
def normalizationInternalAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    internalDerivedPullback Λ f ⊣ internalDerivedPushforward Λ f :=
  CondensedRing.derivedUpperStarLowerStarAdjunction Λ f

/--
Source: Stacks Project, `derived.tex`, Tags 09T5 and 08BJ, and
`sites-cohomology.tex`, Tags 07A6 and 0FPI
(blueprint: lem-pd-section-derived-pushpull-normalization).

Proof, following the eight steps of the node.
1. The ordinary internal-module-operations transport makes E and its inverse
   additive and exact. Localize their termwise actions, units, and counits by
   exact-functor factorization and the localization universal property; the
   triangle identities descend, giving the specified derived equivalence.
2. Each equivalence functor is right adjoint to its exact inverse. Right-adjoint
   preservation of K-injectives gives both implications. Exactness preserves and
   reflects quasi-isomorphisms, identifying K-injective resolutions. The ringed
   resolution-existence theorem supplies enough K-injectives. Maps and homotopies
   are sent degreewise, and K-injective Hom localization identifies the resulting
   derived resolution comparisons.
3. Retain the identity-on-sections pushforward comparison and its specified mate.
   Condensed module pullback is exact, and ordinary transport makes section
   pullback exact. Exact-functor factorization and its derived universal property
   identify both specified left derived functors with their degreewise descents.
   Their right adjoints preserve K-injectives.
4. Apply exactEquivalenceDerivedSquares to these four ordinary functors and the
   independently specified total derived pairs. Their universal transformations
   give the displayed resolution comparison equations. On K-injectives the right
   derived unit is invertible, so the comparison is the localized ordinary map.
5. Termwise adjunction descends to homotopy classes. Apply the resolving derived
   adjunction normalization with all complexes as left resolving class, since
   pullback is exact. For t : P(M) → I its transpose is the class of the ordinary
   transpose followed by the right comparison. Maps into K-injectives represent
   every derived Hom class. The specified derived adjunction has the same counit
   factorization by the theorem deriving an adjunction from its ordinary one;
   invertibility of the right comparison on I identifies their counits everywhere.
6. Localize the ordinary Hom-transposition comparison and insert Step 4's two
   equations into Step 5's formula. This gives the Hom identity below. Evaluate
   the Hom bijections and their inverses on identities to obtain the displayed
   unit and counit equations for the independently derived adjunctions.
7. The two ordinary geometric pushforward compositors commute with the section
   comparisons: both act by the same fibre-product associator on sections.
   Mate pasting and the bijection of adjunction mates give the corresponding
   ordinary pullback composition square.
8. The internal left-derived compositor is localization of the ordinary one, as
   is the section compositor since pullback is exact. Localize Step 7 and insert
   Step 4 to obtain the displayed pullback composition square. The localization
   universal property extends it to every derived object. Mate pasting, using
   the unit and counit equations of Step 6, gives the final right compositor
   square with the specified adjunction mates.
-/
theorem sectionDerivedPushpullNormalization {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedFunctor Λ X).IsEquivalence ∧
    (derivedFunctor Λ Y).IsEquivalence ∧
    (∀ T : Scheme.{u}, ∀ P : CochainComplex (internalModules Λ T) ℤ,
      CochainComplex.IsKInjective
          (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P) ↔
        P.IsKInjective) ∧
    (∀ (T : Scheme.{u}) (P I : CochainComplex (internalModules Λ T) ℤ) (i : P ⟶ I),
      (QuasiIso (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).map i) ∧
        CochainComplex.IsKInjective
          (((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj I)) ↔
        (QuasiIso i ∧ I.IsKInjective)) ∧
    (∀ P : CochainComplex (internalModules Λ Y) ℤ,
      (derivedPullComparison Λ f).hom.app (DerivedCategory.Q.obj P) ≫
          (derivedPullback Λ f).map (sectionLocalizationComparison Λ Y P).hom ≫
          (pullback Λ f).mapDerivedCategoryFactors.hom.app
            (((equivalence Λ Y).functor.mapHomologicalComplex (.up ℤ)).obj P) =
        (derivedEquivalence Λ X).functor.map
            ((CondensedRing.upperStar Λ f).leftDerivedFunctorCounit.app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
          (sectionLocalizationComparison Λ X
            (((CondensedRing.upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj P)).hom ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
            (pullComparison Λ f) (.up ℤ)).hom.app P)) ∧
    (∀ P : CochainComplex (internalModules Λ X) ℤ,
      (derivedEquivalence Λ Y).functor.map
          ((CondensedRing.lowerStar Λ f).rightDerivedFunctorUnit.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
          (derivedPushComparison Λ f).hom.app (DerivedCategory.Q.obj P) ≫
          (derivedPushforward Λ f).map (sectionLocalizationComparison Λ X P).hom =
        (sectionLocalizationComparison Λ Y
            (((CondensedRing.lowerStar Λ f).mapHomologicalComplex (.up ℤ)).obj P)).hom ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
            (pushComparison Λ f) (.up ℤ)).hom.app P) ≫
          (pushforward Λ f).rightDerivedFunctorUnit.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj
              (((equivalence Λ X).functor.mapHomologicalComplex (.up ℤ)).obj P))) ∧
    (∀ (M : DerivedCategory (internalModules Λ Y))
      (N : DerivedCategory (internalModules Λ X))
      (q : (internalDerivedPullback Λ f).obj M ⟶ N),
      (derivedAdjunction Λ f).homEquiv _ _
          ((derivedPullComparison Λ f).inv.app M ≫
            (derivedEquivalence Λ X).functor.map q) =
        (derivedEquivalence Λ Y).functor.map
            ((normalizationInternalAdjunction Λ f).homEquiv _ _ q) ≫
          (derivedPushComparison Λ f).hom.app N) ∧
    (∀ (M : DerivedCategory (internalModules Λ Y)),
      (derivedAdjunction Λ f).unit.app ((derivedEquivalence Λ Y).functor.obj M) =
        (derivedEquivalence Λ Y).functor.map
            ((normalizationInternalAdjunction Λ f).unit.app M) ≫
          (derivedPushComparison Λ f).hom.app ((internalDerivedPullback Λ f).obj M) ≫
          (derivedPushforward Λ f).map ((derivedPullComparison Λ f).hom.app M)) ∧
    (∀ (N : DerivedCategory (internalModules Λ X)),
      (derivedAdjunction Λ f).counit.app ((derivedEquivalence Λ X).functor.obj N) =
        (derivedPullback Λ f).map ((derivedPushComparison Λ f).inv.app N) ≫
          (derivedPullComparison Λ f).inv.app ((internalDerivedPushforward Λ f).obj N) ≫
          (derivedEquivalence Λ X).functor.map
            ((normalizationInternalAdjunction Λ f).counit.app N)) ∧
    (∀ {Z : Scheme.{u}} (g : Y ⟶ Z)
      (M : DerivedCategory (internalModules Λ Z)),
      (derivedPullComparison Λ (f ≫ g)).hom.app M ≫
          (derivedPullbackComposition Λ f g).hom.app
            ((derivedEquivalence Λ Z).functor.obj M) =
        (derivedEquivalence Λ X).functor.map
            ((CondensedRing.leftDerivedUpperStarComp Λ f g).hom.app M) ≫
          (derivedPullComparison Λ f).hom.app
            ((internalDerivedPullback Λ g).obj M) ≫
          (derivedPullback Λ f).map
            ((derivedPullComparison Λ g).hom.app M)) ∧
    (∀ {Z : Scheme.{u}} (g : Y ⟶ Z)
      (N : DerivedCategory (internalModules Λ X)),
      (derivedEquivalence Λ Z).functor.map
          ((conjugateEquiv
            ((normalizationInternalAdjunction Λ g).comp
              (normalizationInternalAdjunction Λ f))
            (normalizationInternalAdjunction Λ (f ≫ g))
            (CondensedRing.leftDerivedUpperStarComp Λ f g).hom).app N) ≫
          (derivedPushComparison Λ (f ≫ g)).hom.app N =
        (derivedPushComparison Λ g).hom.app ((internalDerivedPushforward Λ f).obj N) ≫
          (derivedPushforward Λ g).map ((derivedPushComparison Λ f).hom.app N) ≫
          (conjugateEquiv ((derivedAdjunction Λ g).comp (derivedAdjunction Λ f))
            (derivedAdjunction Λ (f ≫ g)) (derivedPullbackComposition Λ f g).hom).app
              ((derivedEquivalence Λ X).functor.obj N)) := by
  sorry

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
