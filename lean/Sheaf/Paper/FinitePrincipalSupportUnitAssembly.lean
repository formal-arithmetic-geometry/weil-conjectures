/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q154
-/
module

public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Adjunction.Mates

import Sheaf.AlgebraicGeometry.CondensedModulePullbackExact
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Finite principal-support assembly of the specified derived open unit

Source: Stacks Project, Tag 0D6E, lemma-derived-pushforward-composition, and the
agent finite-support assembly in the DAG
(blueprint: lem-sfb-finite-principal-support-unit-assembly).

The empty open is represented by X itself. Every other open is the intersection of
its principal opens, equivalently D of their product. The right-adjoint comparison
is the conjugate of the canonical left-derived pullback comparison. List assembly
uses its inverse, so all composites have the target of the specified unit.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.FinitePrincipalSupport

variable {S : Type u} [CommRing S] {r : ℕ} (f : Fin r → S)

/-- The principal open D(product of f_b over J), written as a finite intersection.
Source: finite-support assembly, X_J (blueprint: lem-sfb-finite-principal-support-unit-assembly).
-/
def openSet (J : Finset (Fin r)) : (Spec (.of S)).Opens :=
  J.inf (fun b => PrimeSpectrum.basicOpen (f b))

/-- The punctured scheme; the empty intersection is represented by X itself.
Source: finite-support assembly, X_J (blueprint: lem-sfb-finite-principal-support-unit-assembly).
-/
def openScheme (J : Finset (Fin r)) : Scheme.{u} :=
  if J = ∅ then Spec (.of S) else (openSet f J).toScheme

/-- The actual open inclusion, with the empty inclusion the identity.
Source: finite-support assembly, i_J (blueprint: lem-sfb-finite-principal-support-unit-assembly).
-/
def inclusion (J : Finset (Fin r)) : openScheme f J ⟶ Spec (.of S) :=
  if h : J = ∅ then eqToHom (by simp only [openScheme, h, ↓reduceIte])
  else eqToHom (by simp only [openScheme, if_neg h]) ≫ (openSet f J).ι

/-- The canonical inclusion after inserting a coordinate. It also permits repeated insertions.
Source: finite-support assembly, e_{J,a}
(blueprint: lem-sfb-finite-principal-support-unit-assembly). -/
def step (J : Finset (Fin r)) (a : Fin r) :
    openScheme f (insert a J) ⟶ openScheme f J :=
  eqToHom (by simp only [openScheme, if_neg (Finset.insert_ne_empty a J)]) ≫
    if h : J = ∅ then
      (openSet f (insert a J)).ι ≫ eqToHom (by simp only [openScheme, h, ↓reduceIte])
    else
      (Spec (.of S)).homOfLE (U := openSet f (insert a J)) (V := openSet f J) (by
        dsimp only [openSet]
        rw [Finset.inf_insert]
        exact inf_le_right) ≫ eqToHom (by simp only [openScheme, if_neg h])

/-- The closed divisor V(f_a) on X_J, constructed by base change from Spec(S/(f_a)).
Source: finite-support assembly, d_{a,J}
(blueprint: lem-sfb-finite-principal-support-unit-assembly). -/
def divisor (J : Finset (Fin r)) (a : Fin r) :
    pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f a}))))
      (inclusion f J) ⟶ openScheme f J :=
  pullback.snd _ _

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The canonical pullback comparison for e_{J,a} followed by i_J.
Source: Stacks 0D6E, via canonical pullback composition
(blueprint: lem-sfb-finite-principal-support-unit-assembly). -/
def pullbackComparison (J : Finset (Fin r)) (a : Fin r) :
    moduleObjectDerivedPullback Λ (inclusion f (insert a J)) ≅
      moduleObjectDerivedPullback Λ (inclusion f J) ⋙
        moduleObjectDerivedPullback Λ (step f J a) :=
  eqToIso (congrArg (moduleObjectDerivedPullback Λ) (by
    by_cases hJ : J = ∅
    · subst J
      simp [step, inclusion, openScheme]
    · simp [step, inclusion, hJ, Finset.insert_ne_empty])) ≪≫
    leftDerivedUpperStarComp Λ (step f J a) (inclusion f J)

/-- The specified direct-image comparison, conjugate to inverse pullback composition.
Source: Stacks 0D6E and the conjugate-adjunction construction
(blueprint: lem-sfb-finite-principal-support-unit-assembly). -/
def pushforwardComparison (J : Finset (Fin r)) (a : Fin r) :
    moduleObjectDerivedPushforward Λ (inclusion f (insert a J)) ≅
      moduleObjectDerivedPushforward Λ (step f J a) ⋙
        moduleObjectDerivedPushforward Λ (inclusion f J) :=
  conjugateIsoEquiv
    (derivedUpperStarLowerStarAdjunction Λ (inclusion f (insert a J)))
    ((derivedUpperStarLowerStarAdjunction Λ (inclusion f J)).comp
      (derivedUpperStarLowerStarAdjunction Λ (step f J a)))
    (pullbackComparison f Λ J a).symm

/-- The comparison of the two targets in the unit composition formula.
Source: Stacks 0D6E, including the pullback identification of K_{J union {a}}
(blueprint: lem-sfb-finite-principal-support-unit-assembly). -/
def unitTargetComparison (J : Finset (Fin r)) (a : Fin r)
    (K : DerivedCategory (supportModules Λ (Spec (.of S)))) :
    (moduleObjectDerivedPushforward Λ (inclusion f (insert a J))).obj
        ((moduleObjectDerivedPullback Λ (inclusion f (insert a J))).obj K) ≅
      (moduleObjectDerivedPushforward Λ (inclusion f J)).obj
        ((moduleObjectDerivedPushforward Λ (step f J a)).obj
          ((moduleObjectDerivedPullback Λ (step f J a)).obj
            ((moduleObjectDerivedPullback Λ (inclusion f J)).obj K))) :=
  (pushforwardComparison f Λ J a).app _ ≪≫
    (moduleObjectDerivedPushforward Λ (step f J a) ⋙
      moduleObjectDerivedPushforward Λ (inclusion f J)).mapIso
        ((pullbackComparison f Λ J a).app K)

/-- Canonical identity comparison for the empty-set pullback.
Source: canonical identity pullback (blueprint: lem-sfb-finite-principal-support-unit-assembly).
-/
def emptyPullbackComparison :
    moduleObjectDerivedPullback Λ (inclusion f ∅) ≅
      𝟭 (DerivedCategory (supportModules Λ (Spec (.of S)))) :=
  leftDerivedUpperStarId Λ (Spec (.of S))

/-- The canonical empty direct-image comparison is the conjugate identity comparison.
Source: finite-support assembly, empty-set convention
(blueprint: lem-sfb-finite-principal-support-unit-assembly). -/
def emptyPushforwardComparison :
    moduleObjectDerivedPushforward Λ (inclusion f ∅) ≅
      𝟭 (DerivedCategory (supportModules Λ (Spec (.of S)))) :=
  conjugateIsoEquiv (derivedUpperStarLowerStarAdjunction Λ (inclusion f ∅))
    Adjunction.id (emptyPullbackComparison f Λ).symm

/-- The canonical identification of the target of the empty-set unit with K.
Source: finite-support assembly, empty-set convention
(blueprint: lem-sfb-finite-principal-support-unit-assembly). -/
def emptyTargetComparison (K : DerivedCategory (supportModules Λ (Spec (.of S)))) :
    (moduleObjectDerivedPushforward Λ (inclusion f ∅)).obj
        ((moduleObjectDerivedPullback Λ (inclusion f ∅)).obj K) ≅ K :=
  (emptyPushforwardComparison f Λ).app _ ≪≫ (emptyPullbackComparison f Λ).app K

/-- Compose the successive specified open units in a list, transported by the canonical
conjugate comparisons. No inverses of adjunction units are selected.
Source: finite-support assembly, ordering clause
(blueprint: lem-sfb-finite-principal-support-unit-assembly). -/
def assembledUnit (K : DerivedCategory (supportModules Λ (Spec (.of S)))) :
    (l : List (Fin r)) → K ⟶
      (moduleObjectDerivedPushforward Λ (inclusion f l.toFinset)).obj
        ((moduleObjectDerivedPullback Λ (inclusion f l.toFinset)).obj K)
  | [] => (derivedUpperStarLowerStarAdjunction Λ (inclusion f ∅)).unit.app K
  | a :: l => by
      rw [List.toFinset_cons]
      exact assembledUnit K l ≫
          (moduleObjectDerivedPushforward Λ (inclusion f l.toFinset)).map
            ((derivedUpperStarLowerStarAdjunction Λ (step f l.toFinset a)).unit.app
              ((moduleObjectDerivedPullback Λ (inclusion f l.toFinset)).obj K)) ≫
          (unitTargetComparison f Λ l.toFinset a K).inv

/-- Finite principal-support vanishing assembles the specified derived open unit.
Source: Stacks 0D6E, with the agent finite-support assembly recorded in the DAG
(blueprint: lem-sfb-finite-principal-support-unit-assembly).

Proof: (1) The recorded exactness of module pullback identifies restriction with total
left-derived pullback on ordinary unbounded internal-module derived categories.
(2) Each principal open is quasi-compact. The closed-support localization triangle
from det-lem-formal-closed-support-adjunction has zero first term by the hypothesis.
Rotate it and apply lem-kun-distinguished-cone-zero to its actual middle unit.
(3) Conjugate inverse canonical pullback composition. The defining conjugate formula,
naturality, and the left triangle identity show that the composite unit is the pushed
step unit after the preceding unit, under precisely unitTargetComparison.
(4) The identity adjunction and conjugate identity comparison give the empty formula.
(5) Induct on |J|, deleting a selected element; functors and composites preserve
invertibility. This gives every subset, not merely one chain of initial segments.
(6) Induct on the list of distinct selected elements using (3) and (4). Each assembled
map is the one fixed unit, so different orderings agree under the stipulated comparisons.
For empty X, zero K, r=0 and empty divisors the same triangles and comparisons apply;
a zero or nilpotent selected f forces the restricted K to vanish by the hypothesis. -/
theorem finite_principal_support_unit_assembly
    (K : DerivedCategory (supportModules Λ (Spec (.of S))))
    (hvanish : ∀ (J : Finset (Fin r)) (a : Fin r), a ∉ J →
      IsZero ((closedSupport Λ (divisor f J a) (step f J a)).rightDerivedFunctor.obj
        ((moduleObjectDerivedPullback Λ (inclusion f J)).obj K))) :
    (∀ J : Finset (Fin r),
      IsIso ((derivedUpperStarLowerStarAdjunction Λ (inclusion f J)).unit.app K)) ∧
    (∀ (J : Finset (Fin r)) (a : Fin r), a ∉ J →
      (derivedUpperStarLowerStarAdjunction Λ (inclusion f (insert a J))).unit.app K ≫
          (unitTargetComparison f Λ J a K).hom =
        (derivedUpperStarLowerStarAdjunction Λ (inclusion f J)).unit.app K ≫
          (moduleObjectDerivedPushforward Λ (inclusion f J)).map
            ((derivedUpperStarLowerStarAdjunction Λ (step f J a)).unit.app
              ((moduleObjectDerivedPullback Λ (inclusion f J)).obj K))) ∧
    ((derivedUpperStarLowerStarAdjunction Λ (inclusion f ∅)).unit.app K ≫
      (emptyTargetComparison f Λ K).hom = 𝟙 K) ∧
    (∀ l : List (Fin r), l.Nodup → assembledUnit f Λ K l =
      (derivedUpperStarLowerStarAdjunction Λ (inclusion f l.toFinset)).unit.app K) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.FinitePrincipalSupport
