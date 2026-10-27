/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryResolutionRule
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.Sober
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-! # Unresolved loci and lowest codimension strata

Source: Temkin, Non-embedded Desingularization, §§2.1.6, 4.1.1--4.1.3 and §4.3
(blueprint: def-per-resolution-strata).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The images of the singular loci of the final scheme and all scheme-theoretic centers.
Source: Temkin §4.1.1 (blueprint: def-per-resolution-strata). -/
def OrdinaryBlowupTower.unresolvedSet {X : Scheme.{u}} (R : OrdinaryBlowupTower X) :
    Set X :=
  (R.toBase ⟨R.length, Nat.lt_succ_self R.length⟩) ''
    {x | ¬ IsRegularLocalRing
      ((R.level ⟨R.length, Nat.lt_succ_self R.length⟩).presheaf.stalk x)} ∪
  ⋃ i : Fin R.length, ((R.center i).subschemeι ≫ R.toBase i.castSucc) ''
    {z | ¬ IsRegularLocalRing ((R.center i).subscheme.presheaf.stalk z)}

/-- Points of a subset whose ambient local ring has dimension `r`, with Krull dimension
in its extended natural-number range. Source: Temkin §4.1.2
(blueprint: def-per-resolution-strata). -/
def Scheme.heightStratum (X : Scheme.{u}) (Z : Set X) (r : ℕ) : Set X :=
  {x | x ∈ Z ∧ ringKrullDim (X.presheaf.stalk x) = (r : WithBot ℕ∞)}

/-- The generic points of the irreducible components of a subset, viewed in the ambient
scheme. The topology on the subset is the subspace topology, without taking its closure.
Source: Temkin §4.1.3 (blueprint: def-per-resolution-strata). -/
def Scheme.genericPointsIn (X : Scheme.{u}) (Z : Set X) : Set X :=
  Subtype.val '' genericPoints Z

/-- The ideal of the reduced closure of a set, constructed by the existing vanishing
ideal operation. Source: Temkin §4.3, Extension 0 and functoriality paragraph; Stacks 01J3
(blueprint: def-per-resolution-strata). -/
noncomputable def Scheme.reducedClosureIdeal (X : Scheme.{u}) (S : Set X) :
    X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨closure S, isClosed_closure⟩

/-- Sections are determined on the local schemes over the generic points of the image:
a section with zero germ at every such source point is zero. This is schematic density,
not merely topological density. Source: Temkin §§2.1.6 and 4.1.3
(blueprint: def-per-resolution-strata). -/
def Scheme.Hom.SchematicallyDenseOverGenericImage {W X : Scheme.{u}} (p : W ⟶ X) :
    Prop :=
  ∀ (U : W.Opens) (a : Γ(W, U)),
    (∀ (w : W) (hw : w ∈ U), p w ∈ X.genericPointsIn (Set.range p) →
      W.presheaf.germ U w hw a = 0) → a = 0

end AlgebraicGeometry
