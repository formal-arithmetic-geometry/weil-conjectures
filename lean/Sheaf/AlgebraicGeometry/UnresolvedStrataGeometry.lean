/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q143
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryResolutionRule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.Sober

/-! # Unresolved loci and codimension strata

Source: Temkin, Non-embedded Desingularization, §§2.1.6, 2.1.9, 4.1.1--4.1.3
(blueprint: def-per-unresolved-strata-geometry).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ResolutionStrata

/-- Absolute singular points, using regular local rings, not relative nonsmoothness.
Source: Temkin §2.1.9 (blueprint: def-per-unresolved-strata-geometry). -/
def singularSet (X : Scheme.{u}) : Set X :=
  {x | ¬ IsRegularLocalRing (X.presheaf.stalk x)}

/-- The points of a subset having ambient local dimension `r`.
Source: Temkin §4.1.2 (blueprint: def-per-unresolved-strata-geometry). -/
def heightStratum {X : Scheme.{u}} (Z : Set X) (r : ℕ) : Set X :=
  {x | x ∈ Z ∧ ringKrullDim (X.presheaf.stalk x) = (r : WithBot ℕ∞)}

/-- Generic points of the irreducible components of a subset, in the ambient space.
Source: Temkin §4.1.3 (blueprint: def-per-unresolved-strata-geometry). -/
def componentGenericPoints {X : Scheme.{u}} (Z : Set X) : Set X :=
  Subtype.val '' genericPoints Z

/-- The reduced closed scheme structure on the closure of a set, expressed by its ideal.
Source: Temkin §4.3; Stacks 01J3 (blueprint: def-per-unresolved-strata-geometry). -/
noncomputable def reducedClosureIdeal {X : Scheme.{u}} (Z : Set X) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨closure Z, isClosed_closure⟩

/-- The strong unresolved set: singular images of the final level and every center.
Source: Temkin §4.1.1 (blueprint: def-per-unresolved-strata-geometry). -/
def unresolvedSet {X : Scheme.{u}} (A : OrdinaryBlowupTower X) : Set X :=
  A.toBase (Fin.last A.length) '' singularSet (A.level (Fin.last A.length)) ∪
    ⋃ i : Fin A.length,
      ((A.center i).subschemeι ≫ A.toBase i.castSucc) ''
        singularSet (A.center i).subscheme

/-- Pure ambient codimension means local dimension `e` at every component generic point.
Source: Temkin §4.1.3 (blueprint: def-per-unresolved-strata-geometry). -/
def HasPureCodimension {X : Scheme.{u}} (D : Set X) (e : ℕ) : Prop :=
  ∀ x ∈ componentGenericPoints D, ringKrullDim (X.presheaf.stalk x) = (e : WithBot ℕ∞)

/-- Functions are determined on the local schemes over the generic points of the image.
Equality of all such germs on each open is exactly injectivity of restriction to those
local schemes; no topology or scheme structure on the set of generic points is chosen.
Source: Temkin §§2.1.6--2.1.7, 4.1.3
(blueprint: def-per-unresolved-strata-geometry). -/
def IsGenericallySchematicallyDense {W X : Scheme.{u}} (f : W ⟶ X) : Prop :=
  ∀ (U : W.Opens) (a b : Γ(W, U)),
    (∀ (w : W) (hw : w ∈ U), f w ∈ componentGenericPoints (Set.range f) →
      W.presheaf.germ U w hw a = W.presheaf.germ U w hw b) → a = b

end AlgebraicGeometry.ResolutionStrata
