/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteOrClosedPerverseSupport
public import
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTriangulated

/-! # The prescribed perverse classes over finite or algebraically closed fields

Source: latest blueprint, def-per-perverse-subcategories; Wei Yang #1441 item 36.
(blueprint: def-per-perverse-subcategories).
The registered support predicate is reused and cosupport uses the generalized actual dual.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]

/-- The support class, unchanged from the recorded support condition.
Source: def-per-perverse-subcategories, first equality
(blueprint: def-per-perverse-subcategories). -/
def FiniteOrClosedPerverseLEZero (_hk : Finite k ∨ IsAlgClosed k)
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] :
    ObjectProperty (BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell)
      X.left)) := CondensedSupportCondition ell

/-- The cosupport class for the same finite or algebraically closed field.
Source: def-per-perverse-subcategories, second equality
(blueprint: def-per-perverse-subcategories). -/
def FiniteOrClosedPerverseGEZero (hk : Finite k ∨ IsAlgClosed k)
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] :
    ObjectProperty (BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ell)
      X.left)) := FiniteOrClosedCosupportCondition ell hk X

/-- Translation by [-n], as pullback of the support property along [n].
Source: def-per-perverse-subcategories, third equality
(blueprint: def-per-perverse-subcategories). -/
def FiniteOrClosedPerverseLE (hk : Finite k ∨ IsAlgClosed k)
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] (n : ℤ) := (FiniteOrClosedPerverseLEZero ell hk X).shift n

/-- Translation by [-n], as pullback of the cosupport property along [n].
Source: def-per-perverse-subcategories, fourth equality
(blueprint: def-per-perverse-subcategories). -/
def FiniteOrClosedPerverseGE (hk : Finite k ∨ IsAlgClosed k)
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] (n : ℤ) := (FiniteOrClosedPerverseGEZero ell hk X).shift n

/-- Full perverse heart candidate, the intersection of the two prescribed properties.
Source: def-per-perverse-subcategories, last equality
(blueprint: def-per-perverse-subcategories). -/
def FiniteOrClosedPerverseHeart (hk : Finite k ∨ IsAlgClosed k)
    (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] :=
  FiniteOrClosedPerverseLEZero ell hk X ⊓ FiniteOrClosedPerverseGEZero ell hk X

end AlgebraicGeometry.ProEtale.CondensedRing
