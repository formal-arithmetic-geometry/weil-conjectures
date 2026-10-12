/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-! # Shifting a uniform direct-image bound to the truncation tail

Source: Stacks Project, Tag 08D5, final truncation argument
(blueprint: lem-pc-direct-image-truncation-tail-bound).
-/

@[expose] public section

universe u wX wS

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A bound on nonpositive quasi-coherent derived objects gives a bound on the
upper truncation tail, without any geometric hypotheses beyond the supplied bound.
Source: Stacks Project, Tag 08D5, final truncation argument
(blueprint: lem-pc-direct-image-truncation-tail-bound).

Proof: Put T = τ_{< -n} E. Its cohomology is quasi-coherent, since it is either
zero or the corresponding cohomology of E. The shift T[-n-1] has no positive
cohomology: H^m(T[-n-1]) = H^{m-n-1}(T), which vanishes when m > 0.
Apply the supplied uniform bound to this shifted quasi-coherent derived object
in degree j+n+1. Derived direct image commutes with shifts and
H^{j+n+1}(Rf_*(T[-n-1])) is naturally isomorphic to H^j(Rf_*T).
Transport its zero-object property along this isomorphism. This works for all
integers n and j; no nonnegativity hypothesis on n is needed. -/
theorem directImage_truncation_tail_bound
    {X S : Scheme.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (f : X ⟶ S) (N : ℤ)
    (hN : ∀ E : schemeDerivedQCohCategory X,
      (∀ m : ℤ, 0 < m → IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) m).obj E.obj)) →
      ∀ m : ℤ, N ≤ m → IsZero ((schemeHigherDirectImage f m).obj E.obj))
    (E : schemeDerivedQCohCategory X) (n j : ℤ) (hj : N ≤ j + n + 1) :
    IsZero ((schemeHigherDirectImage f j).obj
      ((DerivedCategory.TStructure.t.truncLT (-n)).obj E.obj)) := by
  sorry

end AlgebraicGeometry
