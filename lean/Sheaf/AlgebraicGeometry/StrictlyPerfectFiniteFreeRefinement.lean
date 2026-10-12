/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.RingTheory.FiniteProjectiveStandardFreeCover
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Finite free refinement of a strictly perfect local model

Source: Stacks Project, Tags 08C4, 08CM and 00NX.
(blueprint: lem-pc-strictly-perfect-finite-free-refinement).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A strictly perfect representative near a point can be made finite free on a smaller
affine neighbourhood, without changing the represented derived object.

Source: Stacks Project, Cohomology, Definitions 08C4 and 08CM; Algebra, Tag 00NX.
Proof: choose an affine neighbourhood of x contained in U. Restrict P and its termwise
splittings of finite free modules to that neighbourhood. Taking affine sections identifies
these splittings with splittings of finite free modules over its coordinate ring. Apply
`lem-weil-pbc-finite-projective-standard-free-cover` to each nonzero term and choose a
principal neighbourhood of x on which that term is finite free. There are only finitely
many such terms. Intersect these principal neighbourhoods to obtain an affine V containing
x and contained in U. Restrict P termwise to V to define F. Restriction is exact and
preserves zero objects, so F has the same finite bounds. On the remaining degrees use
rank zero. Restriction preserves the splittings and the selected finite free
trivializations. Finally restrict hEP and use the canonical comparison between successive
open restrictions, first on complexes and then after localization, to identify E restricted
to V with Q(F). The empty scheme has no point to check; zero terms use the rank zero free
module, so no nonzero-rank or nonempty-support hypothesis is needed.
(blueprint: lem-pc-strictly-perfect-finite-free-refinement). -/
theorem exists_finiteFree_refinement_of_isStrictlyPerfect
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    (E : schemeDerivedCategory X) (U : X.Opens)
    (P : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P)
    (hEP : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj P))
    (x : X) (hx : x ∈ U) :
    ∃ V : X.Opens, x ∈ V ∧ V ≤ U ∧ IsAffine V.toScheme ∧
      ∃ F : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)) ℤ,
        (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (F.X n)) ∧
        (∀ n : ℤ, ∃ r : ℕ, Nonempty (F.X n ≅ SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over V) (ULift.{u} (Fin r)))) ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) V).mapDerivedCategory.obj E ≅
            DerivedCategory.Q.obj F) := by sorry

end AlgebraicGeometry.Scheme
