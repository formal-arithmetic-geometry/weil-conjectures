/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.AlternatingCechSheafConstruction

/-! # Inner inverses of local alternating face differentials

Source: Stacks Project, Tag 02FU (cohomology-lemma-covering-resolution),
with increasing tuples as in Tag 01FM.
(blueprint: lem-pc-s3-alternating-cech-sheaf-differential-inner-inverse).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Each local face differential has an inner inverse, independently of the others.
Source: Stacks Project, Tag 02FU (cohomology-lemma-covering-resolution),
adapted to the increasing-tuple convention of Tag 01FM.
(blueprint: lem-pc-s3-alternating-cech-sheaf-differential-inner-inverse).

Proof: For a nonnegative degree k, on each test open V contained in U i,
define s from degree k+1 to k by signed insertion of i: the t-coordinate
is zero when t contains i, and otherwise is (-1)^b times the coordinate
indexed by t with i inserted in its increasing position b. The two
intersection opens inside V coincide. These formulas are linear and commute
with restriction, giving a morphism of restricted module presheaves.
Apply this formula to d(x). Its differential is d(x): on an inserted tuple
this follows from d(d(x))=0 and the face deleting i; on a tuple containing i
only the face omitting i contributes, with sign squared one. Consequently
d s d=d. This calculation only concerns boundaries, and does not assert
an identity on arbitrary cochains or compare adjacent choices of s.
The intersection presheaves V ↦ G(V intersect W) are already sheaves,
being direct images of restrictions to W. Their finite products are
sheaves, so each term's sheafification unit is an isomorphism. Restrict
these units to U i; naturality identifies their differential with the
restricted sheafified differential. Lift the insertion map through the
fully faithful forgetful functor and conjugate by these units. This
preserves d s d=d. Transport through extendXIso in the three
occurrences of d. For k<0 the differential is zero, since its source is
an extension-by-zero term, and s=0 works. Empty opens and zero terms cause
no exception; r=0 admits no index i. -/
theorem alternatingCechSheaf_restrict_differential_inner_inverse
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (i : Fin r)
    (k : ℤ) :
    let F := Scheme.Modules.restrictFunctor (U i).ι
    let C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((alternatingCechSheafComplex U G).extend ComplexShape.embeddingUpNat)
    ∃ s : C.X (k + 1) ⟶ C.X k,
      C.d k (k + 1) ≫ s ≫ C.d k (k + 1) = C.d k (k + 1) := by sorry

end AlgebraicGeometry
