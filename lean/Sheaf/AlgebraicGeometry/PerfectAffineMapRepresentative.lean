/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! # Representing affine perfect derived arrows by chain maps

Source: Stacks Project, Tag 08CR, second proof; Tag 06Z0, affine derived equivalence
(blueprint: lem-pc-perfect-affine-map-representative).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A derived arrow between strictly perfect complexes on an affine open is represented by
an actual chain map. Source: Stacks Project, Tag 08CR, second proof; Tag 06Z0
(blueprint: lem-pc-perfect-affine-map-representative).

Proof: Identify the localized site over U with the site of the affine scheme U, and
identify U with the spectrum of its ring of sections. The finite-free retract equations
show that every term of A and B is quasi-coherent. Taking global sections of the complexes
gives bounded complexes of finite projective modules: sections preserve retracts, and
sections of finite free modules on an affine scheme are finite free. The affine
sheafification/global-sections counit recovers A and B termwise, naturally in their
differentials. Thus the affine derived equivalence, followed by the fully faithful
quasi-coherent subcategory inclusion, lifts f to the module derived category. The source
complex is bounded above and projective, hence K-projective. Bijectivity of Qh on maps out
of it, followed by fullness of the homotopy quotient, gives a module chain map representing
the lifted arrow. Sheafify that chain map and conjugate by the termwise counit isomorphisms.
The factorization isomorphism for the affine equivalence and its naturality identify the
image under Q of this sheaf chain map with f. Transport back to the localized site to
obtain the claimed equality. For an empty affine open all objects and maps are zero. -/
theorem perfect_affine_map_representative (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (hU : IsAffineOpen U)
    (A B : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hA : IsStrictlyPerfect X U A) (hB : IsStrictlyPerfect X U B)
    (f : DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj B) :
    ∃ α : A ⟶ B, DerivedCategory.Q.map α = f := by sorry

end AlgebraicGeometry.Scheme
