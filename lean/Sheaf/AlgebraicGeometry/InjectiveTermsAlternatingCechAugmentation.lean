/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.AlgebraicGeometry.AlternatingCechTotalComplex

/-! # Finite-cover augmentation for complexes with injective terms

Source: Stacks Project, Tag 08C1, proof; Tags 01EP and 01FM.
(blueprint: lem-sc-injective-terms-alternating-cech-augmentation)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Injective terms suffice for the finite-cover augmentation; no boundedness or
K-injectivity assumption on the coefficient complex is needed.

Source: Stacks Project, Tag 08C1, first paragraph of the proof, using Tags 01EP
and 01FM (blueprint: lem-sc-injective-terms-alternating-cech-augmentation).

Proof: For each integer q, augment the alternating section complex of I.X q by
its global sections. The sheaf gluing axiom identifies the kernel in degree zero
with global sections and makes the augmentation injective. Injective module
Čech acyclicity gives zero positive cohomology for the ordered complex. The
ordered-to-increasing comparison, whose map is restriction to increasing tuples,
commutes with augmentation and identifies this with exactness of the explicit
alternating row used here. Forgetting global scalar structure detects exactness.
The cone of the section-to-total map is, up to its cone sign conventions, the
total of these augmented rows. Its Čech columns range from -1 to r-1: an increasing
(p+1)-tuple in Fin r does not exist when p >= r. For a total cocycle, exactness
supplies a horizontal preimage of its highest Čech component, since the next
column is zero. Subtract the total differential of this preimage. The highest
component disappears and the vertical part changes only the previous column.
Repeat down to column -1; injectivity of augmentation kills the final component.
Thus every cone cocycle is a boundary, even with unbounded vertical degrees,
and the augmentation is a quasi-isomorphism. If r=0, the cover implies X is empty;
the sheaf axiom makes every section module zero, and both complexes vanish. -/
theorem injectiveTerms_alternatingCech_augmentation_quasiIso
    (X : Scheme.{u}) (r : ℕ) (U : Fin r → X.Opens) (hU : iSup U = ⊤)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hI : ∀ n : ℤ, Injective (I.X n)) :
    QuasiIso ((alternatingCechAugmentation U).app I) := by sorry

end AlgebraicGeometry
