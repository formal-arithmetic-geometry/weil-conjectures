/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Sheaf.AlgebraicGeometry.AlternatingCechTotalComplex

/-! # Čech augmentation of a K-injective complex

Source: Stacks Project, Cohomology, Lemma 08C1.
(blueprint: lem-sc-kinjective-alternating-cech-augmentation-quasi-iso)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The finite-cover Čech augmentation is a quasi-isomorphism on every K-injective
complex. Injectivity of its individual terms is not required.

Source: Stacks Project, Cohomology, Lemma 08C1 and Tag 01EP.
(blueprint: lem-sc-kinjective-alternating-cech-augmentation-quasi-iso).

Proof: Resolve J into a K-injective complex I with injective terms. Each augmented
alternating section row of I is exact: degree zero is the sheaf gluing axiom, and
positive degrees follow from injective Čech acyclicity and ordered-to-alternating
comparison. The cone of the augmentation is the total of these exact augmented rows.
It has only finitely many Čech columns. Eliminate a total cocycle column by column
using row exactness; at the augmentation column its injectivity eliminates the last
component. This proves acyclicity of the cone and hence that the augmentation of I
is a quasi-isomorphism. The quasi-isomorphism J → I between K-injectives is a homotopy
equivalence. Termwise sections preserve its homotopies. Čech totalization preserves
homotopies as well: in Čech degree p apply the sectionwise homotopy with sign (-1)^p;
the horizontal homotopy terms cancel and the vertical equation is dh + hd.
The augmentation's naturality square therefore has homotopy equivalences as its two
vertical maps. Two-out-of-three transports the quasi-isomorphism from I to J.
For the empty covering the scheme is empty and all its section modules are zero. -/
theorem kInjective_alternatingCech_augmentation_quasiIso
    (X : Scheme.{u}) (r : ℕ) (U : Fin r → X.Opens) (hU : iSup U = ⊤)
    (J : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [J.IsKInjective] :
    QuasiIso ((alternatingCechAugmentation U).app J) := by sorry

end AlgebraicGeometry
