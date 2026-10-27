/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveMatrixCentralCover
public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Mathlib.AlgebraicGeometry.Properties

import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Proper reduced connected subgroups of PGL₂ are smooth and solvable

Source: Milne, Algebraic Groups (2017), Corollary 17.27, printed p.360, and
Theorem 20.16 (c) implies (d), printed p.413; Stacks Project, Tag 0B7R.
(blueprint: lem-sfb-pgl2-proper-connected-subgroup-solvable)

The ambient group is any presentation of the fpqc scalar quotient from
`ProjectiveMatrixCentralCover.Presentation`, specialized to degree two.
Properness of the closed subgroup means that its inclusion is not an isomorphism.
Solvability refers to the scheme-theoretic derived series, including scheme structure.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A proper reduced connected closed subgroup of PGL₂ is smooth and has finite
scheme-theoretic derived length, in every characteristic.
Source: Milne, Algebraic Groups, Corollary 17.27, printed p.360, as used in
Theorem 20.16 (c) implies (d), printed p.413; Stacks Project, Tag 0B7R.
(blueprint: lem-sfb-pgl2-proper-connected-subgroup-solvable)

Proof:
1. By lem-sfb-locally-algebraic-group-identity-component, the reduced identity
component of I is smooth and integral. Connectedness identifies the identity component
with I, and reducedness identifies its reduction with I
(def-weil-pbc-scheme-reduction). Thus I is smooth, without a characteristic assumption.
2. The presentation of lem-sfb-projective-matrix-central-cover makes PGL₂ affine,
smooth, connected and three dimensional. The identity-component result makes it
irreducible, and sbc-lem-smooth-geometrically-reduced makes it reduced, hence integral
(def-pc-integral-scheme). Its identity section gives nonemptiness. The closed immersion
(def-weil-closed-immersion) writes I as Spec(A/J) in the affine integral ambient Spec(A).
If its underlying closed subset were all of Spec(A), the prime (0) would contain J,
so J=0 and the inclusion would be an isomorphism, contrary to properness. Appending
this strictly larger irreducible ambient space to a chain in I gives dim I + 1 ≤ 3
by def-kun-topological-krull-dimension. Thus dim I ≤ 2.
3. Apply lem-sfb-connected-group-dimension-two-solvable (Milne Corollary 17.27) to
this smooth connected affine finite-type group. Its conclusion is termination of the
scheme-theoretic derived series, which together with step 1 gives both assertions. -/
theorem pgl2_properConnectedSubgroup_smooth_solvable
    (F : Type u) [Field F] [IsAlgClosed F]
    (P : Grp (Over (Spec (.of F))))
    (π : GeneralLinearGroup (LinearGroupSchemes.Index.{u} 2) F ⟶ P.X)
    (j : StandardGroupSchemes.roots F 2 ⟶ LinearGroupSchemes.specialLinear F 2)
    (hP : ProjectiveMatrixCentralCover.Presentation F 2 (Nat.le_refl 2) P π j)
    (I : Over (Spec (.of F))) [GrpObj I] [IsAffine I.left]
    [LocallyOfFiniteType I.hom] [QuasiCompact I.hom]
    (i : I ⟶ P.X) [IsClosedSubgroupScheme i] (hproper : ¬ IsIso i)
    [IsReduced I.left] [ConnectedSpace I.left] :
    Smooth I.hom ∧ IsSolvableGroupScheme I := by
  sorry

end AlgebraicGeometry
