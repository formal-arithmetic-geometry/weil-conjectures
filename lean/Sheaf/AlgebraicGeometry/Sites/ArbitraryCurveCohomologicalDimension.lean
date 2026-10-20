/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license.
-/
module

public import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.KrullDimension

import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.AlgebraicGeometry.Curve.TorsionCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison

/-!
# Torsion cohomological dimension of arbitrary curves

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-sc-arbitrary-curve-cd.md,
statement and proof (blueprint: lem-sc-arbitrary-curve-cd).
Stacks Project, Tag 00TV supplies the regular-to-smooth criterion used in the proof.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A separated finite-type scheme of dimension at most one over an algebraically closed field has
torsion étale cohomological dimension at most two, and at most one when it is affine.
Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-sc-arbitrary-curve-cd.md,
statement and proof (blueprint: lem-sc-arbitrary-curve-cd).
Stacks Project, Tag 00TV supplies the regular-to-smooth criterion used in the proof.

Proof: (1) Use `thm-weil-pbc-universal-homeomorphism-invariance` for the reduction map;
its equivalence preserves cohomology and local torsion. The reduction of an affine scheme is
affine, and in the non-affine case any bound at most two suffices. Finite type over a field makes
X Noetherian with finitely many components (`lem-weil-pbc-finite-type-over-noetherian`,
`lem-weil-pbc-noetherian-finitely-many-components`). Normalize the reduced integral components
in their function fields and take their finite disjoint union h : X' → X.
`lem-fin-normalization-extension-finite` makes h finite. On affine covers, invert common
nonzero denominators of generators of the normalization to obtain dense opens where it is the
identity. Remove their complements and intersections of distinct components. The removed set
is closed of dimension at most zero, hence a finite set S of closed points by
`lem-sc-dim0-finite`; h is an isomorphism over U = X \ S.

(2) The field is perfect. Apply `lem-sc-normalized-curve-smooth` to each one-dimensional
integral component, and `lem-sc-normalization-exists` for its dimension. Each normalized
component is connected, separated, and of finite type. A zero-dimensional integral component
is a field spectrum and equals Spec k by `lem-kun-closed-point-field`. If X is affine, X' and
each of its open-and-closed components are affine, since h is finite.

(3) Let F be any locally torsion abelian étale sheaf, with no common annihilator assumed.
The unit F → h_*h^*F is an isomorphism on U. Points of S have residue field k by
`lem-kun-closed-point-field`. Apply `lem-sc-iso-off-finite-set-cohomology` to compare
cohomology in degrees q ≥ 2. Exactness of finite direct image
(`lemma-weil-pbc-finite-direct-image-exact`) identifies the latter groups with H^q(X', h^*F).
By `lem-weil-pbc-inverse-image-stalk-germ` and
`lem-weil-pbc-torsion-sheaf-characterizations`, h^*F is locally torsion. Apply
`lem-sc-cohomological-dimension` on smooth connected curve components, or
`lem-sc-affine-cohomological-dimension` if X is affine, and
`lem-weil-pbc-zero-dimensional-cohomology` on point components. Derived sections on a finite
disjoint union decompose as a finite product, since finite products of abelian groups are exact.
Thus H^q(X', h^*F) vanishes for q > e, including the empty union. Since q > e ≥ 1 implies
q ≥ 2, the comparison gives the required vanishing on X. Quantifying over all locally torsion
F is exactly `def-sc-etale-torsion-cd`. -/
theorem torsionEtaleCohomologicalDimensionLE_of_dim_le_one
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim X ≤ 1) :
    (IsAffine X ∧ Scheme.HasTorsionEtaleCohomologicalDimensionLE X 1) ∨
      (¬ IsAffine X ∧ Scheme.HasTorsionEtaleCohomologicalDimensionLE X 2) := by
  let _ : IsCurve f := { krullDim_le_one := hdim }
  obtain ⟨h₂, h₁⟩ := IsCurve.hasTorsionCohomologicalDimensionLE f
  have convert (n : ℕ) (h : X.HasTorsionCohomologicalDimensionLE n) :
      Scheme.HasTorsionEtaleCohomologicalDimensionLE X n := by
    intro F hF q hq
    have h' := h F hF q hq
    have : Subsingleton ((Sheaf.functorH X.smallEtaleTopology q).obj F) := h'
    obtain ⟨e⟩ := Scheme.nonempty_sheafH_extDerivedIso X q
    exact (e.app F).addCommGroupIsoToAddEquiv.symm.injective.subsingleton
  by_cases ha : IsAffine X
  · exact Or.inl ⟨ha, convert 1 (h₁ ha)⟩
  · exact Or.inr ⟨ha, convert 2 h₂⟩

end AlgebraicGeometry

end
