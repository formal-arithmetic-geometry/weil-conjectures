/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q16
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.Topology.Constructible

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.Mathlib.Topology.Constructible

/-!
# Constructible images and open pieces on affine schemes of finite type

Source: Weil conjectures blueprint, `sec-algebraic-groups-lie-algebras/sk-p-geometry`,
`lem-wf-affine-constructible-open`, clauses (1)-(2) and their corollaries.
(blueprint: lem-wf-affine-constructible-open)

The existing spectrum-level Chevalley theorem and the Noetherian-space open-piece theorem
supply the inputs. These statements expose the precise affine-scheme hypotheses of the node.
-/

public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Chevalley for a morphism over a field between affine schemes of finite type.

Source: blueprint `sk-p-geometry/lem-wf-affine-constructible-open`, clause (1);
Stacks Project, Tag 054J. (blueprint: lem-wf-affine-constructible-open)

Proof: The finite-type affine covers and `lem-wf-affine-noetherian-components` make the
schemes locally Noetherian (`pqf-def-locnoeth`); affineness makes them quasi-compact and
quasi-separated (`lem-weil-pbc-affine-scheme-qcqs`). Since f is over k, finite-type
cancellation (`lemma-nagata-finite-type-to-separated-target`, clause (a)) makes f locally
of finite type, hence locally of finite presentation by `pqf-lem-lft-fp-locnoeth`.
It is affine by `lem-weil-pbc-morphism-affine-schemes-affine`, hence quasi-compact by
`lem-weil-pbc-affine-morphism-permanence`, clause (3). Apply
`lem-weil-pbc-chevalley-constructible-image` to the constructible subset S. -/
theorem Scheme.Hom.isConstructible_image_of_affine_finiteType
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    {S : Set X} (hS : Topology.IsConstructible S) :
    Topology.IsConstructible (f '' S) := by
  sorry

/-- The image of a morphism over a field between affine schemes of finite type is constructible.

Source: blueprint `sk-p-geometry/lem-wf-affine-constructible-open`, clause (1), final sentence;
Stacks Project, Tag 054J. (blueprint: lem-wf-affine-constructible-open)

Proof: Apply the preceding constructible-image assertion, obtained from finite-type
cancellation, the locally Noetherian finite-presentation criterion, affineness and Chevalley
as in `lem-weil-pbc-chevalley-constructible-image`, to S = X. The whole space is constructible
by `def-weil-constructible-subset`, and its image is the range of f. -/
theorem Scheme.Hom.isConstructible_range_of_affine_finiteType
    (k : Type u) [Field k] {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] :
    Topology.IsConstructible (Set.range f) := by
  sorry

/-- A nonempty constructible subset of an affine scheme of finite type over a field
contains a nonempty open subset of its closure, written as an ambient-open intersection.

Source: blueprint `sk-p-geometry/lem-wf-affine-constructible-open`, clause (2).
(blueprint: lem-wf-affine-constructible-open)

Proof: Finite-type affine covers are Noetherian by `lem-wf-affine-noetherian-components`;
`pqf-def-locnoeth` and `lem-weil-pbc-affine-scheme-qcqs` therefore make Y Noetherian.
Write S as a finite union of nonempty locally closed pieces S_i = U_i ∩ F_i using
`def-weil-constructible-subset`. Their closures cover Z = closure S. By
`lem-sc-noetherian-closed-subset-finite-components`, Z has finitely many irreducible
components C_j. Irreducibility (`def-weil-irreducible-components`) and induction on a finite
closed cover put C_1 inside some closure S_i. Remove the other components from Z to obtain
an open subset Ω of Z contained in C_1. It is nonempty: otherwise irreducibility puts C_1
inside a distinct component, contradicting maximality. For one component, Ω = Z.
Choose ambient open O with Ω = O ∩ Z. Then O ∩ closure S_i = Ω, so Ω is a nonempty open
subset of closure S_i and meets the dense S_i. Since closure S_i is contained in F_i,
S_i ∩ Ω = U_i ∩ Ω is nonempty, open in Z, and contained in S. Represent this relative open
as U ∩ Z using the subspace topology. Equivalently, apply the existing Noetherian-space
statement `exists_isOpen_inter_closure_subset_of_isConstructible` to Y. -/
theorem Scheme.exists_isOpen_inter_closure_subset_of_isConstructible_of_affine_finiteType
    (k : Type u) [Field k] (Y : Scheme.{u}) [IsAffine Y]
    [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    {S : Set Y} (hS : Topology.IsConstructible S) (hne : S.Nonempty) :
    ∃ U : Set Y, IsOpen U ∧ (U ∩ closure S).Nonempty ∧ U ∩ closure S ⊆ S := by
  sorry

/-- A nonempty dense constructible subset of an affine scheme of finite type over a field
contains a nonempty open subset of that scheme.

Source: blueprint `sk-p-geometry/lem-wf-affine-constructible-open`, clause (2), final sentence.
(blueprint: lem-wf-affine-constructible-open)

Proof: The finite-type and affine hypotheses give a Noetherian space, as in
`lem-wf-affine-noetherian-components`, `pqf-def-locnoeth` and
`lem-weil-pbc-affine-scheme-qcqs`. Apply the open-piece assertion proved by the finite
locally closed decomposition, finite irreducible components, and component-isolation
argument of clause (2). Density gives closure S = Y, so the nonempty intersection of the
ambient open with closure S is the ambient open itself, contained in S. -/
theorem Scheme.exists_isOpen_nonempty_subset_of_dense_isConstructible_of_affine_finiteType
    (k : Type u) [Field k] (Y : Scheme.{u}) [IsAffine Y]
    [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    {S : Set Y} (hS : Topology.IsConstructible S) (hne : S.Nonempty) (hdense : Dense S) :
    ∃ U : Set Y, IsOpen U ∧ U.Nonempty ∧ U ⊆ S := by
  sorry

end AlgebraicGeometry
