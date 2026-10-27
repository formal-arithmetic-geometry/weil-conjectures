/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion

import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic
import WeilConjectures.AlgebraicGeometry.IsAffineOfFiniteClosedCover
import Mathlib.Topology.Irreducible
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Common affine opens for finitely many rational points of a group scheme

Source: Stacks Project, Groupoids, Tag 0B7S (lemma-points-in-affine)
(blueprint: lem-sfb-group-finite-points-affine).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every finite list of rational points of a locally algebraic group over an algebraically
closed field factors through one affine open. Points may repeat and the list may be empty.
Source: Stacks Project, Groupoids, Tag 0B7S (lemma-points-in-affine)
(blueprint: lem-sfb-group-finite-points-affine).

Proof:
1. By lem-sfb-locally-algebraic-group-identity-component, the identity component C is a
clopen irreducible open subgroup of finite type. Partition the marked indices by the
finitely many connected components they meet. In each choose a marked rational point a.
By lem-sc-translation-automorphism, left translation by a identifies C with that component;
restrict the inverse translations using lem-weil-pbc-morphism-factors-through-open-subscheme.
2. Translate its marked points to b_i = a⁻¹ h_i in C. Choose an affine open neighbourhood V
of the identity (def-pc-scheme). Each right translate V b_i⁻¹ is nonempty and open in C
(def-sc-group-scheme-translate, lem-sc-translation-automorphism), so their finite intersection
is nonempty by irreducibility (def-weil-irreducible-components). Restrict these translations
through the open subgroup using lem-weil-pbc-morphism-factors-through-open-subscheme.
3. By lem-sc-lft-over-field-jacobson-space, this nonempty open contains a closed point.
By lem-weil-pbc-closed-point-residue-field-base, its residue field is k, yielding a rational
point g in every V b_i⁻¹. This uses local finite type and imposes no quasi-compactness on
that intersection.
4. Thus g b_i lies in V and b_i lies in g⁻¹ V. The affine open a g⁻¹ V in H contains the
marked points of this component; translations are isomorphisms by
lem-sc-translation-automorphism. The order of multiplication does not assume commutativity.
5. The finitely many resulting affine opens are disjoint and clopen in their union U.
Their inclusions into U are closed immersions (def-weil-closed-immersion): the stalk maps
are identities on the summand and have zero targets off it. Apply
lem-sc-closed-affine-union-affine to see that U is affine. Each marked morphism factors
through U by lem-weil-pbc-morphism-factors-through-open-subscheme. For n = 0 use the empty
affine open, the spectrum of the zero ring. Repetitions do not change the construction. -/
theorem GrpObj.exists_isAffineOpen_fin_points
    (k : Type u) [Field k] [IsAlgClosed k]
    (H : Over (Spec (.of k))) [GrpObj H] [LocallyOfFiniteType H.hom]
    (n : ℕ) (h : Fin n → (Spec (.of k) ⟶ H.left))
    (hh : ∀ i : Fin n, h i ≫ H.hom = 𝟙 (Spec (.of k))) :
    ∃ U : H.left.Opens, IsAffineOpen U ∧
      ∀ i : Fin n, ∃ hU : Spec (.of k) ⟶ U.toScheme, hU ≫ U.ι = h i := by
  sorry

end AlgebraicGeometry
