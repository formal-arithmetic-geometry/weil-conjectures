/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Isomorphisms of abelian étale sheaves are detected on an étale covering

Source: Stacks Project, Étale Cohomology, Tag 0EZR, proof of (1), with Tags 03PU and 03Q1
(blueprint: lem-weil-pbc-etale-cover-detects-iso).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- A morphism of abelian sheaves on the small étale site is an isomorphism exactly when
its inverse images along a jointly surjective étale family are isomorphisms.
Source: Stacks Project, Tag 0EZR, last sentence of the proof of (1), with Tags 03PU and 03Q1
(blueprint: lem-weil-pbc-etale-cover-detects-iso).

Proof:
1. An inverse to `φ` is sent by each inverse-image functor to an inverse to its image
   (def-weil-pbc-inverse-image).
2. Conversely, for every geometric point of `T`, joint surjectivity and étaleness lift it
   to a geometric point of some `U i` over the same algebraically closed field
   (lem-weil-pbc-etale-cover-geometric-point-lift; def-weil-geometric-point; Stacks Tag 03PR).
3. At this lift, the stalk of the inverse image is naturally isomorphic to the stalk at
   the original geometric point (lemma-openclosed-stalk-upperstar;
   def-weil-pbc-geometric-stalks; def-weil-pbc-inverse-image; Stacks Tag 03Q1 (3)).
   Taking stalks preserves isomorphisms, and naturality conjugates the map on the original
   stalk to the map on the inverse-image stalk. Thus every geometric stalk map is invertible.
4. Geometric stalks detect isomorphisms (lemma-weil-pbc-geometric-stalk-conservative;
   Stacks Tag 03PU), so `φ` is invertible.
For the empty index type, joint surjectivity forces `T` to have no points, and the right
side is vacuous. The same criterion therefore says every morphism is invertible. -/
theorem isIso_iff_of_jointlySurjective_etale_family
    {T : Scheme.{u}} {I : Type w} {U : I → Scheme.{u}}
    (t : ∀ i : I, U i ⟶ T) [∀ i : I, Etale (t i)]
    (ht : ∀ x : T, ∃ (i : I) (y : U i), (t i).base y = x)
    {G H : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}} (φ : G ⟶ H) :
    IsIso φ ↔ ∀ i : I, IsIso ((upperStar AddCommGrpCat.{u + 1} (t i)).map φ) := by
  sorry

end AlgebraicGeometry.Etale
