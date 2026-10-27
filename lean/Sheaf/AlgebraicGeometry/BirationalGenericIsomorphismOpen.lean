/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.Topology.Sober
public import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Irreducible
import Sheaf.AlgebraicGeometry.BirationalIsomorphismDenseOpen

/-!
# Generic isomorphism open of a proper birational map

Source: Stacks Project, Varieties, Tag 0BFP,
lemma-modification-normal-iso-over-codimension-1, proof (1), using Morphisms, Tag 0BAJ,
lemma-birational-isomorphism-over-dense-open
(blueprint: lem-sfb-birational-generic-isomorphism-open).
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- A proper birational morphism to a Noetherian scheme is an isomorphism over a dense open
containing every generic point of every irreducible component of the target. Birationality
means that this morphism bijects the component generic points and induces isomorphisms of
their local rings. No reducedness hypothesis is imposed.

Source: Stacks Project, Varieties, Tag 0BFP,
lemma-modification-normal-iso-over-codimension-1, proof (1), using Morphisms, Tag 0BAJ,
lemma-birational-isomorphism-over-dense-open
(blueprint: lem-sfb-birational-generic-isomorphism-open).

Proof:
1. Properness [def-weil-proper-morphism] gives separatedness and finite type, hence local
   finite type [def-weil-finite-type-morphism]. Over the locally Noetherian target
   [pqf-def-locnoeth], local finite presentation follows from [pqf-lem-lft-fp-locnoeth].
2. The Noetherian target has finitely many irreducible components by
   [lem-weil-pbc-noetherian-finite-components]. Sobriety [lem-sc-scheme-sober] identifies
   components with their generic points. The assumed bijection of these points therefore
   implies that the source also has finitely many irreducible components.
3. Apply [lem-sfb-birational-isomorphism-dense-open] with separatedness, local finite
   presentation, the finite component sets, and the given generic-point and stalk hypotheses.
   This yields a dense open V for which the entire inverse-image restriction is an isomorphism.
4. For a component C with generic point xi [def-sc-generic-point], remove the other finitely
   many components to obtain an open O containing xi. No other component contains xi, since
   closedness would force it to contain C, contradicting maximality
   [def-weil-irreducible-components]. Every point lies in a component by
   [lem-sc-irreducible-components-cover], so O is contained in C. Density of V gives a point
   z in O intersect V. Since z lies in C = closure {xi}, its open neighbourhood V contains xi.
   For the empty target the empty open is dense, and this final clause is vacuous.
-/
theorem exists_dense_open_isIso_of_proper_birational
    {X Y : Scheme.{u}} [IsNoetherian X] (f : Y ⟶ X) [IsProper f]
    (hgeneric : Set.BijOn f (genericPoints Y) (genericPoints X))
    (hstalk : ∀ η : Y, η ∈ genericPoints Y → IsIso (f.stalkMap η)) :
    ∃ V : X.Opens, Dense (V : Set X) ∧ genericPoints X ⊆ (V : Set X) ∧
      IsIso (f ∣_ V) := by
  sorry

end AlgebraicGeometry
