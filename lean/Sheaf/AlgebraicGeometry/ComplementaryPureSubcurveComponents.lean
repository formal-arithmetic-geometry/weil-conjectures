/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.KrullDimension
import WeilConjectures.Topology.IrreducibleOpenComplementDimension

/-!
# Complementary components of a reduced pure subcurve

Source: Stacks Project, Curves, Tag 0E38, first paragraph of the proof of
`lemma-closed-subscheme-nodal-curve`; Schemes, Tags 01J3 and 01J4
(blueprint: lem-trf-complementary-pure-subcurve-components).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A reduced pure one-dimensional closed subcurve is a union of components, and its
complementary reduced closure consists of the remaining components. Taking the complementary
reduced closure twice recovers the subcurve as a closed subscheme of the ambient scheme.
Source: Stacks Project, Curves, Tag 0E38, first proof paragraph; Schemes, Tags 01J3 and 01J4
(blueprint: lem-trf-complementary-pure-subcurve-components).

Here `j` represents the reduced induced structure on the complementary closure: it is a
reduced closed immersion with that image, hence is the unique such closed subscheme by
`Scheme.IdealSheafData.reduced_induced_closed_subscheme`. For the same reason, the two range
identities express equality with the reduced closed unions, including their scheme structures.
The set `irreducibleComponents X` is finite by
`finite_irreducibleComponents_of_isNoetherian`.

Proof plan, following the six steps of the node:
1. Noetherianity gives finitely many components
   (lem-weil-pbc-noetherian-finitely-many-components). If X is empty, all schemes are empty.
   Every point belongs to a component (lem-sc-irreducible-components-cover).
2. Each component C of Y is a closed irreducible subset of a component D of X. If C is
   proper in D, new-node-irreducible-open-complement-dimension applied to D minus C bounds
   its dimension by zero, contradicting the dimension-one hypothesis. Thus C equals D.
3. Take I to be the components of X arising from Y. Component coverage gives range i equal
   to their union; reduced-induced uniqueness identifies the scheme structure
   (lem-weil-pbc-reduced-induced-closed-subscheme).
4. The union W of the remaining components is closed. It contains X minus range i.
   Conversely the generic point of each remaining component lies outside range i:
   otherwise irreducibility and the finite closed cover force that component into a
   selected component, contradicting maximality. Its closure is therefore in the closure
   of X minus range i. This proves W equals range j, using lem-sc-scheme-sober.
5. The maximal irreducible subsets of W are exactly the remaining components: a finite
   closed cover contains any irreducible subset in one member, and distinct components
   do not contain one another. Hence all components of Z have dimension one; reducedness
   supplies the asserted reduced union (lem-weil-pbc-reduced-induced-closed-subscheme).
6. X minus W lies in range i. Each selected component has its generic point outside W,
   since otherwise it would equal a remaining component. Thus the closure of X minus W
   is range i. Reduced-induced uniqueness gives the displayed isomorphism over X.
   The same argument includes I empty and I equal to the entire component set. -/
theorem complementary_pure_subcurve_components
    {X Y Z : Scheme.{u}} [IsReduced X] [IsNoetherian X]
    (hX : ∀ C ∈ irreducibleComponents X, topologicalKrullDim C = 1)
    (i : Y ⟶ X) [IsClosedImmersion i] [IsReduced Y]
    (hY : ∀ C ∈ irreducibleComponents Y, topologicalKrullDim C = 1)
    (j : Z ⟶ X) [IsClosedImmersion j] [IsReduced Z]
    (hZ : Set.range j = closure ((Set.range i)ᶜ)) :
    ∃ I : Set (Set X), I ⊆ irreducibleComponents X ∧
      Set.range i = ⋃₀ I ∧
      Set.range j = ⋃₀ (irreducibleComponents X \ I) ∧
      (∀ C ∈ irreducibleComponents Z, topologicalKrullDim C = 1) ∧
      ∃ e : Y ≅
          (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ((Set.range j)ᶜ))).subscheme,
        e.hom ≫
          (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ((Set.range j)ᶜ))).subschemeι =
            i := by
  sorry

end AlgebraicGeometry
