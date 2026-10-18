/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q111
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Sheaf.AlgebraicGeometry.SeparatedLqfBaseChange

/-!
# Birational morphisms are isomorphisms over a dense open

Source: Stacks Project, Morphisms, Tag 0BAJ, the separated and locally finitely presented case
(blueprint: lem-per-birational-isomorphism-dense-open).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A separated, locally finitely presented morphism between schemes with finitely many
irreducible components is an isomorphism over a dense open of its target if it maps generic
points bijectively and induces isomorphisms on their local rings.

Source: Stacks Project, Morphisms, Tag 0BAJ, separated and locally finitely presented case
(blueprint: lem-per-birational-isomorphism-dense-open).

Proof:
1. Apply `lem-per-birational-common-dense-opens` (Tag 0BAC(2)) to obtain dense opens
   `U` in `Y` and `V` in `X` such that the restriction `g : U ⟶ V` of `f` is an
   isomorphism. No reducedness is required. Put `W = f ⁻¹ᵁ V`; the inclusion of `U`
   factors as an open inclusion `j : U ⟶ W` followed by `W.ι`
   (`def-weil-open-immersion`).
2. The restriction `p : W ⟶ V` is separated, since it is a base change of `f`
   (`lem-weil-pbc-separated-lqf-base-change`, first clause). The map `g.inv ≫ j`
   is a section of `p`, hence a closed immersion
   (`lem-weil-pbc-section-separated-closed-immersion`, Tag 01KT). Its image is `U`,
   which is therefore closed in `W` (`def-weil-closed-immersion`).
3. Every nonempty open of `W` is open in `Y` and meets the dense open `U`. Thus `U`
   is dense as well as closed in `W`, so `U = W` as open subsets of `Y`. Their open
   subscheme structures agree (`def-weil-open-immersion`), and `p` is the isomorphism
   `g`. The open `V` is dense in `X`. This also covers empty schemes. -/
theorem exists_dense_open_isIso_of_generic_stalks {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsSeparated f] [LocallyOfFinitePresentation f]
    (hX : (irreducibleComponents X).Finite) (hY : (irreducibleComponents Y).Finite)
    (hgeneric : Set.BijOn f (genericPoints Y) (genericPoints X))
    (hstalk : ∀ η ∈ genericPoints Y, IsIso (f.stalkMap η)) :
    ∃ V : X.Opens, Dense (V : Set X) ∧ IsIso (f ∣_ V) := by
  sorry

end AlgebraicGeometry
