/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Splitting the irreducible components over a field

Source: Stacks Project, Tags 0551 and 054R.
(blueprint: lem-sbc-generic-components-split)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicGeometry

/-- A finite type scheme over a field acquires geometrically irreducible components
after a finite separable field extension.

Source: Stacks Project, Tag 0551, first paragraph of the proof, and Tag 054R.
Proof: the scheme is noetherian, since it is finite type over a field. By Tag 054R,
base change to a separable algebraic closure. Its finitely many irreducible
components descend to a finite subextension: on a finite affine cover their defining
ideals have finitely many generators, and only finitely many algebraic coefficients
occur. Enlarge the subextension for all components simultaneously. The descended
components are geometrically irreducible, since their base changes to the separable
closure are irreducible (purely inseparable extensions do not change the topology).
Thus this is a finite separable extension with the required components. Its spectrum
map is finite and etale. For a component C,
give C its reduced closed subscheme structure. Geometric irreducibility says that
every field base change of this subscheme is irreducible and nonempty. The underlying
subset of that base change in the base changed ambient scheme is exactly the inverse
image of C under the first pullback projection. Hence that inverse image is
irreducible. If the scheme is empty, use the identity extension; there are no
components and the universal assertion is vacuous.

(blueprint: lem-sbc-generic-components-split) -/
theorem exists_finite_etale_geometric_component_extension {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (L : Type u) (_ : Field L)
      (y : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k)),
      IsFinite y ∧ Etale y ∧
      ∀ A ∈ irreducibleComponents ↥(pullback f y),
        ∀ (E : Type u) (_ : Field E) (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of L)),
          IsIrreducible ((pullback.fst (pullback.snd f y) z) ⁻¹' A) := by sorry

end AlgebraicGeometry
