/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober

import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.GenericComponentsSplit
import WeilConjectures.AlgebraicGeometry.GeometricGenericCoverSpread

/-! # Split generic components and a uniform upper bound

Source: literature/stacks-project/more-morphisms.tex, Tag 055A,
second and final proof paragraphs; Tags 0551 and 055G.
(blueprint: lem-trf-generic-split-component-upper-bound)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicGeometry

/-- A finite type morphism over an irreducible base admits a finite etale generic
field extension whose distinct geometric components bound the number of components
of every field extension of nearby fibres. Field extensions are represented by
morphisms between field spectra, equivalently by their injective unital ring maps.
The number of components may be zero.

Source: literature/stacks-project/more-morphisms.tex, Tag 055A,
second and final proof paragraphs; Tags 0551 and 055G.
(blueprint: lem-trf-generic-split-component-upper-bound)

Proof:
1. Finite type is stable under base change
   (lem-sfb-finite-type-composition-base-change). Apply
   lem-sbc-generic-components-split to the generic fibre to obtain the finite etale
   field extension and the geometric irreducibility of every component. The new
   fibre is finite type over a field, hence Noetherian
   (lem-weil-pbc-finite-type-over-noetherian). Its components are finite in number
   (lem-weil-pbc-noetherian-finitely-many-components), closed, and cover it
   (def-weil-irreducible-components, lem-sc-irreducible-components-cover).
   Enumerate them without repetitions by Fin n. If n = 0, their cover is empty.
2. Apply lem-sbc-geometric-generic-cover-spread to precisely this finite closed
   cover. It gives an open neighbourhood of the generic point. For each point of
   that open and each test field extension, there is a surjection from a scheme Z
   covered by n nonempty irreducible subsets B_i to the test fibre Y.
3. The closures C_i of the images of B_i are nonempty irreducible closed subsets
   covering Y. Any irreducible component D of Y is covered by the finitely many
   relatively closed subsets D intersect C_i. Induction using the closed two-set
   definition of irreducibility puts D inside one C_i; maximality gives D = C_i.
   Assign D the least such index. This injects the components into Fin n. For
   n = 0 the cover forces Z to be empty, and surjectivity forces Y to be empty.
-/
theorem exists_generic_split_component_upper_bound
    {X S : Scheme.{u}} [IrreducibleSpace S]
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f]
    (η : S) (hη : IsGenericPoint η (Set.univ : Set S)) :
    ∃ (L : Type u) (_ : Field L)
      (a : Spec (CommRingCat.of L) ⟶ Spec (S.residueField η))
      (n : ℕ) (W : Set S)
      (A : Fin n → Set ↥(pullback (f.fiberToSpecResidueField η) a)),
      IsFinite a ∧ Etale a ∧ IsOpen W ∧ η ∈ W ∧
      Function.Injective A ∧
      Set.range A = irreducibleComponents ↥(pullback (f.fiberToSpecResidueField η) a) ∧
      (⋃ i, A i) = Set.univ ∧
      (∀ (i : Fin n) (E : Type u) (_ : Field E)
        (z : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of L)),
        IsIrreducible ((pullback.fst
          (pullback.snd (f.fiberToSpecResidueField η) a) z) ⁻¹' A i)) ∧
      ∀ s ∈ W, ∀ (K : Type u) (_ : Field K)
        (y : Spec (CommRingCat.of K) ⟶ Spec (S.residueField s)),
        (∃ j : ↥(irreducibleComponents ↥(pullback (f.fiberToSpecResidueField s) y)) →
            Fin n, Function.Injective j) ∧
        (n = 0 → IsEmpty ↥(pullback (f.fiberToSpecResidueField s) y)) := by
  sorry

end AlgebraicGeometry
