/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q141
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Irreducible
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sets.Closeds

/-!
# Finite geometric decomposition above an irreducible component

Source: Stacks Project, Varieties, Tag 04KZ (3), with the algebraic-closure comparison
of Tag 038H, as used in the first proof paragraph of Tag 04L7
(blueprint: lem-sfb-geometric-component-finite-preimage).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Above each irreducible component, extension to an algebraic closure gives a nonempty
finite union of irreducible components, for a scheme locally of finite type over a field.

Source: Stacks Project, Varieties, Tags 04KZ (3), 038H and 04L7
(blueprint: lem-sfb-geometric-component-finite-preimage).

Proof:
1. Choose a point t of T and a finite-type affine open U = Spec A of X containing t
   (`def-weil-finite-type-morphism`). Its inverse image V is the base-changed open subscheme
   (`def-pc-fibre-product`, `lem-weil-pbc-open-immersion-base-change`,
   `def-weil-open-immersion`). By `lem-weil-pbc-fibre-product-affine-spectra` it is
   Spec (A tensor K). The images of finitely many algebra generators of A generate this
   tensor product over K. Hence V has finitely many components by
   `lem-wf-affine-noetherian-components`.
2. Let S be the components of the base change contained in the preimage of T. By
   `lem-sfb-field-extension-irreducible-components`, this preimage is nonempty and is the
   union of S. Every C in S has actual image a component of X contained in T, hence equal
   to T by maximality (`def-weil-irreducible-components`). Thus every C meets V above t.
3. By `lem-weil-pbc-open-subspace-irreducible-closed-correspondence`, C intersect V is
   irreducible closed in V and its closure upstairs is C. It is a component of V: any
   larger irreducible closed subset would have closure containing C, contradicting
   maximality. Equal restrictions have equal closures, so restriction injects S into
   the finite set of components of V. Therefore S is finite.
4. Enumerate the nonempty finite S by Fin n, with n positive. Step 2 gives the asserted
   equality of the full preimage with the union. This argument uses just one affine
   chart meeting T, and imposes no global finiteness, connectedness or reducedness.
   For the empty scheme there is no component T, so the assertion is vacuous. -/
theorem exists_finite_geometric_irreducibleComponents_preimage
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsAlgClosure k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (T : Set X) (hT : T ∈ irreducibleComponents X) :
    ∃ n : ℕ, 0 < n ∧
      ∃ C : Fin n → Set ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
        (∀ i : Fin n, C i ∈ irreducibleComponents
          ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) ∧
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ⁻¹' T =
          ⋃ i : Fin n, C i := by
  sorry

end AlgebraicGeometry
