/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsSepClosed

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicGeometry

/-- All components over a separable closure simultaneously descend to closed subsets over
one finite intermediate field.

Source: Stacks Project, Tag 04KZ (1),(2), and Tag 054R, proof.
Proof: for each geometric component choose an affine open U of X meeting it after base
change. The coordinate ring of U is finite type over k, so its base change is noetherian.
The minimal prime defining the component on this chart has finitely many generators.
Write each generator as a finite sum of tensors and adjoin their ksep coefficients for
all components. There are finitely many coefficients, and algebraicity makes their
intermediate field L finite over k. Every automorphism fixing L preserves each chosen
chart and fixes the ideal generators, hence fixes the component on that chart. Its
closure is the entire component, which is therefore fixed. Since ksep/L is algebraic,
normal and separable, it is Galois, even if L/k is not normal.
Descent of invariant closed subsets (Stacks Tag 038B, applied over L) supplies closed
subsets of X_L whose full preimages are those components. The projection is surjective
by faithful flatness of field extension. The pullback tower isomorphism identifies the
iterated base change with X_ksep and transports the given finiteness of components.
For empty X take the bottom field and use the vacuous component assertion.
(blueprint: new-lem-sbc-finite-field-closed-component-descent) -/
theorem exists_finite_intermediateField_closed_component_descent {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hfinite : (irreducibleComponents
      ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (SeparableClosure k)))))).Finite) :
    ∃ L : IntermediateField k (SeparableClosure k),
      Module.Finite k L ∧
      let Z := pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L)))
      let Y := pullback
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
        (Spec.map (CommRingCat.ofHom L.subtype))
      let p : Y ⟶ Z := pullback.fst
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
        (Spec.map (CommRingCat.ofHom L.subtype))
      Function.Surjective p ∧ (irreducibleComponents ↥Y).Finite ∧
        ∀ C ∈ irreducibleComponents ↥Y,
          ∃ A : Set Z, IsClosed A ∧ p ⁻¹' A = C := by sorry

end AlgebraicGeometry
