/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.FiniteFieldClosedComponentDescent
import WeilConjectures.AlgebraicGeometry.ClosedComponentDescentTopology

/-!
# Finite descent of irreducible components from a separable closure

Source: Stacks Project, Tag 04KZ, parts (1) and (2), and Tag 054R.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicGeometry

/-- When the base change to a separable closure has finitely many components, one finite
intermediate field makes the inverse image of each component a single component.

Source: Stacks Project, Tag 04KZ, parts (1) and (2), and the proof of Tag 054R. -/
theorem exists_finite_intermediateField_component_preimages {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hfinite : (irreducibleComponents
      ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k (SeparableClosure k)))))).Finite) :
    ∃ L : IntermediateField k (SeparableClosure k),
      Module.Finite k L ∧
      ∀ A ∈ irreducibleComponents
        ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L)))),
        (pullback.fst
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
          (Spec.map (CommRingCat.ofHom L.subtype))) ⁻¹' A ∈
            irreducibleComponents
              ↥(pullback
                (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
                (Spec.map (CommRingCat.ofHom L.subtype))) := by
  obtain ⟨L, hL, hsurj, hfin, hdesc⟩ :=
    exists_finite_intermediateField_closed_component_descent f hfinite
  refine ⟨L, hL, ?_⟩
  exact component_preimages_of_closed_descent _ (Scheme.Hom.continuous _) hsurj hfin hdesc

end AlgebraicGeometry
