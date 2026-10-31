/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.JacobsonSpace

/-!
# Closed fibres under separation of closed points

Source: Stacks Project, Tag 0E8S, proof after condition (1), with Tag 0478
(blueprint: lem-sc-point-tangent-closed-fibre-singleton).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For a scheme locally of finite type over an algebraically closed field, a morphism
injective on closed points has empty or singleton fibres over closed points, with the singleton
point closed in the source. Source: Stacks Project, Tag 0E8S, proof after condition (1),
with Tag 0478 (blueprint: lem-sc-point-tangent-closed-fibre-singleton).

Proof: The source is Jacobson because it is locally of finite type over a field.
The fibre over the closed point `p` is closed by continuity. If it is nonempty,
it contains a point `x` closed in `X`, by the Jacobson property. Injectivity on
closed points implies that its intersection with `closedPoints X` is exactly `{x}`.
The closure of this intersection is the whole fibre, again by the Jacobson property.
Since `x` is closed, that closure is `{x}`, as required. -/
theorem preimage_singleton_eq_empty_or_singleton_of_injOn_closedPoints
    (k : Type u) [Field k] [IsAlgClosed k] (X Y : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] (f : X ⟶ Y)
    (hf : Set.InjOn f (closedPoints X)) (p : Y) (hp : p ∈ closedPoints Y) :
    f ⁻¹' {p} = ∅ ∨ ∃ x : X, x ∈ closedPoints X ∧ f ⁻¹' {p} = {x} := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace
    (X ↘ Spec (CommRingCat.of k))
  have hF : IsClosed (f ⁻¹' {p}) := hp.preimage f.continuous
  rcases (f ⁻¹' {p}).eq_empty_or_nonempty with hempty | hne
  · exact Or.inl hempty
  · obtain ⟨x, ⟨hx, hxc⟩⟩ := nonempty_inter_closedPoints hne hF.isLocallyClosed
    refine Or.inr ⟨x, hxc, ?_⟩
    have hclosed : f ⁻¹' {p} ∩ closedPoints X = {x} := by
      apply Set.Subset.antisymm
      · intro y hy
        exact Set.mem_singleton_iff.mpr (hf hy.2 hxc (hy.1.trans hx.symm))
      · exact Set.singleton_subset_iff.mpr ⟨hx, hxc⟩
    calc
      f ⁻¹' {p} = closure (f ⁻¹' {p} ∩ closedPoints X) :=
        (closure_inter_closedPoints hF).symm
      _ = {x} := by rw [hclosed, hxc.closure_eq]

end AlgebraicGeometry
