/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphismComparison
import WeilConjectures.AlgebraicGeometry.FiniteClosedPoints
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite

/-!
# Dominant morphisms of integral curves are quasi-finite at every point

Source: Stacks Project, Varieties, Tag 0AB6, condition (1), specialized to integral
separated curves of finite type over a field
(blueprint: lem-trf-birational-curve-quasifinite).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A dominant locally finite type morphism between integral separated curves of finite type
with finite induced function-field extension is quasi-finite at every point.
Source: Stacks Project, Varieties, Tag 0AB6, condition (1)
(blueprint: lem-trf-birational-curve-quasifinite).

The finite extension is expressed by finiteness of the canonical stalk map at the generic
point of `E`. Dominance identifies its image with the generic point of `C`, so this is exactly
finiteness of the induced map `k(C) → k(E)`, with the function fields defined as generic stalks
in `def-sc-function-field`.

Proof plan:
1. By `lem-sc-scheme-sober` and integrality, each curve has a unique generic point.
   Every other point is closed: otherwise a closed specialization, its closure and the
   whole curve give a chain of length two, contradicting
   `def-kun-topological-krull-dimension`. The generic point is not closed, since the
   dimension is one.
2. Continuity and dominance send the generic point of `E` to that of `C`.
3. The finite-type `k`-scheme `C` is Jacobson. Mathlib's
   `Scheme.Hom.closePoints_subset_preimage_closedPoints` then shows that the locally
   finite type morphism `p` sends closed points to closed points.
4. The generic fibre consists of the generic point of `E`. Every other fibre is a closed
   subset of `E` consisting of closed points, hence finite by
   `lem-kun-finite-closed-subscheme`; this also includes empty fibres.
5. Apply `pqf-lem-locqf-fibre-discrete` to each finite fibre, using local finite type.
   This gives quasi-finiteness at each point, in the Stacks sense of `pqf-def-quasifinite`.
   Separatedness and the finite generic extension remain among the hypotheses although
   this direct dimension-one proof does not require them. -/
theorem quasiFiniteAtPoint_of_dominant_integral_curves
    {k : Type u} [Field k] {C E : Scheme.{u}}
    [C.Over (Spec (.of k))] [E.Over (Spec (.of k))]
    [IsIntegral C] [IsIntegral E]
    [IsSeparated (C ↘ Spec (.of k))] [IsSeparated (E ↘ Spec (.of k))]
    [LocallyOfFiniteType (C ↘ Spec (.of k))] [QuasiCompact (C ↘ Spec (.of k))]
    [LocallyOfFiniteType (E ↘ Spec (.of k))] [QuasiCompact (E ↘ Spec (.of k))]
    (hC : topologicalKrullDim C = 1) (hE : topologicalKrullDim E = 1)
    (p : E ⟶ C) [p.IsOver (Spec (.of k))] [IsDominant p] [LocallyOfFiniteType p]
    (hfinite : (p.stalkMap (genericPoint E)).hom.Finite) :
    ∀ x : E, p.IsQuasiFiniteAtPoint x := by
  classical
  -- The dimension-one argument does not need the finite generic extension.
  have _ := hfinite
  have hclosed (X : Scheme.{u}) [IsIntegral X]
      (hd : topologicalKrullDim X = 1) (x : X) (hx : x ≠ genericPoint X) :
      IsClosed ({x} : Set X) := by
    have hη : genericPoint X ∉ closure ({x} : Set X) := by
      intro h
      exact hx ((specializes_iff_mem_closure.mpr h).antisymm
        (genericPoint_specializes x)).eq
    exact isClosed_closure.isOpen_compl.isClosed_singleton_of_mem_compl hd.le
      ⟨genericPoint X, hη⟩ (by simpa using (subset_closure (Set.mem_singleton x)))
  have hηC : ¬ IsClosed ({genericPoint C} : Set C) := by
    intro h
    have hsingleton : (Set.univ : Set C) = {genericPoint C} :=
      (genericPoint_closure C).symm.trans h.closure_eq
    have : Subsingleton C := ⟨fun a b ↦ by
      have ha : a ∈ ({genericPoint C} : Set C) := hsingleton ▸ Set.mem_univ a
      have hb : b ∈ ({genericPoint C} : Set C) := hsingleton ▸ Set.mem_univ b
      exact ha.trans hb.symm⟩
    have hz := topologicalKrullDim_zero_of_discreteTopology C
    rw [hC] at hz
    exact (by decide : ¬ (1 : WithBot ℕ∞) ≤ 0) hz
  have hpη : p (genericPoint E) = genericPoint C := by
    apply IsGenericPoint.eq (S := Set.univ) ?_ (genericPoint_spec C)
    simpa only [Set.image_univ, p.denseRange.closure_range] using
      (genericPoint_spec E).image p.continuous
  have : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace (C ↘ Spec (.of k))
  have himage (x : E) (hx : IsClosed ({x} : Set E)) : IsClosed ({p x} : Set C) :=
    p.closePoints_subset_preimage_closedPoints hx
  have hfib (y : C) : (p ⁻¹' {y}).Finite := by
    by_cases hy : y = genericPoint C
    · subst y
      apply (Set.finite_singleton (genericPoint E)).subset
      intro x hx
      by_contra hne
      have hxy : p x = genericPoint C := hx
      apply hηC
      rw [← hxy]
      exact himage x (hclosed E hE x hne)
    · apply IsClosed.finite_of_finiteType_over_field_of_closed_points
        (E ↘ Spec (.of k)) ((hclosed C hC y hy).preimage p.continuous)
      intro x hx
      apply hclosed E hE x
      intro h
      have hxy : p x = y := hx
      rw [h, hpη] at hxy
      exact hy hxy.symm
  intro x
  exact (p.isQuasiFiniteAtPoint_iff_quasiFiniteAt x).mpr
    ((p.discreteTopology_fiber_and_quasiFiniteAt (p x) (hfib (p x))).2.2 x rfl)

end AlgebraicGeometry
