/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Sheaf.AlgebraicGeometry.ClosedPointField
import Sheaf.AlgebraicGeometry.FiniteClosedPoints
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
3. A closed point of `E` has residue field finite over `k` by
   `lem-kun-closed-point-field`. The residue-field map of `def-weil-residue-field` embeds
   the residue field of its image into that finite extension. The converse in
   `lem-kun-closed-point-field` makes the image closed in `C`.
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
  sorry

end AlgebraicGeometry
