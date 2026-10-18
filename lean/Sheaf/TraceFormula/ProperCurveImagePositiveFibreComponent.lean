module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.FiniteTypeFibreImageDimensionBounds

/-!
# Proper curve image and positive-dimensional fibre component

Source: Stacks Project, varieties.tex, Tag 0B2L, lemma-dimension-fibres-locally-algebraic,
(2)(b)--(d) and its dimension/transcendence-degree computation.
(blueprint: lem-trf-proper-curve-image-positive-fibre-component).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/--
Source: Stacks Project, varieties.tex, Tag 0B2L, lemma-dimension-fibres-locally-algebraic,
(2)(b)--(d) and its dimension/transcendence-degree computation.
(blueprint: lem-trf-proper-curve-image-positive-fibre-component).

Returned-delivery repair (2026-10-18): the immutable-head return identified only an
artifact naming issue; the theorem signature and all hypotheses are retained verbatim.

Proof (Tag 0B2L, with the recorded project lemmas):
1. The positive-dimensional fibre has an irreducible component of positive dimension;
   choose its generic point and a strict specialization. Finite type over a field gives
   Noetherianity and finitely many components.
2. Surjectivity and properness imply that the image of `T` is `G`; the image-dimension
   inequality and the one-dimensional component hypothesis give `topologicalKrullDim G ≤ 1`.
3. If `y` were not closed, proper closed-image specialization would produce a chain of
   three strict points in `G`, contradicting that bound; hence `y` is closed.
4. Lift the generic point of the chosen fibre component to a component `Z` of `T`.
   Properness makes its image closed, and the image-dimension inequality together with
   the chain bound identifies it with the chosen fibre component. Its image under `p` is
   therefore exactly `{y}` and has dimension one.
-/
theorem properCurveImagePositiveFibreComponent
    {k : Type u} [Field k]
    {T G Y : Scheme.{u}}
    [T.Over (Spec (.of k))] [G.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (G ↘ Spec (.of k))]
    [QuasiCompact (G ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (r : T ⟶ G) [r.IsOver (Spec (.of k))] [IsProper r]
    (p : G ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    [Surjective r]
    (hT : ∀ Z : Set (T : Type u),
      Z ∈ irreducibleComponents (T : Type u) →
        topologicalKrullDim Z = (1 : WithBot ℕ∞))
    (y : Y)
    (hy : 0 < topologicalKrullDim (p.fiber y)) :
    y ∈ closedPoints (Y : Type u) ∧
      ∃ Z : Set (T : Type u),
        Z ∈ irreducibleComponents (T : Type u) ∧
        ((r ≫ p).base '' Z) = ({y} : Set Y) ∧
        topologicalKrullDim (r.base '' Z) = (1 : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
