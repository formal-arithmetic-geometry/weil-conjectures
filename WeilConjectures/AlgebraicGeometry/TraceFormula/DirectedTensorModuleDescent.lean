/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
public import Mathlib.AlgebraicGeometry.Cover.Directed
import WeilConjectures.AlgebraicGeometry.TraceFormula.DirectedTensorMatchingSections

/-! # Module descent on a locally directed open cover

Source: Stacks Project, Sheaves, Tags 00AL, 00AM and 04TN; Constructions, Tag 01LI.
(blueprint: lem-trf-directed-tensor-module-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- A coherent family of module isomorphisms on a locally directed open cover is effective.

Source: Stacks Project, Sheaves, Tags 00AL, 00AM and 04TN, applied after the common-refinement
construction of Constructions, Tag 01LI. This is the general module gluing step, independent
of graded algebras, relative Proj, twists, and fraction normalizations.

Proof: Identify each cover member with its open image in X. The unique comparison of the
section-normalized tensor pullback with ordinary restriction identifies each t(f) with a
restriction isomorphism; uniqueness of left adjoints identifies the specified composition
comparison with the restriction associator. Thus ht is the usual restriction cocycle.
The identity case follows by applying ht to two identity arrows and cancelling the
invertible transition; the pullback unit and associator laws identify the remaining map
with the canonical restriction unit.
On the intersection of members i and j, the common refinements k with maps to i and j form
an open cover, by local directedness. On such a member the overlap map from M(i) to M(j)
is t(k to i) followed by the inverse of t(k to j). On a further common refinement the two
maps agree by ht. Two different common refinements agree after refining their intersection
again, so 04TN glues these maps and their inverses to an overlap isomorphism. This argument
also applies to empty intersections. On a triple intersection, refine simultaneously
inside all three members; cancellation of t and its inverse gives the overlap cocycle.
Apply glue_sheaves_of_modules, object clause, to the resulting modules on the open images
and their overlap isomorphisms. It gives L and local isomorphisms. The compatibility from
that clause, restricted to the member i contained in j, says exactly that t(f) composed
with the pullback of chart(j) equals chart(i), after the displayed equality transport and
section-normalized composition comparison. Transport the open-image identifications back
to the original cover members to obtain chart. No quasi-coherence or finiteness is needed;
the empty cover gives the module on the empty scheme.
(blueprint: lem-trf-directed-tensor-module-descent). -/
theorem exists_directed_tensor_module_descent
    {X : Scheme.{u}} (𝒰 : X.OpenCover.{u}) [Category.{v} 𝒰.I₀]
    [𝒰.LocallyDirected] [Quiver.IsThin 𝒰.I₀]
    (M : ∀ i : 𝒰.I₀, (𝒰.X i).Modules)
    (t : ∀ {i j : 𝒰.I₀} (f : i ⟶ j), (tensorPullback (𝒰.trans f)).obj (M j) ≅ M i)
    (ht : ∀ {i j k : 𝒰.I₀} (f : i ⟶ j) (g : j ⟶ k),
      t (f ≫ g) =
        eqToIso (congrArg (fun a ↦ (tensorPullback a).obj (M k)) (𝒰.trans_comp f g)) ≪≫
          (tensorPullbackSectionComp (𝒰.trans f) (𝒰.trans g)).app (M k) ≪≫
          (tensorPullback (𝒰.trans f)).mapIso (t g) ≪≫ t f) :
    ∃ (L : X.Modules) (chart : ∀ i : 𝒰.I₀, (tensorPullback (𝒰.f i)).obj L ≅ M i),
      ∀ {i j : 𝒰.I₀} (f : i ⟶ j),
        eqToIso (congrArg (fun a ↦ (tensorPullback a).obj L) (𝒰.trans_map f).symm) ≪≫
          (tensorPullbackSectionComp (𝒰.trans f) (𝒰.f j)).app L ≪≫
          (tensorPullback (𝒰.trans f)).mapIso (chart j) ≪≫ t f = chart i := by
  refine ⟨tensorMatchingModule 𝒰 M t, tensorMatchingChartIso 𝒰 M t ht, ?_⟩
  intro i j f
  exact tensorMatchingChartIso_condition 𝒰 M t ht f

end AlgebraicGeometry.Scheme.Modules
