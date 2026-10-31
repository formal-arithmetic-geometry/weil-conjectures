/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic

/-!
# Scheme charts over a pulled-back étale covering

Source: Stacks Project, Properties of Spaces, Tags 03G2 and 03GA;
Modules on Sites, Tag 03DO, covering step of the proof
(blueprint: lem-sfb-space-module-chart-cover).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- All commuting scheme charts over a covering of the target cover the source.
Source: Stacks Project, Properties of Spaces, Tag 03G2; Modules on Sites,
Tag 03DO, proof, the covering obtained by base change
(blueprint: lem-sfb-space-module-chart-cover).

Proof: regard the target scheme charts as objects of the enlarged étale site.
Their covering condition on every small-site object implies that they cover the
final enlarged object: first restrict to a surjective étale scheme atlas of the
space, and then use the covering sieve supplied by `hV` on that atlas. Base change
along `f` preserves this covering. Refine every resulting algebraic-space object
by a surjective étale scheme atlas. A refined chart has a map to the original
scheme chart and hence is an object of `ModuleChart f (V i)`. The composites of
these atlases form an étale covering of the source. On any source scheme object,
base change this covering and refine once more by scheme atlases. Thus the sieve
of all objects `q.left` is covering on that object, precisely `CoversTop`.
The empty family is allowed: its covering hypothesis forces the target, and
therefore the source, to be empty. No representability of `f` is used. -/
theorem moduleChart_coversTop {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {I : Type w} (V : I → Y.EtaleSite)
    (hV : Y.etaleTopology.CoversTop V) :
    X.etaleTopology.CoversTop
      (fun p : Σ i, ModuleChart f (V i) ↦ p.2.left) := by sorry

end AlgebraicGeometry.AlgebraicSpace
