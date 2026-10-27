/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q114
-/
module

public import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
import Sheaf.AlgebraicGeometry.SpaceOpenChartTests
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus

/-! # Open graphs of morphisms into an étale algebraic space

Source: Rydh, Submersions and effective descent of étale morphisms, Appendix A,
Corollary (A.3) and Proposition (A.2), printed p. 35; Stacks Project, Tags 05W5,
03FT, 03FU, 03FV and 03BZ (blueprint: lem-sfb-space-etale-open-graph).

Graphs are actual image subfunctors. The universal point condition tests the first
projection after every algebraic-space base change. The inverse correspondence uses
an isomorphism of the underlying presheaves, hence of the represented algebraic spaces.
No representability, quasi-compactness or separation of the étale target map is imposed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The graph of a morphism over `B`, as an image subfunctor of the sheaf fibre product.
Source: Rydh, Appendix A, Corollary (A.3), the graph construction
(blueprint: lem-sfb-space-etale-open-graph). -/
def etaleGraphSubfunctor {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (a : {a : X ⟶ Y // a ≫ g = f}) :
    Subfunctor (enlargedFibreProduct f g).obj.obj :=
  Subfunctor.range (Limits.pullback.lift (𝟙 X.obj) a.val.hom
    (by simpa using congrArg (fun k ↦ k.hom) a.property.symm)).hom

/-- The graph projection is surjective and universally injective on point classes:
its point map is bijective after every algebraic-space base change to `X`.
Source: Rydh, Appendix A, Corollary (A.3); Stacks Project, Tags 040X and 05W5
(blueprint: lem-sfb-space-etale-open-graph). -/
def EtaleGraphPointCondition {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (A : OpenSubspace (enlargedFibreProduct f g)) : Prop :=
  ∀ (T : AlgebraicSpace S) (t : T ⟶ X),
    Function.Bijective (mapPoint (Limits.pullback.snd
      (A.val.ι ≫ (Limits.pullback.fst f.hom g.hom).hom) t.hom.hom))

/-- Morphisms into a chartwise étale algebraic space are classified by open graph
subfunctors with universally bijective first projection. The isomorphism `e` identifies
that projection, and its inverse followed by the second projection recovers the morphism.
Source: Rydh, Appendix A, Corollary (A.3) and Proposition (A.2), printed p. 35;
Stacks Project, Tags 05W5, 040X and 03BZ (blueprint: lem-sfb-space-etale-open-graph).

Proof:
1. The fibre product exists by lem-trf-space-fibre-products-etale-covers. Its projection
   to X is chartwise étale by lem-trf-space-chartwise-etale-permanence. A graph is its
   section, so the over-base permanence clause makes it chartwise étale. It is injective
   on every scheme's sections; lem-sfb-space-etale-monomorphism-open makes its image
   an open subspace. The first projection has the graph section as its inverse, also
   after every base change. Thus the displayed universal point condition holds.
2. For an admissible open subspace A, lem-a1-space-open-chart-tests makes its inclusion
   chartwise étale. Composing with the first projection makes q : A -> X chartwise étale.
3. In R = A ×_X A, the first projection r is a base change of q, hence injective on
   points. Its diagonal section delta satisfies r delta = id. For each point z of R,
   injectivity applied to r(delta(r(z))) = r(z) gives delta(r(z)) = z. Thus delta is
   surjective on points, without asserting that point spaces preserve fibre products.
4. Permanence makes delta chartwise étale. It is a monomorphism, hence an open immersion
   by lem-sfb-space-etale-monomorphism-open. Its full point image makes it an isomorphism
   by lem-a1-space-point-open-calculus. Therefore q is a sheaf monomorphism. The same
   two results make q an open immersion and, by its surjectivity on points, an isomorphism.
5. Compose q inverse with the inclusion and second projection. The fibre-product equation
   makes this a B-morphism. Its graph is the original subfunctor, since on sections its
   graph section is precisely the inclusion composed with q inverse. Conversely, the
   graph of a given morphism has inverse first projection x -> (x,a(x)); its second
   projection recovers a. These identities give existence and uniqueness, as subfunctors.
-/
theorem space_etale_open_graph {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (hg : IsChartwiseEtale g) :
    (∀ a : {a : X ⟶ Y // a ≫ g = f},
      ∃ A : OpenSubspace (enlargedFibreProduct f g),
        A.val = etaleGraphSubfunctor f g a ∧ EtaleGraphPointCondition f g A) ∧
    (∀ A : OpenSubspace (enlargedFibreProduct f g), EtaleGraphPointCondition f g A →
      (∃! a : {a : X ⟶ Y // a ≫ g = f}, etaleGraphSubfunctor f g a = A.val) ∧
      ∃ e : A.val.toFunctor ≅ X.obj.obj,
        e.hom = A.val.ι ≫ (Limits.pullback.fst f.hom g.hom).hom ∧
        ∀ a : {a : X ⟶ Y // a ≫ g = f}, etaleGraphSubfunctor f g a = A.val →
          a.val.hom.hom = e.inv ≫ A.val.ι ≫
            (Limits.pullback.snd f.hom g.hom).hom) := by
  sorry

/-- Both directions of the open-graph correspondence commute with arbitrary base change
in `B`. The cartesian squares allow any models of the base-changed spaces; the equations
for `m` uniquely characterize the canonical map from their product to the old product.
The final clause expresses naturality of the inverse correspondence by its uniquely
recovered morphisms, whose explicit inverse-projection formula is in `space_etale_open_graph`.
Source: Rydh, Appendix A, Corollary (A.3), base-change functoriality
(blueprint: lem-sfb-space-etale-open-graph).

Proof: Step 6 of the node. For b : B1 -> B, identify the pulled-back product on sections
by ((x,y),t) -> ((x,t),(y,t)), with inverse forgetting the repeated t. This gives m
with its stated projections, using lem-trf-space-fibre-products-etale-covers. A graph
pulls back to the pairs ((x,t),(a(x),t)), exactly the graph of the unique pulled-back
morphism. Its uniqueness follows from the cartesian square for Y1. Open subspaces
remain open because each new scheme test is the old scheme test composed with m
(def-a1-space-open-subspace). The projection remains an isomorphism: pulling back
both inverse identities gives its inverse. Consequently the universal point conditions
persist. Finally, taking the second projection of this pulled-back inverse recovers
precisely the base-changed morphism. Equivalently, the two recovered graph morphisms
satisfy a1 followed by y = x followed by a, which is the last displayed equality. -/
theorem space_etale_open_graph_baseChange {S : Scheme.{u}}
    {X Y B X₁ Y₁ B₁ : AlgebraicSpace S}
    (f : X ⟶ B) (g : Y ⟶ B) (hg : IsChartwiseEtale g)
    (f₁ : X₁ ⟶ B₁) (g₁ : Y₁ ⟶ B₁) (b : B₁ ⟶ B) (x : X₁ ⟶ X) (y : Y₁ ⟶ Y)
    (hx : IsPullback x.hom f₁.hom f.hom b.hom)
    (hy : IsPullback y.hom g₁.hom g.hom b.hom) :
    ∃ m : (enlargedFibreProduct f₁ g₁).obj.obj ⟶ (enlargedFibreProduct f g).obj.obj,
      m ≫ (Limits.pullback.fst f.hom g.hom).hom =
        (Limits.pullback.fst f₁.hom g₁.hom).hom ≫ x.hom.hom ∧
      m ≫ (Limits.pullback.snd f.hom g.hom).hom =
        (Limits.pullback.snd f₁.hom g₁.hom).hom ≫ y.hom.hom ∧
      (∀ a : {a : X ⟶ Y // a ≫ g = f},
        ∃! a₁ : {a₁ : X₁ ⟶ Y₁ // a₁ ≫ g₁ = f₁},
          a₁.val ≫ y = x ≫ a.val ∧
          etaleGraphSubfunctor f₁ g₁ a₁ = (etaleGraphSubfunctor f g a).preimage m) ∧
      ∀ A : OpenSubspace (enlargedFibreProduct f g), EtaleGraphPointCondition f g A →
        ∃ A₁ : OpenSubspace (enlargedFibreProduct f₁ g₁),
          A₁.val = A.val.preimage m ∧ EtaleGraphPointCondition f₁ g₁ A₁ ∧
          ∀ (a : {a : X ⟶ Y // a ≫ g = f})
            (a₁ : {a₁ : X₁ ⟶ Y₁ // a₁ ≫ g₁ = f₁}),
            etaleGraphSubfunctor f g a = A.val →
            etaleGraphSubfunctor f₁ g₁ a₁ = A₁.val → a₁.val ≫ y = x ≫ a.val := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
