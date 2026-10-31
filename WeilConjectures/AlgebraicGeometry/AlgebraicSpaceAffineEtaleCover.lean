/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePointClasses
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Topology.Defs.Induced
import WeilConjectures.AlgebraicGeometry.SpaceAtlasOpenRefinementPullback
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceAtlasPointComparison
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceAtlasTestOpenSubsets

/-!
# Affine étale atlases and the topology of an algebraic space

Source: Stacks Project, Properties of Spaces, Tags 03FX and 03BX
(blueprint: lem-a1-space-affine-etale-cover).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space admits a disjoint-union affine étale atlas over affine opens of
its base. Its point topology is the quotient topology for any surjective étale scheme
atlas. Every map from a scheme is continuous on points; an étale one is open, with open
image. Source: Stacks, Tags 03FX, 03BX (blueprint: lem-a1-space-affine-etale-cover).

Proof: (1) Choose an atlas V → E. Refine V by affine opens lying over affine opens of S
using lem-weil-pbc-affine-opens-basis and
lem-weil-pbc-morphism-factors-through-open-subscheme. Their coproduct W exists by
lem-weil-pbc-scheme-coproduct-family, with its displayed component factorizations.
(2) On any scheme test, pull back V and its open refinement. The coproduct of these
pullbacks represents the pullback of W. The projections are étale by
lem-weil-pbc-open-immersion-base-change and lem-weil-pbc-etale-composition-cancellation,
and jointly cover the test, proving representable surjective étaleness. Testing at a
field spectrum and taking a residue field proves surjectivity on point classes.
(3) Give the point set the quotient topology from W. For another atlas V, the scheme
W ×_E V has open surjective étale projections by lem-weil-pbc-etale-morphism-open-map.
The equality of inverse images follows from lem-a1-space-fibre-product-point. It shows
that either atlas detects precisely the same open subsets.
(4) For T → E, pull back W. The surjective étale projection to T is open, and hence
detects open subsets. Pulling back an open subset of E therefore proves continuity.
(5) If T → E is étale, the other projection to W is open. The fibre-product point
criterion identifies its image of the inverse image of B with the inverse image in W
of the image of B in E. The quotient criterion proves openness, including the image
of all of T. These arguments also cover the empty atlas and empty space. -/
theorem exists_affine_etale_cover_and_point_topology {S : Scheme.{u}}
    (E : AlgebraicSpace S) :
    ∃ (W : Over S) (w : yoneda.obj W ⟶ E.obj.obj)
      (I : Type u) (A : I → Scheme.{u}) (ι : ∀ i : I, A i ⟶ W.left),
      Nonempty (IsColimit (Cofan.mk W.left ι)) ∧
      (∀ i : I, IsAffine (A i)) ∧
      (∀ i : I, ∃ (U : S.Opens) (_ : IsAffineOpen U) (a : A i ⟶ U.toScheme),
        a ≫ U.ι = ι i ≫ W.hom) ∧
      IsRepresentable w ∧ IsSurjective w ∧ IsEtale w ∧
      Function.Surjective (schemePointMap w) ∧
      ∃ τ : TopologicalSpace (Point E.obj.obj),
        τ = TopologicalSpace.coinduced (schemePointMap w) inferInstance ∧
        (∀ (V : Over S) (p : yoneda.obj V ⟶ E.obj.obj),
          IsRepresentable p → IsSurjective p → IsEtale p →
          τ = TopologicalSpace.coinduced (schemePointMap p) inferInstance) ∧
        (∀ (T : Over S) (t : yoneda.obj T ⟶ E.obj.obj),
          @Continuous T.left (Point E.obj.obj) inferInstance τ (schemePointMap t) ∧
          (IsEtale t →
            @IsOpenMap T.left (Point E.obj.obj) inferInstance τ (schemePointMap t) ∧
            @IsOpen (Point E.obj.obj) τ (Set.range (schemePointMap t)))) := by
  classical
  obtain ⟨V, p, hpEt, hpSurj⟩ := E.property.2
  have hp : IsRepresentable p := by
    intro T t
    obtain ⟨P, q, a, h, _⟩ := hpEt T t
    exact ⟨P, q, a, h, trivial⟩
  obtain ⟨hrefine, I, U, j, hj, hcover, hAffine, hbase⟩ :=
    space_atlas_open_refinement_pullback E V p hp hpEt hpSurj
  obtain ⟨_, hwRep, hwSurj, hwEt, hwPoints⟩ := hrefine I U j hj hcover
  let W : Over S := ∐ U
  let w : yoneda.obj W ⟶ E.obj.obj := yoneda.map (Sigma.desc j) ≫ p
  refine ⟨W, w, I, fun i ↦ (U i).left, fun i ↦ (Sigma.ι U i).left,
    ⟨isColimitOfHasCoproductOfPreservesColimit (Over.forget S) U⟩,
    hAffine, ?_, hwRep, hwSurj, hwEt, hwPoints, ?_⟩
  · intro i
    obtain ⟨B, hB, b, hb⟩ := hbase i
    exact ⟨B, hB, b, hb.trans (Over.w (Sigma.ι U i)).symm⟩
  · let τ := TopologicalSpace.coinduced (schemePointMap w) inferInstance
    let : TopologicalSpace (Point E.obj.obj) := τ
    refine ⟨τ, rfl, ?_, ?_⟩
    · intro V' p' _ hpSurj' hpEt'
      obtain ⟨Q, a, b, _, _, _, _, _, _, _, _, _, _, hsubsets⟩ :=
        exists_atlas_point_comparison E W V' w p' hwEt hwSurj hpEt' hpSurj'
      apply TopologicalSpace.ext
      funext A
      exact propext (hsubsets A).2.2
    · intro T t
      obtain ⟨Q, q, b, _, _, _, _, _, hpreimage, _, himage⟩ :=
        exists_atlas_test_open_subsets E W T w t hwEt hwSurj
      refine ⟨?_, ?_⟩
      · apply continuous_def.mpr
        intro A hA
        exact (hpreimage A).2.2 hA
      · intro ht
        have hopen : IsOpenMap (schemePointMap t) := by
          intro B hB
          exact (himage ht).2 B hB
        exact ⟨hopen, hopen.isOpen_range⟩

end AlgebraicGeometry.AlgebraicSpace
