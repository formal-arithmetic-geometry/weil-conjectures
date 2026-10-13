/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso
public import Sheaf.AlgebraicGeometry.OpenCoverTensorPullbackComparison

/-! # Composition square for restriction and tensor pullback
Source: Stacks Project, Sheaves on Spaces, Tags 0095 and 0096.
(blueprint: lem-pc-open-cover-tensor-pullback-composition). -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
attribute [local irreducible] tensorPullback openCoverTensorPullbackComparison

/-- Restriction comparisons commute with two successive tensor pullbacks.
Source: Stacks Project, Tags 0095 and 0096, pullback and its adjunction.
(blueprint: lem-pc-open-cover-tensor-pullback-composition).
Proof: The hypotheses identify the two projections of the supplied chart
isomorphism with those of the iterated pullback chart. Expand the three
restriction comparisons into ordinary pullback composition and the unique
comparison of left adjoints to pushforward. Transpose the resulting square
through the tensor and ordinary pullback adjunctions. Mates preserve horizontal
and vertical composition, and the unique comparison of left adjoints is the
mate of the identity on pushforward. Hence every intermediate comparison
cancels. On right adjoints the remaining square is pushforward associativity
and the two projection equations hs and hk. On sections over each open it is
just the same restriction map on both sides. Injectivity of the mate
correspondence proves the square of left adjoints; evaluate at M. The assertion
holds for every module, including zero, and for empty charts and identity maps.
There is no local map, global morphism or recovery hypothesis in this square. -/
theorem openCoverTensorPullbackComparison_composition
    {X Y Z : Scheme.{u}} (q : Y ⟶ X) (p : Z ⟶ Y) (b : Z ⟶ X)
    (wpq : p ≫ q = b) (U₀ : X.OpenCover.{u}) (α : U₀.I₀)
    (s : ((U₀.pullback₁ q : Y.OpenCover.{u}).pullback₁ p : Z.OpenCover.{u}).X α ≅
      (U₀.pullback₁ b).X α)
    (hs : s.hom ≫ (U₀.pullback₁ b).f α =
      ((U₀.pullback₁ q : Y.OpenCover.{u}).pullback₁ p : Z.OpenCover.{u}).f α)
    (hk : s.hom ≫ U₀.pullbackHom b α =
      Scheme.Cover.pullbackHom (U₀.pullback₁ q : Y.OpenCover.{u}) p α ≫ U₀.pullbackHom q α)
    (M : X.Modules) :
    let U : Y.OpenCover.{u} := U₀.pullback₁ q
    let V : Z.OpenCover.{u} := U.pullback₁ p
    let W : Z.OpenCover.{u} := U₀.pullback₁ b
    let t₀ := openCoverTensorPullbackComparison b U₀ α
    let t₁ := openCoverTensorPullbackComparison q U₀ α
    let t₂ := openCoverTensorPullbackComparison p U α
    let c := tensorPullbackCompositionIso p q b wpq
    let l := pullbackComp s.hom (U₀.pullbackHom b α) ≪≫ pullbackCongr hk ≪≫
      (pullbackComp (U.pullbackHom p α) (U₀.pullbackHom q α)).symm
    let v := pullbackComp s.hom (W.f α) ≪≫ pullbackCongr hs
    (pullback s.hom).map (t₀.hom.app M) ≫ v.hom.app ((tensorPullback b).obj M) ≫
        (pullback (V.f α)).map (c.hom.app M) =
      l.hom.app ((pullback (U₀.f α)).obj M) ≫
        (pullback (U.pullbackHom p α)).map (t₁.hom.app M) ≫
          t₂.hom.app ((tensorPullback q).obj M) := by sorry

end AlgebraicGeometry.Scheme.Modules
