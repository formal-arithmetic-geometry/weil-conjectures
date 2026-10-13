/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.AlgebraicGeometry.OpenCoverRefinementComparisons

/-! # Coherence of tensor pullback comparisons on refined charts

Source: Stacks Project, Tags 0095 and 0096, functoriality of module pullback.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The restriction/composition comparison is compatible with a chart refinement.
Source: Stacks Project, Tags 0095 and 0096; the canonical-comparison step in
lem-pc-open-cover-map-lift-transport.
(blueprint: lem-pc-open-cover-tensor-comparison-coherence).

Proof: For every scheme map b, let c_b be the unique comparison from its
fixed tensor left adjoint to its ordinary pullback left adjoint. Transposing
under the fixed adjunctions shows that tensorPullbackCompositionIso(g,b,t,w)
is the composite of c_t, congruence from t to g ≫ b, inverse ordinary pullback
composition, and the inverses of c_b and c_g on the two functor factors:
both transposes are pushforwardComp(g,b) followed by pushforwardCongr(w).
Injectivity of the adjunction conjugation gives this formula. The chart
comparison is, by its definition, ordinary composition/congruence followed by
the inverse of c_b on the base-map factor.
Substitute these formulas in alpha, ck and cl from the comparison bundle.
Functoriality moves each c_b through whiskering, and the adjacent c_b and
c_b inverse factors cancel. The remaining assertion involves only ordinary
pullback composition and pullback congruence. Its two paths are the reassociated
pullbacks of the same map from Vl(a) to U(a): hz identifies the route through
d and the chart map of Vk, hd identifies the route from Ul to U(a), and hz0
identifies the maps to W. Apply Scheme.Modules.pseudofunctor_associativity to
these reassociations; congruence along the stated scheme equalities identifies
the composites, independently of their equality proof witnesses. Restore the
cancelled comparisons and evaluate at M. This proves precisely the displayed
identity, including identity refinements, empty charts and zero modules. -/
theorem openCover_tensor_comparison_coherence
    {X Y Z W : Scheme.{u}} (q : Y ⟶ X) (v : Z ⟶ X) (h : W ⟶ X)
    (pk : W ⟶ Y) (pl : W ⟶ Z) (wk : pk ≫ q = h) (wl : pl ≫ v = h)
    (U : X.OpenCover.{u}) (a : U.I₀)
    (d : (U.pullback₁ v).X a ⟶ (U.pullback₁ q).X a)
    (hd : d ≫ U.pullbackHom q a = U.pullbackHom v a)
    (z : ((U.pullback₁ v).pullback₁ pl).X a ⟶
      ((U.pullback₁ q).pullback₁ pk).X a)
    (hz : z ≫ Scheme.Cover.pullbackHom (U.pullback₁ q) pk a =
      Scheme.Cover.pullbackHom (U.pullback₁ v) pl a ≫ d)
    (hz0 : z ≫ ((U.pullback₁ q).pullback₁ pk).f a =
      ((U.pullback₁ v).pullback₁ pl).f a)
    (M : X.Modules) :
    let Uk : Y.OpenCover.{u} := U.pullback₁ q
    let Ul : Z.OpenCover.{u} := U.pullback₁ v
    let Vk : W.OpenCover.{u} := Uk.pullback₁ pk
    let Vl : W.OpenCover.{u} := Ul.pullback₁ pl
    let D := pullback d
    let Pk := pullback (Uk.pullbackHom pk a)
    let Pl := pullback (Ul.pullbackHom pl a)
    let Zf := pullback z
    let Rk := pullback (Vk.f a)
    let Rl := pullback (Vl.f a)
    let Lk := tensorPullback q ⋙ pullback (Uk.f a)
    let Ll := tensorPullback v ⋙ pullback (Ul.f a)
    let comparisons := openCoverRefinementComparisons q v h pk pl wk wl U a d hd z hz hz0
    let alpha := comparisons.1
    let beta := comparisons.2.1
    let delta := comparisons.2.2.1
    let ck := moduleRecoveryComparisonIso (tensorPullback h) (tensorPullback q)
      (tensorPullback pk) (pullback (Uk.f a)) Pk Rk
      (tensorPullbackCompositionIso pk q h wk) (openCoverTensorPullbackComparison pk Uk a)
    let cl := moduleRecoveryComparisonIso (tensorPullback h) (tensorPullback v)
      (tensorPullback pl) (pullback (Ul.f a)) Pl Rl
      (tensorPullbackCompositionIso pl v h wl) (openCoverTensorPullbackComparison pl Ul a)
    Zf.map (ck.hom.app M) ≫ delta.hom.app (Lk.obj M) ≫
      Pl.map (alpha.inv.app M) = beta.hom.app ((tensorPullback h).obj M) ≫
        cl.hom.app M := by sorry

end AlgebraicGeometry.Scheme.Modules
