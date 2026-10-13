/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.AlgebraicGeometry.LocalOverlapTransitions
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Sheaf.AlgebraicGeometry.FinitePresentationZeroMapDescent

/-! # Eventual vanishing on a fixed affine cover chart

Source: Stacks Project, Tag 01ZR (3).
(blueprint: lem-pc-fp-chart-map-zero-eventually). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A map on a base-changed affine chart, with finite type source and finitely
presented target, vanishes at some finite stage if it vanishes after pullback to the limit.
Source: Stacks Project, Tag 01ZR (3), applied to a single affine cover chart.
(blueprint: lem-pc-fp-chart-map-zero-eventually).

Proof: Write W for the chart at k and b : W → Spec(R_k) for its structural map.
The stage map X_k → X_j is affine, since it is a base change of a map between
spectra. Thus W, the inverse image of an affine chart of U, is affine, and b is
quasi-compact. Apply finitePresentation_zero_map_descent to b with both initial
indices equal to k. The pullback of b along the identity of Spec(R_k) is canonically
isomorphic to W; use this isomorphism to transport the two modules and the map.
The limit base change of W is canonically isomorphic to the chart pulled back
along overlapLimitMap: both are the iterated pullback of U.X a along the same
maps. The analogous comparison at every later stage identifies the base change
of the map with its pullback along overlapRefinementHom. These comparisons follow
by the pullback universal property (their two projections agree), and the induced
module comparisons follow from pullbackComp and pullbackCongr. The tensor pullback
used by moduleBaseChange and the native pullback are naturally isomorphic: both are
left adjoint to the same pushforward, so adjoint uniqueness supplies the comparison.
Naturality transports zero equations in both directions. Hence the given
limit-zero hypothesis is the hypothesis of zero-map descent, which gives l ≥ k.
No Noetherian, finite-cover,
finite-presentation-of-the-scheme or transition/coherence hypothesis is needed.
Zero modules and empty affine charts cause no exception to the argument. -/
theorem finitePresentation_chart_map_zero_eventually
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (j : I) (hij : i ≤ j)
    (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    [∀ a, IsAffine (U.X a)] (a : U.I₀) (k : I) (hjk : j ≤ k)
    (F G : ((U.pullback₁ (overlapStageMap R f hij hjk)).X a).Modules)
    (hF_ft : F.IsFiniteType) (hF_qc : F.IsQuasicoherent)
    (hG_fp : G.IsFinitePresentation) (hG_qc : G.IsQuasicoherent)
    (δ : F ⟶ G)
    (hδ : (Scheme.Modules.pullback
      (Scheme.Cover.pullbackHom (U.pullback₁ (overlapStageMap R f hij hjk))
        (overlapLimitMap R c f (hij.trans hjk)) a)).map δ = 0) :
    ∃ (l : I) (hkl : k ≤ l),
      (Scheme.Modules.pullback
        (overlapRefinementHom U (overlapStageMap R f hij hjk)
          (overlapStageMap R f hij (hjk.trans hkl))
          (overlapStageMap R f (hij.trans hjk) hkl)
          (overlapStageMap_comp R f hij hjk hkl) a)).map δ = 0 := by sorry

end AlgebraicGeometry
