/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Sheaf.AlgebraicGeometry.LocalOverlapTransitions
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback
public import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.FinitePresentationZeroMapDescent

/-! # Persistent eventual diagonal overlap equation

Source: Stacks Project, Tags 01ZR and 05N7.
(blueprint: lem-pc-fp-overlap-diagonal-eventually). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The identity defect of a single cover chart vanishes eventually, and remains
zero at every later stage.
Source: Stacks Project, Tag 01ZR (3), finite-type zero-map descent.
(blueprint: lem-pc-fp-overlap-diagonal-eventually).

Proof: On the chart at k subtract the identity from its self transition. Its source
and target are pullbacks of the prescribed finitely presented quasi-coherent module,
up to the supplied component isomorphism. The source is therefore of finite type.
The chart is quasi-compact over Spec(R_k), as an affine chart base changed along
an affine map. The identity-base-change comparison identifies this defect with a
map to which finitePresentation_zero_map_descent applies. Naturality of transitions,
the pullback composition comparisons, and limit coherence show that its limit
pullback is zero. Zero-map descent gives l. At any m above l the defect is still
zero since pullback is additive. The canonical chart refinement maps compose,
by the pullback universal property, and pseudofunctor associativity identifies
this pullback defect with the self transition of the prescribed T' minus identity.
Thus the displayed equation holds. This also handles zero modules and empty charts;
the theorem is only invoked for an actual cover index. -/
theorem finitePresentation_overlap_diagonal_eventually
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (j : I) (hij : i ≤ j)
    (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    [Finite U.I₀] [∀ a, IsAffine (U.X a)]
    (N : (a : U.I₀) → (U.X a).Modules)
    (a : U.I₀)
    (hN : ∀ a, (N a).IsFinitePresentation) (hNq : ∀ a, (N a).IsQuasicoherent)
    :
    ∀ (k : I) (hjk : j ≤ k),
      let q₀ := overlapStageMap R f hij hjk
      let V₀ : (pullback f (Spec.map (R.map (homOfLE (hij.trans hjk))))).OpenCover.{u} :=
        U.pullback₁ q₀
      let p₀ := overlapLimitMap R c f (hij.trans hjk)
      ∀ T : modulesPseudofunctor.OverlapTransitions V₀.f,
        (∀ a, Nonempty ((T.obj a : (V₀.X a).Modules) ≅
          (Scheme.Modules.pullback (U.pullbackHom q₀ a)).obj (N a))) →
        (T.pull (p := p₀) (α := fun a ↦ a)
          (fun a ↦ V₀.pullbackHom_map p₀ a)).Coherent →
        ∃ (l : I) (hkl : k ≤ l), ∀ (m : I) (hkm : k ≤ m), l ≤ m →
          let q := overlapStageMap R f hij (hjk.trans hkm)
          let V : (pullback f (Spec.map
              (R.map (homOfLE (hij.trans (hjk.trans hkm)))))).OpenCover.{u} :=
            U.pullback₁ q
          let r := overlapStageMap R f (hij.trans hjk) hkm
          let s := overlapRefinementHom U q₀ q r
            (overlapStageMap_comp R f hij hjk hkm)
          let T' := T.pull (p := r) (α := fun a ↦ a) (p' := s)
            (fun a ↦ overlapRefinementHom_map U q₀ q r
              (overlapStageMap_comp R f hij hjk hkm) a)
          T'.hom (V.f a) (𝟙 _) (𝟙 _) (Category.id_comp _) (Category.id_comp _) = 𝟙 _ := by sorry

end AlgebraicGeometry
