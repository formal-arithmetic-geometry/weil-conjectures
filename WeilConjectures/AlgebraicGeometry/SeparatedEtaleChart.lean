/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# Separated étale charts of algebraic spaces

Source: Stacks Project, `spaces-properties.tex`, Tag 03FZ and
`morphisms.tex`, Tag 01QR (blueprint: lem-a1-separated-etale-chart).

The representable diagonal is expressed by the closed-immersion property
of every scheme test; the second clause records a scheme representing each
scheme fibre product and the separatedness of its projection.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A separated scheme étale chart into an algebraic space has separated
representable diagonal, and all its scheme fibre products over the space are
separated.

Source: Stacks Project, `spaces-properties.tex`, Tag 03FZ (lemma-separated-cover),
and `morphisms.tex`, Tag 01QR (base change of closed immersions); the scheme
cancellation input is `schemes.tex`, Tag 01KV.
(blueprint: lem-a1-separated-etale-chart)

Proof: absolute separatedness of `U` and separated cancellation give a closed
immersion for the diagonal of `U` over `S`.  The diagonal of the chart is its
base change along the represented relation `U ×_E U`, so closed-immersion base
change gives the first clause, including all scheme tests.  For a scheme `C`
with a map to `E`, represent `C ×_E U` by a scheme `W`; the same cartesian
diagonal argument identifies its diagonal over `C` as a base change of the
chart diagonal, proving the second clause.
-/
theorem separated_etale_chart
    {S : Scheme.{u}} (E : AlgebraicSpace S) (U : Over S)
    [Scheme.IsSeparated U.left]
    (u : yoneda.obj U ⟶ E.obj.obj) (hu : IsEtale u) :
    AlgebraicSpace.IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (CategoryTheory.Limits.pullback.lift (𝟙 (yoneda.obj U)) (𝟙 (yoneda.obj U))
        (by simp) : yoneda.obj U ⟶ CategoryTheory.Limits.pullback u u) ∧
      ∀ (C : Over S) (c : yoneda.obj C ⟶ E.obj.obj),
        ∃ (W : Over S) (p : W ⟶ C) (q : yoneda.obj W ⟶ yoneda.obj U),
          IsPullback q (yoneda.map p) u c ∧ IsSeparated p.left := by
  classical
  constructor
  · intro T a
    let f : T ⟶ U := yoneda.preimage (a ≫ pullback.fst u u)
    let g : T ⟶ U := yoneda.preimage (a ≫ pullback.snd u u)
    let V := equalizer f g
    let p : V ⟶ T := equalizer.ι f g
    let q : yoneda.obj V ⟶ yoneda.obj U := yoneda.map (p ≫ f)
    have hfg : p ≫ f = p ≫ g := equalizer.condition f g
    refine ⟨V, p, q, ?_, inferInstance⟩
    have hw : q ≫ pullback.lift (𝟙 _) (𝟙 _) (by simp) = yoneda.map p ≫ a := by
      apply pullback.hom_ext
      · simp [q, f]
      · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
        change yoneda.map (p ≫ f) = yoneda.map p ≫ a ≫ pullback.snd u u
        rw [hfg, Functor.map_comp]
        simp [g]
    let hV := isLimitOfHasEqualizerOfPreservesLimit yoneda f g
    apply IsPullback.of_isLimit (c := PullbackCone.mk q (yoneda.map p) hw)
    refine PullbackCone.IsLimit.mk _ (fun s ↦ Fork.IsLimit.lift hV s.snd ?_) ?_ ?_ ?_
    · have h₁ := congrArg (fun k ↦ k ≫ pullback.fst u u) s.condition
      have h₂ := congrArg (fun k ↦ k ≫ pullback.snd u u) s.condition
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        Category.comp_id] at h₁ h₂
      simpa [f, g] using h₁.symm.trans h₂
    · intro s
      dsimp [q]
      rw [Functor.map_comp, ← Category.assoc]
      rw [show Fork.IsLimit.lift hV s.snd _ ≫ yoneda.map p = s.snd from
        Fork.IsLimit.lift_ι' hV _ _]
      have h := congrArg (fun k ↦ k ≫ pullback.fst u u) s.condition
      simpa [f] using h.symm
    · intro s
      exact Fork.IsLimit.lift_ι' hV _ _
    · intro s m _ h₂
      apply Fork.IsLimit.hom_ext hV
      exact h₂.trans (Fork.IsLimit.lift_ι' hV _ _).symm
  · intro C c
    obtain ⟨W, p, q, hW, _⟩ := hu C c
    refine ⟨W, p, q, hW, ?_⟩
    let r : W ⟶ U := yoneda.preimage q
    let i : W ⟶ C ⨯ U := prod.lift p r
    have hi : Mono i := ⟨fun {Z} a b hab ↦ by
      apply yoneda.map_injective
      apply hW.hom_ext
      · have h := congrArg (fun k ↦ k ≫ prod.snd) hab
        simpa [i, r, Functor.map_comp] using congrArg yoneda.map h
      · have h := congrArg (fun k ↦ k ≫ prod.fst) hab
        simpa [i, Functor.map_comp] using congrArg yoneda.map h⟩
    have hprod : IsSeparated (prod.fst : C ⨯ U ⟶ C).left := by
      apply MorphismProperty.of_isPullback
        (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd C U)).flip
      exact inferInstanceAs (IsSeparated (show U.left ⟶ S from U.hom))
    have : IsSeparated (i.left ≫ (prod.fst : C ⨯ U ⟶ C).left) := inferInstance
    have hip : i.left ≫ (prod.fst : C ⨯ U ⟶ C).left = p.left :=
      congrArg (fun k : W ⟶ C ↦ k.left) (prod.lift_fst p r)
    rwa [hip] at this

end AlgebraicGeometry.AlgebraicSpace
