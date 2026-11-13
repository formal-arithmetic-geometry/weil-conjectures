/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalBaseChangePoints
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Points of a zero-dimensional curve after base change

Base change of a zero-dimensional curve between algebraically closed fields is again a
zero-dimensional curve, with the same points, all of which are rational.

## References

* [Stacks Project, Tag 00KH](https://stacks.math.columbia.edu/tag/00KH)
* [Stacks Project, Tag 00FV](https://stacks.math.columbia.edu/tag/00FV)
* [Stacks Project, Tag 01JT](https://stacks.math.columbia.edu/tag/01JT)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The base change of a zero-dimensional curve over an algebraically closed field `k` to an
algebraically closed extension `k'` is a zero-dimensional curve whose points correspond
bijectively to those of `C`, each given by a `k'`-point. -/
theorem zeroDimensional_baseChange_geometric_points {k k' : Type u}
    [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] {C C' : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsCurve f] (hC : topologicalKrullDim C ≤ 0)
    {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f ι) :
    IsCurve f' ∧ topologicalKrullDim C' ≤ 0 ∧
      ∃ b : C' ≃ C, (∀ c', b c' = ι' c') ∧
        ∃ s : C' → (Spec (.of k') ⟶ C'), ∀ c', s c' default = c' := by
  classical
  let : C.Over (Spec (.of k)) := ⟨f⟩
  let φ : k →+* k' := (Spec.preimage ι).hom
  let : Algebra k k' := φ.toAlgebra
  have hi : Spec.map (CommRingCat.ofHom (algebraMap k k')) = ι := by
    exact Spec.map_preimage ι
  let : IsSeparated (C ↘ Spec (.of k)) := inferInstanceAs (IsSeparated f)
  let : LocallyOfFiniteType (C ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType f)
  let : QuasiCompact (C ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact f)
  obtain ⟨_, hdiscrete, _, _, hd, hp⟩ := zeroDimensional_baseChange_points k k' C hC
  rw [hi] at hd hp
  let e := h.isoPullback
  have he : e.hom ≫ CategoryTheory.Limits.pullback.fst f ι = ι' := h.isoPullback_hom_fst
  have hdim : topologicalKrullDim C' ≤ 0 := by
    rw [e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq]
    exact hd
  let : IsSeparated f' := MorphismProperty.of_isPullback h inferInstance
  let : LocallyOfFiniteType f' := MorphismProperty.of_isPullback h inferInstance
  let : QuasiCompact f' := MorphismProperty.of_isPullback h inferInstance
  refine ⟨⟨hdim.trans (by norm_num)⟩, hdim, ?_⟩
  let b := e.hom.homeomorph.toEquiv.trans (hp.homeomorph _).toEquiv
  refine ⟨b, ?_, ?_⟩
  · intro c'
    change (CategoryTheory.Limits.pullback.fst f ι) (e.hom c') = ι' c'
    exact congrArg (fun g : C' ⟶ C ↦ g c') he
  · let : DiscreteTopology C := hdiscrete
    let eb := e.hom.homeomorph.trans (hp.homeomorph _)
    let : DiscreteTopology C' := eb.isEmbedding.discreteTopology
    refine ⟨fun c' ↦ pointOfClosedPoint f' c' (isClosed_discrete _), ?_⟩
    intro c'
    exact pointOfClosedPoint_apply _ _ _ _

end AlgebraicGeometry
