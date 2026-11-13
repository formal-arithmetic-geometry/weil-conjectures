/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Morphisms as clopen graphs of degree one
-/

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- Morphisms to a finite étale scheme correspond to clopen graphs of degree one
(Stacks, Tags 024T and 01KT). -/
theorem Scheme.finiteEtale_graph_clopen
    {Y U V : Scheme.{u}} (p : U ⟶ Y) (q : V ⟶ Y) [IsFinite q] [Etale q] :
    ∃ e : {a : U ⟶ V // a ≫ q = p} ≃
      {W : (pullback q p).Opens //
        IsClosed W.carrier ∧ IsIso (W.ι ≫ pullback.snd q p)},
      ∀ a, (e a).1.carrier =
        Set.range (pullback.lift (f := q) (g := p) a.1 (𝟙 U) (by simpa using a.2)).base  := by
  classical
  let graph (a : {a : U ⟶ V // a ≫ q = p}) : U ⟶ pullback q p :=
    pullback.lift a.1 (𝟙 U) (by simpa using a.2)
  have hsec (a) : graph a ≫ pullback.snd q p = 𝟙 U := by simp [graph]
  have hopen (a) : IsOpenImmersion (graph a) := by
    have : Mono (graph a) := mono_of_mono_fac (hsec a)
    have : Etale (graph a ≫ pullback.snd q p) := by rw [hsec]; infer_instance
    have : Etale (graph a) := Etale.of_comp _ (pullback.snd q p)
    exact IsOpenImmersion.of_flat_of_mono _
  have hclosed (a) : IsClosedImmersion (graph a) := by
    have : IsClosedImmersion (graph a ≫ pullback.snd q p) := by
      rw [hsec]; infer_instance
    exact IsClosedImmersion.of_comp _ (pullback.snd q p)
  let toClopen (a : {a : U ⟶ V // a ≫ q = p}) :
      {W : (pullback q p).Opens //
        IsClosed W.carrier ∧ IsIso (W.ι ≫ pullback.snd q p)} := by
    have := hopen a
    have := hclosed a
    refine ⟨(graph a).opensRange, (graph a).isClosedEmbedding.isClosed_range, ?_⟩
    have heq : (graph a).opensRange.ι ≫ pullback.snd q p = (graph a).isoOpensRange.inv := by
      rw [← (graph a).isoOpensRange_inv_comp, Category.assoc, hsec, Category.comp_id]
    rw [heq]
    infer_instance
  have hrange (a) : (toClopen a).1.carrier = Set.range (graph a).base := rfl
  have hinj : Function.Injective toClopen := by
    intro a b hab
    have := hopen a
    have := hopen b
    have hr : Set.range (graph a).base = Set.range (graph b).base :=
      congrArg (fun W ↦ W.1.carrier) hab
    let e := IsOpenImmersion.isoOfRangeEq (graph a) (graph b) hr
    have hfac : e.hom ≫ graph b = graph a :=
      IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    have hid : e.hom = 𝟙 U := by
      calc
        e.hom = e.hom ≫ graph b ≫ pullback.snd q p := by rw [hsec]; simp
        _ = graph a ≫ pullback.snd q p := by rw [← Category.assoc, hfac]
        _ = 𝟙 U := hsec a
    have hg : graph a = graph b := by rw [← hfac, hid]; simp
    apply Subtype.ext
    simpa [graph] using congrArg (fun s ↦ s ≫ pullback.fst q p) hg
  have hsurj : Function.Surjective toClopen := by
    intro W
    have := W.2.2
    let t := W.1.ι ≫ pullback.snd q p
    let s := inv t ≫ W.1.ι
    have hs : s ≫ pullback.snd q p = 𝟙 U := by simp [s, t]
    let a : {a : U ⟶ V // a ≫ q = p} :=
      ⟨s ≫ pullback.fst q p, by
        rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]⟩
    have hg : graph a = s := by
      apply pullback.hom_ext
      · simp [graph, a]
      · simpa [graph] using hs.symm
    refine ⟨a, ?_⟩
    apply Subtype.ext
    apply TopologicalSpace.Opens.ext
    change (toClopen a).1.carrier = W.1.carrier
    rw [hrange, hg]
    have hr : Set.range (inv t).base = Set.univ :=
      Set.range_eq_univ.mpr (inv t).surjective
    simp only [s, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hr,
      Set.image_univ]
    exact Subtype.range_coe
  exact ⟨Equiv.ofBijective toClopen ⟨hinj, hsurj⟩, hrange⟩

end AlgebraicGeometry
