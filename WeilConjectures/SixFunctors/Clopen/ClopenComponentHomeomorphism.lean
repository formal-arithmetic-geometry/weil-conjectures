/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.Homeomorph.Defs
import WeilConjectures.ProEtaleCoefficients.ConnectedComponentsProfinite
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Sets.Closeds
import WeilConjectures.SixFunctors.Supporting.ProfiniteClopenPullback

/-!
# Clopen inverse images and spectral connected-component spaces

## References

* [Stacks, Tag 0900]
* [Stacks, Tag 0906]
* [Stacks, Tag 005F]
* [Stacks, Tag 08ZZ]
* [Stacks, Tag 004T]
* [Stacks, Tag 0376]
* [Stacks, Tag 08ZL]
-/

@[expose] public section

universe u v w

namespace ConnectedComponents

/-- Clopen subsets descend bijectively through the connected-component quotient of an
arbitrary space. -/
private theorem clopen_descent_aux (Z : Type w) [TopologicalSpace Z] :
    Function.Bijective
      (fun V : TopologicalSpace.Clopens (ConnectedComponents Z) ↦
        (⟨mk ⁻¹' (V : Set (ConnectedComponents Z)),
          V.isClopen.preimage continuous_coe⟩ : TopologicalSpace.Clopens Z)) ∧
    ∀ U : TopologicalSpace.Clopens Z,
      IsClopen ((mk : Z → ConnectedComponents Z) '' (U : Set Z)) ∧
      (mk : Z → ConnectedComponents Z) ⁻¹'
        ((mk : Z → ConnectedComponents Z) '' (U : Set Z)) = (U : Set Z) := by
  have saturation (U : TopologicalSpace.Clopens Z) :
      (mk : Z → ConnectedComponents Z) ⁻¹'
        ((mk : Z → ConnectedComponents Z) '' (U : Set Z)) = (U : Set Z) := by
    rw [connectedComponents_preimage_image, U.isClopen.biUnion_connectedComponent_eq]
  have image_clopen (U : TopologicalSpace.Clopens Z) :
      IsClopen ((mk : Z → ConnectedComponents Z) '' (U : Set Z)) := by
    rw [← isQuotientMap_coe.isClopen_preimage, saturation]
    exact U.isClopen
  refine ⟨⟨?_, ?_⟩, fun U ↦ ⟨image_clopen U, saturation U⟩⟩
  · intro V W hVW
    apply TopologicalSpace.Clopens.ext
    exact Set.preimage_injective.mpr surjective_coe (congrArg SetLike.coe hVW)
  · intro U
    exact ⟨⟨mk '' (U : Set Z), image_clopen U⟩,
      TopologicalSpace.Clopens.ext (saturation U)⟩

/-- Clopens descend bijectively through the connected-component quotient, with inverse
given by set image. The uniquely normalized continuous component map makes this descent
natural, so bijectivity on clopens is equivalent before and after taking components.
The spaces may be empty and need not satisfy any separation or compactness condition. -/
theorem clopen_descent_naturality
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) :
    ∃ h : ContinuousMap (ConnectedComponents X) (ConnectedComponents Y),
      (h ∘ (mk : X → ConnectedComponents X) =
        (mk : Y → ConnectedComponents Y) ∘ f) ∧
      (∀ g : ContinuousMap (ConnectedComponents X) (ConnectedComponents Y),
        g ∘ (mk : X → ConnectedComponents X) =
          (mk : Y → ConnectedComponents Y) ∘ f → g = h) ∧
      (∀ x : X, h (mk x) = mk (f x)) ∧
      (∀ (Z : Type w) [TopologicalSpace Z],
        Function.Bijective
          (fun V : TopologicalSpace.Clopens (ConnectedComponents Z) ↦
            (⟨mk ⁻¹' (V : Set (ConnectedComponents Z)),
              V.isClopen.preimage continuous_coe⟩ : TopologicalSpace.Clopens Z)) ∧
        ∀ U : TopologicalSpace.Clopens Z,
          IsClopen ((mk : Z → ConnectedComponents Z) '' (U : Set Z)) ∧
          (mk : Z → ConnectedComponents Z) ⁻¹'
            ((mk : Z → ConnectedComponents Z) '' (U : Set Z)) = (U : Set Z)) ∧
      (∀ V : TopologicalSpace.Clopens (ConnectedComponents Y),
        (mk : X → ConnectedComponents X) ⁻¹' (h ⁻¹' (V : Set (ConnectedComponents Y))) =
          f ⁻¹' ((mk : Y → ConnectedComponents Y) ⁻¹' (V : Set (ConnectedComponents Y)))) ∧
      (Function.Bijective
        (fun U : TopologicalSpace.Clopens Y ↦
          (⟨f ⁻¹' (U : Set Y), U.isClopen.preimage hf⟩ : TopologicalSpace.Clopens X)) ↔
        Function.Bijective
          (fun V : TopologicalSpace.Clopens (ConnectedComponents Y) ↦
            (⟨h ⁻¹' (V : Set (ConnectedComponents Y)), V.isClopen.preimage h.continuous⟩ :
              TopologicalSpace.Clopens (ConnectedComponents X)))) := by
  let h : ContinuousMap (ConnectedComponents X) (ConnectedComponents Y) :=
    ⟨hf.connectedComponentsMap, hf.connectedComponentsMap_continuous⟩
  refine ⟨h, rfl, ?_, fun _ ↦ rfl, clopen_descent_aux, fun _ ↦ rfl, ?_⟩
  · intro g hg
    apply ContinuousMap.ext
    intro c
    obtain ⟨x, rfl⟩ := surjective_coe c
    exact congrFun hg x
  · let βX := fun V : TopologicalSpace.Clopens (ConnectedComponents X) ↦
      (⟨mk ⁻¹' (V : Set (ConnectedComponents X)),
        V.isClopen.preimage continuous_coe⟩ : TopologicalSpace.Clopens X)
    let βY := fun V : TopologicalSpace.Clopens (ConnectedComponents Y) ↦
      (⟨mk ⁻¹' (V : Set (ConnectedComponents Y)),
        V.isClopen.preimage continuous_coe⟩ : TopologicalSpace.Clopens Y)
    let F := fun U : TopologicalSpace.Clopens Y ↦
      (⟨f ⁻¹' (U : Set Y), U.isClopen.preimage hf⟩ : TopologicalSpace.Clopens X)
    let H := fun V : TopologicalSpace.Clopens (ConnectedComponents Y) ↦
      (⟨h ⁻¹' (V : Set (ConnectedComponents Y)),
        V.isClopen.preimage h.continuous⟩ :
          TopologicalSpace.Clopens (ConnectedComponents X))
    have hβX : Function.Bijective βX := (clopen_descent_aux X).1
    have hβY : Function.Bijective βY := (clopen_descent_aux Y).1
    have square : F ∘ βY = βX ∘ H := rfl
    change Function.Bijective F ↔ Function.Bijective H
    rw [← Function.Bijective.of_comp_iff F hβY, square]
    exact hβX.of_comp_iff' H

end ConnectedComponents

/-- A continuous map of spectral spaces whose inverse-image map on clopens is bijective
induces a homeomorphism of connected-component quotients, normalized by the quotient maps.
No nonemptiness assumption is imposed. -/
theorem isHomeomorph_connectedComponentsMap_of_bijective_clopen_preimage
    {T : Type u} {S : Type v} [TopologicalSpace T] [TopologicalSpace S]
    [SpectralSpace T] [SpectralSpace S] {f : T → S} (hf : Continuous f)
    (hclop : Function.Bijective
      (fun U : TopologicalSpace.Clopens S ↦
        (⟨f ⁻¹' (U : Set S), U.isClopen.preimage hf⟩ : TopologicalSpace.Clopens T))) :
    IsHomeomorph hf.connectedComponentsMap ∧
      hf.connectedComponentsMap ∘ (ConnectedComponents.mk : T → ConnectedComponents T) =
        (ConnectedComponents.mk : S → ConnectedComponents S) ∘ f := by
  obtain ⟨h, hnorm, _, _, _, _, hclop_iff⟩ :=
    ConnectedComponents.clopen_descent_naturality.{u, v, u} f hf
  obtain ⟨hTcompact, hThausdorff, hTdisconnected⟩ :=
    spectralSpace_connectedComponents_profinite (T := T)
  obtain ⟨hScompact, hShausdorff, hSdisconnected⟩ :=
    spectralSpace_connectedComponents_profinite (T := S)
  have : CompactSpace (ConnectedComponents T) := hTcompact
  have : T2Space (ConnectedComponents T) := hThausdorff
  have : TotallyDisconnectedSpace (ConnectedComponents T) := hTdisconnected
  have : CompactSpace (ConnectedComponents S) := hScompact
  have : T2Space (ConnectedComponents S) := hShausdorff
  have : TotallyDisconnectedSpace (ConnectedComponents S) := hSdisconnected
  obtain ⟨hinj, hsurj, _, hopen⟩ :=
    bijective_and_isOpenMap_of_bijective_clopen_preimage h.continuous (hclop_iff.mp hclop)
  have heq : (h : ConnectedComponents T → ConnectedComponents S) =
      hf.connectedComponentsMap := by
    apply ConnectedComponents.surjective_coe.injective_comp_right
    exact hnorm
  rw [← heq]
  exact ⟨⟨h.continuous, hopen, hinj, hsurj⟩, hnorm⟩
