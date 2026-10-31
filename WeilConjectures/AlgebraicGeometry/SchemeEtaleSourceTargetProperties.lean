/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import WeilConjectures.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.SmoothEtaleLocalSource
import WeilConjectures.AlgebraicGeometry.EtaleDescentThroughSourceCover
import WeilConjectures.AlgebraicGeometry.Morphisms.LocallyOfFinitePresentationFppfSource
import WeilConjectures.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFlatLfpSource
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Étale source-and-target locality for five scheme properties

Source: Stacks Project, Descent, Tags 04QZ, 04R1 and 04R3
(blueprint: lem-sfb-scheme-etale-source-target-properties).

Smooth, étale, flat, locally finitely presented and locally finite type morphisms satisfy
étale source-and-target locality, its commutative-square consequences, and descent along
any jointly surjective set-indexed étale source family, including an empty family.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Pass from singleton descent to arbitrary families by factoring each étale map
through its open image. Zariski locality then glues these images, including an empty cover. -/
private theorem etale_source_family_iff (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderComposition] [IsZariskiLocalAtSource P] (hE : @Etale ≤ P)
    (hD : ∀ {U X Y : Scheme.{u}} (a : U ⟶ X) (f : X ⟶ Y),
      Etale a → Surjective a → P (a ≫ f) → P f)
    {X Y : Scheme.{u}} (f : X ⟶ Y) {I : Type v}
    (U : I → Scheme.{u}) (a : ∀ i : I, U i ⟶ X)
    (ha : ∀ i : I, Etale (a i))
    (hcover : ∀ x : X, ∃ (i : I) (u : U i), (a i).base u = x) :
    P f ↔ ∀ i : I, P (a i ≫ f) := by
  constructor
  · intro hf i
    exact P.comp_mem (a i) f (hE _ _ _ (ha i)) hf
  · intro hf
    let W : I → X.Opens := fun i ↦
      ⟨Set.range (a i), @Scheme.Hom.isOpenMap _ _ (a i)
        (by have := ha i; infer_instance) |>.isOpen_range⟩
    have hW : iSup W = ⊤ := by
      apply top_le_iff.mp
      intro x _
      obtain ⟨i, u, hu⟩ := hcover x
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, u, hu⟩
    apply IsZariskiLocalAtSource.of_iSup_eq_top (P := P) W hW
    intro i
    have : Etale (a i) := ha i
    let q : U i ⟶ (W i).toScheme :=
      IsOpenImmersion.lift (W i).ι (a i)
        (by rw [Scheme.Opens.range_ι]; exact Set.Subset.rfl)
    have hq : q ≫ (W i).ι = a i := IsOpenImmersion.lift_fac _ _ _
    have : Etale q := by
      have : Etale (q ≫ (W i).ι) := hq.symm ▸ ha i
      exact Etale.of_comp q (W i).ι
    have : Surjective q := by
      constructor
      intro z
      obtain ⟨u, hu⟩ := z.property
      refine ⟨u, ?_⟩
      apply (W i).ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hq]
      exact hu
    apply hD q ((W i).ι ≫ f) inferInstance inferInstance
    simpa only [← Category.assoc, hq] using hf i

/-- The graph of a map into an étale target is étale, so base change and
composition cancel that target from any of the properties considered here. -/
private theorem etale_target_cancel (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderComposition] [P.IsStableUnderBaseChange] (hE : @Etale ≤ P)
    {U V Y : Scheme.{u}} (h : U ⟶ V) (b : V ⟶ Y) [Etale b]
    (hf : P (h ≫ b)) : P h := by
  let s : U ⟶ pullback (h ≫ b) b := pullback.lift (𝟙 U) h (by simp)
  have : Etale s := by
    have : Etale (s ≫ pullback.fst (h ≫ b) b) := by
      dsimp [s]
      rw [pullback.lift_fst]
      infer_instance
    exact Etale.of_comp s (pullback.fst (h ≫ b) b)
  have hs : P (s ≫ pullback.snd (h ≫ b) b) :=
    P.comp_mem _ _ (hE _ _ s inferInstance) (P.pullback_snd _ _ hf)
  simpa only [s, pullback.lift_snd] using hs

/-- Each of the five listed scheme properties is étale local on source-and-target.
In a square with étale vertical arrows the property passes to the top horizontal map;
it descends to the bottom horizontal map if the source vertical map is surjective.
It is also detected by any jointly surjective étale source family.

Source: Stacks Project, Descent, Tags 04QZ (definition-local-source-target),
04R1 (lemma-local-source-target-characterize), and 04R3 (remark-list-local-source-target)
(blueprint: lem-sfb-scheme-etale-source-target-properties).

Proof:
1. Mathlib supplies composition, arbitrary base-change stability, Zariski source locality,
   and the implication from étale to each of the five properties.
2. Singleton étale source descent is the singleton case of the smooth and lfp family
   criteria, étale source descent, flat source descent, or flat-lfp source descent for lft.
3. Factor each member of an arbitrary étale family through its open image. The factor is
   surjective and étale, so step 2 gives the property on each open image. These images cover
   the source; Zariski locality glues them. This also treats empty and large-universe families.
4. The graph into the pullback along an étale target map is étale by cancellation with its
   étale projection. Base change followed by this graph proves target cancellation.
5. Composition, target cancellation, and singleton descent give both square implications.
6. Identity charts give the forward pointwise criterion. Conversely choose one chart over
   each source point, postcompose its good horizontal map with the étale target map, and
   apply step 3 to the resulting jointly surjective family of source charts.
-/
theorem scheme_etale_source_target_properties
    (P : MorphismProperty Scheme.{u})
    (hP : P = @Smooth ∨ P = @Etale ∨ P = @Flat ∨
      P = @LocallyOfFinitePresentation ∨ P = @LocallyOfFiniteType) :
    IsEtaleLocalOnSourceAndTarget P ∧
      (∀ (X Y U V : Scheme.{u}) (f : X ⟶ Y) (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V),
        Etale a → Etale b → a ≫ f = h ≫ b →
          (P f → P h) ∧ (Surjective a → P h → P f)) ∧
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (I : Type v)
        (U : I → Scheme.{u}) (a : ∀ i : I, U i ⟶ X),
        (∀ i : I, Etale (a i)) →
          (∀ x : X, ∃ (i : I) (u : U i), (a i).base u = x) →
            (P f ↔ ∀ i : I, P (a i ≫ f))) := by
  have : P.IsStableUnderComposition := by
    rcases hP with rfl | rfl | rfl | rfl | rfl <;> infer_instance
  have : P.IsStableUnderBaseChange := by
    rcases hP with rfl | rfl | rfl | rfl | rfl <;> infer_instance
  have : IsZariskiLocalAtSource P := by
    rcases hP with rfl | rfl | rfl | rfl | rfl <;> infer_instance
  have hE : @Etale ≤ P := by
    intro X Y f hf
    have : Etale f := hf
    rcases hP with rfl | rfl | rfl | rfl | rfl <;> infer_instance
  have hD {U X Y : Scheme.{u}} (a : U ⟶ X) (f : X ⟶ Y)
      (ha : Etale a) (hs : Surjective a) (hf : P (a ≫ f)) : P f := by
    have : Etale a := ha
    have : Surjective a := hs
    rcases hP with rfl | rfl | rfl | rfl | rfl
    · exact (smooth_iff_of_jointly_surjective_etale f (fun _ : Unit ↦ U)
        (fun _ ↦ a) (fun x ↦ by
          obtain ⟨u, hu⟩ := a.surjective x
          exact ⟨(), u, hu⟩)).mpr (fun _ ↦ hf)
    · have : Etale (a ≫ f) := hf
      exact Etale.of_comp_of_surjective_etale f a
    · have : Flat (a ≫ f) := hf
      exact Flat.of_comp_of_flat_of_surjective a f
    · exact (locallyOfFinitePresentation_iff_of_fppf_source_family f
        (fun _ : Unit ↦ U) (fun _ ↦ a) (fun x ↦ by
          obtain ⟨u, hu⟩ := a.surjective x
          exact ⟨(), u, hu⟩)).mpr (fun _ ↦ hf)
    · have : LocallyOfFiniteType (a ≫ f) := hf
      exact locallyOfFiniteType_of_flat_lfp_source a f
  have hpost {U V Y : Scheme.{u}} (h : U ⟶ V) (b : V ⟶ Y)
      (hb : Etale b) (hh : P h) : P (h ≫ b) :=
    P.comp_mem h b hh (hE _ _ b hb)
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro X Y Z a f ha hf
    exact P.comp_mem a f (hE _ _ a ha) hf
  · intro X Y V f b hf _
    exact P.pullback_snd f b hf
  · intro X Y f
    constructor
    · intro hf x
      exact ⟨X, Y, 𝟙 X, 𝟙 Y, f, x, inferInstance, inferInstance,
        rfl, by simp, hf⟩
    · intro hf
      choose U V a b h u ha hb hu hcomm hh using hf
      apply (etale_source_family_iff P hE hD f U a ha
        (fun x ↦ ⟨x, u x, hu x⟩)).mpr
      intro x
      rw [hcomm x]
      exact hpost (h x) (b x) (hb x) (hh x)
  · intro X Y U V f a b h ha hb hcomm
    have : Etale b := hb
    constructor
    · intro hf
      apply etale_target_cancel P hE h b
      rw [← hcomm]
      exact P.comp_mem a f (hE _ _ a ha) hf
    · intro hs hh
      apply hD a f ha hs
      rw [hcomm]
      exact hpost h b hb hh
  · intro X Y f I U a ha hcover
    exact etale_source_family_iff P hE hD f U a ha hcover

end AlgebraicGeometry
