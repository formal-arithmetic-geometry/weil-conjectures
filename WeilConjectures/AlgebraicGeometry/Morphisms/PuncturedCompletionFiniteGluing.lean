/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.AdicCompletion.Algebra
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingPuncturedIso
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingCompletedIso
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Finite algebra gluing across maximal-ideal completion

Source: Stacks Project, Tag 0BLH.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A finite completed model glues to a finite model with both prescribed restrictions.

Source: Stacks Project, Tag 0BLH and More on Algebra, Proposition 15.91.16.
(blueprint: lem-sbc-punctured-completion-finite-gluing)

Proof: Form the actual ring of matching sections Γ(Y) ×_{Γ(P)} Γ(E), where
P is the overlap and the map to E is induced by the supplied identification.
The A-algebra map is the pullback lift of the two structural maps on sections.
Its spectrum is the candidate F. The punctured and completed comparison theorems
identify its two restrictions with the supplied models. The natural base equations
and the inverse-hom identity give the equations required below. The completed
pullback projection is finite because it is isomorphic over the completed base
to s. Noetherian maximal-ideal completion is flat and local, hence faithfully flat;
finite morphisms descend under this fpqc base change. This proves finiteness of F
without an additional hole. For empty U the matching ring is Γ(E), so the same
construction also includes Artinian local bases. -/
theorem exists_finite_model_of_completed_model
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (U : (Spec (.of A)).Opens)
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} (q : Y ⟶ U.toScheme) [IsFinite q]
    (E : Scheme.{u}) (s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))) [IsFinite s]
    (hext :
      let c := Spec.map (CommRingCat.ofHom
        (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))
      let W := c ⁻¹ᵁ U
      ∃ e : pullback q (c ∣_ U) ≅ (s ⁻¹ᵁ W).toScheme,
        e.hom ≫ s ∣_ W = pullback.snd q (c ∣_ U)) :
    ∃ (F : Scheme.{u}) (r : F ⟶ Spec (.of A)), IsFinite r ∧
      (∃ e : Y ≅ (r ⁻¹ᵁ U).toScheme, e.hom ≫ r ∣_ U = q) ∧
      ∃ e : pullback r (Spec.map (CommRingCat.ofHom
          (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))) ≅ E,
        e.hom ≫ s = pullback.snd r (Spec.map (CommRingCat.ofHom
          (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))) := by
  obtain ⟨e, he⟩ := hext
  let D : CompletionGluingData A U q E s := ⟨e, he⟩
  have : IsIso D.puncturedMap := D.puncturedMap_isIso hU
  have : IsIso D.completedMap := D.completedMap_isIso hU
  have hcompleted : (asIso D.completedMap).inv ≫ s =
      pullback.snd D.modelMap (completionSpecMap A) := by
    calc
      (asIso D.completedMap).inv ≫ s = (asIso D.completedMap).inv ≫
          (D.completedMap ≫ pullback.snd D.modelMap (completionSpecMap A)) :=
        congrArg (fun f => (asIso D.completedMap).inv ≫ f) D.completedMap_over.symm
      _ = _ := (asIso D.completedMap).inv_hom_id_assoc _
  have : IsFinite (pullback.snd D.modelMap (completionSpecMap A)) := by
    rw [← hcompleted]
    infer_instance
  have : Module.FaithfullyFlat A (AdicCompletion (IsLocalRing.maximalIdeal A) A) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hcover : Flat (completionSpecMap A) ∧ Surjective (completionSpecMap A) :=
    (flat_and_surjective_SpecMap_iff _).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have : QuasiCompact (completionSpecMap A) := inferInstance
  have := IsFinite.descendsAlong_surjective_inf_flat_inf_quasicompact
  have hfinite : IsFinite D.modelMap :=
    MorphismProperty.of_pullback_snd_of_descendsAlong
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ⟨⟨hcover.2, hcover.1⟩, inferInstance⟩ inferInstance
  refine ⟨D.model, D.modelMap, hfinite, ?_, ?_⟩
  · exact ⟨asIso D.puncturedMap, D.puncturedMap_over⟩
  · exact ⟨(asIso D.completedMap).symm, hcompleted⟩

end AlgebraicGeometry.Scheme
