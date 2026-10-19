/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject

/-! # Canonical truncation comparisons for t-exact functors

Source: BBD, Proposition 1.3.3(i),(ii), pp. 29–30, and §1.3.16, p. 36; the scalar-extension
and automorphism sentences in the proof of `prop-constructible-truncations` in the blueprint,
chapter `sec-poincare-duality`, unit `sk-lem-finite`
(blueprint: lem-pod-texact-truncation-comparison).

The comparison isomorphisms are the existing `Functor.eTruncLTIso` at `m + 1` and
`Functor.eTruncGEIso` at `m`. Their integer specializations are comparisons for `τ≤m` and
`τ≥m`. The identity and composite clauses quantify over comparisons characterized by the
canonical maps, so they do not require a new choice of t-exactness structures on functors.
-/

@[expose] public section

universe uC vC uD vD uB vB

namespace CategoryTheory.Triangulated.TStructure

open Limits

private lemma cancel_truncGE_unit
    {A : Type*} [Category* A] [Preadditive A] [HasZeroObject A] [HasShift A ℤ]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [Pretriangulated A]
    (t : TStructure A) (n : ℤ) {X Y Z : A} [t.IsGE Z n]
    (e : Y ≅ (t.truncGE n).obj X) (u : X ⟶ Y)
    (hu : u ≫ e.hom = (t.truncGEπ n).app X) (f g : Y ⟶ Z)
    (h : u ≫ f = u ≫ g) : f = g := by
  apply (cancel_epi e.inv).1
  apply t.from_truncGE_obj_ext
  have he : (t.truncGEπ n).app X ≫ e.inv = u := by
    rw [← hu, Category.assoc, e.hom_inv_id, Category.comp_id]
  simpa only [← Category.assoc, he] using h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Canonical comparisons for a t-exact triangulated functor are uniquely characterized by
the truncation counit and unit, commute with every natural transformation, and respect
identity functors and composition. Source: BBD, Proposition 1.3.3(i),(ii), pp. 29–30,
§1.3.16, p. 36; blueprint `prop-constructible-truncations`, scalar-extension and automorphism
sentences (blueprint: lem-pod-texact-truncation-comparison).

Here `truncLT (m + 1)` is `τ≤m` and `truncGE m` is `τ≥m`. The existing upstream
isomorphisms supply existence. Uniqueness is asserted separately for each sign. In the
identity and composition clauses, the quantified isomorphisms are required to satisfy
exactly the defining counit/unit equations; thus these clauses describe the same uniquely
characterized comparisons, independently of any t-exactness instance used to construct them.

Proof, as recorded in the nine steps of the DAG node:
1. Mathlib's `to_truncLT_obj_ext` and `from_truncGE_obj_ext` express the injectivity
   of composition with the counit and unit. The proved helper `cancel_truncGE_unit`
   transports the latter along an isomorphism characterized by the unit equation.
2. The existing `eTruncLTIso` and its counit equation give the upper comparison.
   Its source lies in the upper aisle by t-exactness, so counit cancellation gives
   uniqueness componentwise, hence uniqueness of the natural isomorphism.
3. The existing `eTruncGEIso` and its unit equation give the lower comparison.
   The helper from step 1 gives uniqueness of its components and natural isomorphism.
4. Upper object naturality is already part of `eTruncLTIso`.
5. Lower object naturality and the natural inverses are already part of `eTruncGEIso`.
6. For any η : F → G, postcompose the upper compatibility square with the counit.
   The characterization equations and naturality of η and the counit give equality;
   cancel using step 1. No compatibility of η with the shifts is used.
7. Precompose the lower square with F of the unit. Naturality of η and of the unit
   and both characterization equations give equality; cancel using step 1.
8. For the identity functor the identity maps satisfy the characterizations, so the
   two Mathlib extensionality lemmas give the identity comparisons directly.
9. For H after F, the upper source bound follows by t-exactness of F and then H.
   Apply counit cancellation and the two counit equations, using H.map_comp.
   For the lower sign, transport unit cancellation along the given βGE and apply
   H to F's unit equation, followed by H's unit equation. -/
theorem texact_truncation_comparison
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
    (tC : TStructure C) (tD : TStructure D)
    (_hC : tC.bounded = ⊤) (_hD : tD.bounded = ⊤)
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact tC tD] (m : ℤ) :
    (∀ K : C,
      (F.eTruncLTIso tC tD (m + 1 : ℤ)).hom.app K ≫
          (tD.truncLTι (m + 1)).app (F.obj K) = F.map ((tC.truncLTι (m + 1)).app K) ∧
      F.map ((tC.truncGEπ m).app K) ≫ (F.eTruncGEIso tC tD m).hom.app K =
          (tD.truncGEπ m).app (F.obj K)) ∧
    (∀ β : tC.truncLT (m + 1) ⋙ F ≅ F ⋙ tD.truncLT (m + 1),
      (∀ K : C, β.hom.app K ≫ (tD.truncLTι (m + 1)).app (F.obj K) =
        F.map ((tC.truncLTι (m + 1)).app K)) →
      β = F.eTruncLTIso tC tD (m + 1 : ℤ)) ∧
    (∀ β : tC.truncGE m ⋙ F ≅ F ⋙ tD.truncGE m,
      (∀ K : C, F.map ((tC.truncGEπ m).app K) ≫ β.hom.app K =
        (tD.truncGEπ m).app (F.obj K)) → β = F.eTruncGEIso tC tD m) ∧
    (∀ (G : C ⥤ D) [G.CommShift ℤ] [G.IsTriangulated] [G.IsTExact tC tD]
      (η : F ⟶ G) (K : C),
      η.app ((tC.truncLT (m + 1)).obj K) ≫
          (G.eTruncLTIso tC tD (m + 1 : ℤ)).hom.app K =
        (F.eTruncLTIso tC tD (m + 1 : ℤ)).hom.app K ≫
          (tD.truncLT (m + 1)).map (η.app K) ∧
      η.app ((tC.truncGE m).obj K) ≫ (G.eTruncGEIso tC tD m).hom.app K =
        (F.eTruncGEIso tC tD m).hom.app K ≫ (tD.truncGE m).map (η.app K)) ∧
    (∀ (βLE : tC.truncLT (m + 1) ⋙ 𝟭 C ≅ 𝟭 C ⋙ tC.truncLT (m + 1))
      (βGE : tC.truncGE m ⋙ 𝟭 C ≅ 𝟭 C ⋙ tC.truncGE m),
      (∀ K : C, βLE.hom.app K ≫ (tC.truncLTι (m + 1)).app K =
        (tC.truncLTι (m + 1)).app K) →
      (∀ K : C, (tC.truncGEπ m).app K ≫ βGE.hom.app K =
        (tC.truncGEπ m).app K) →
      ∀ K : C, βLE.hom.app K = 𝟙 _ ∧ βGE.hom.app K = 𝟙 _) ∧
    (∀ (B : Type uB) [Category.{vB} B] [Preadditive B] [HasZeroObject B] [HasShift B ℤ]
      [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B] [IsTriangulated B]
      (tB : TStructure B) (_hB : tB.bounded = ⊤)
      (H : D ⥤ B) [H.CommShift ℤ] [H.IsTriangulated] [H.IsTExact tD tB]
      (βLE : tC.truncLT (m + 1) ⋙ (F ⋙ H) ≅ (F ⋙ H) ⋙ tB.truncLT (m + 1))
      (βGE : tC.truncGE m ⋙ (F ⋙ H) ≅ (F ⋙ H) ⋙ tB.truncGE m),
      (∀ K : C, βLE.hom.app K ≫ (tB.truncLTι (m + 1)).app (H.obj (F.obj K)) =
        H.map (F.map ((tC.truncLTι (m + 1)).app K))) →
      (∀ K : C, H.map (F.map ((tC.truncGEπ m).app K)) ≫ βGE.hom.app K =
        (tB.truncGEπ m).app (H.obj (F.obj K))) →
      ∀ K : C,
        βLE.hom.app K = H.map ((F.eTruncLTIso tC tD (m + 1 : ℤ)).hom.app K) ≫
          (H.eTruncLTIso tD tB (m + 1 : ℤ)).hom.app (F.obj K) ∧
        βGE.hom.app K = H.map ((F.eTruncGEIso tC tD m).hom.app K) ≫
          (H.eTruncGEIso tD tB m).hom.app (F.obj K)) := by
  have hLE (K : C) :
      (F.eTruncLTIso tC tD (m + 1 : ℤ)).hom.app K ≫
        (tD.truncLTι (m + 1)).app (F.obj K) =
      F.map ((tC.truncLTι (m + 1)).app K) :=
    F.eTruncLTIsoApp_hom_eTruncLTι_app tC tD (m + 1 : ℤ) K
  have hGE (K : C) :
      F.map ((tC.truncGEπ m).app K) ≫ (F.eTruncGEIso tC tD m).hom.app K =
        (tD.truncGEπ m).app (F.obj K) :=
    F.eTruncGEπ_app_eTruncGEIsoApp_hom tC tD m K
  refine ⟨fun K ↦ ⟨hLE K, hGE K⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro β hβ
    apply Iso.ext
    ext K
    have := Functor.IsTExact.isLE_obj tC tD F ((tC.truncLT (m + 1)).obj K) (m + 1 - 1)
    exact tD.to_truncLT_obj_ext (Y := F.obj ((tC.truncLT (m + 1)).obj K))
      ((hβ K).trans (hLE K).symm)
  · intro β hβ
    apply Iso.ext
    ext K
    exact cancel_truncGE_unit tD m (Z := (tD.truncGE m).obj (F.obj K))
      ((F.eTruncGEIso tC tD m).app K)
      (F.map ((tC.truncGEπ m).app K)) (hGE K) _ _ ((hβ K).trans (hGE K).symm)
  · intro G _ _ _ η K
    have hGLE : (G.eTruncLTIso tC tD (m + 1 : ℤ)).hom.app K ≫
        (tD.truncLTι (m + 1)).app (G.obj K) =
        G.map ((tC.truncLTι (m + 1)).app K) :=
      G.eTruncLTIsoApp_hom_eTruncLTι_app tC tD (m + 1 : ℤ) K
    have hGGE : G.map ((tC.truncGEπ m).app K) ≫
        (G.eTruncGEIso tC tD m).hom.app K = (tD.truncGEπ m).app (G.obj K) :=
      G.eTruncGEπ_app_eTruncGEIsoApp_hom tC tD m K
    constructor
    · have := Functor.IsTExact.isLE_obj tC tD F
        ((tC.truncLT (m + 1)).obj K) (m + 1 - 1)
      apply tD.to_truncLT_obj_ext
      rw [Category.assoc, hGLE]
      rw [Category.assoc, (tD.truncLTι (m + 1)).naturality]
      rw [← Category.assoc, hLE]
      exact (η.naturality ((tC.truncLTι (m + 1)).app K)).symm
    · have : tD.IsGE ((G ⋙ tD.eTruncGE.obj (m : EInt)).obj K) m := by
        change tD.IsGE ((tD.truncGE m).obj (G.obj K)) m
        infer_instance
      apply cancel_truncGE_unit tD m ((F.eTruncGEIso tC tD m).app K)
        (F.map ((tC.truncGEπ m).app K)) (hGE K)
      erw [← Category.assoc, η.naturality ((tC.truncGEπ m).app K)]
      rw [Category.assoc, hGGE]
      rw [← Category.assoc, hGE]
      exact (tD.truncGEπ m).naturality (η.app K)
  · intro βLE βGE hβLE hβGE K
    constructor
    · change βLE.hom.app K = 𝟙 ((tC.truncLT (m + 1)).obj K)
      have : tC.IsLE ((tC.truncLT (m + 1) ⋙ 𝟭 C).obj K) (m + 1 - 1) := by
        change tC.IsLE ((tC.truncLT (m + 1)).obj K) (m + 1 - 1)
        infer_instance
      apply tC.to_truncLT_obj_ext
      exact (hβLE K).trans (Category.id_comp _).symm
    · have : tC.IsGE ((𝟭 C ⋙ tC.truncGE m).obj K) m := by
        change tC.IsGE ((tC.truncGE m).obj K) m
        infer_instance
      apply tC.from_truncGE_obj_ext
      exact (hβGE K).trans (Category.comp_id _).symm
  · intro B _ _ _ _ _ _ _ tB _ H _ _ _ βLE βGE hβLE hβGE K
    constructor
    · have := Functor.IsTExact.isLE_obj tC tD F
        ((tC.truncLT (m + 1)).obj K) (m + 1 - 1)
      have := Functor.IsTExact.isLE_obj tD tB H
        (F.obj ((tC.truncLT (m + 1)).obj K)) (m + 1 - 1)
      have : tB.IsLE ((tC.truncLT (m + 1) ⋙ F ⋙ H).obj K) (m + 1 - 1) := by
        change tB.IsLE (H.obj (F.obj ((tC.truncLT (m + 1)).obj K))) (m + 1 - 1)
        assumption
      apply tB.to_truncLT_obj_ext
      erw [hβLE K, Category.assoc, Functor.eTruncLTIso_hom_app,
        Functor.eTruncLTIsoApp_hom_eTruncLTι_app, ← H.map_comp, hLE]
    · have : tB.IsGE (((F ⋙ H) ⋙ tB.truncGE m).obj K) m := by
        change tB.IsGE ((tB.truncGE m).obj (H.obj (F.obj K))) m
        infer_instance
      apply cancel_truncGE_unit tB m (βGE.app K)
        (H.map (F.map ((tC.truncGEπ m).app K))) (hβGE K)
      rw [hβGE, ← Category.assoc, ← H.map_comp, hGE]
      exact (H.eTruncGEπ_app_eTruncGEIsoApp_hom tD tB m (F.obj K)).symm

end CategoryTheory.Triangulated.TStructure
