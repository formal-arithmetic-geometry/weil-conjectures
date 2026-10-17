/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorBundle

/-!
# Pullback of a vector bundle

For a vector bundle `π : V ⟶ S` of rank `d` and a cartesian square

```
V' --g'--> V
|          |
π'         π
v          v
S' --g---> S
```

the base change `π' : V' ⟶ S'` is a vector bundle of rank `d`
(`AlgebraicGeometry.VectorBundle.ofIsPullback`): its charts are the base changes of the charts
of `π` over the preimages `g⁻¹(U i)` of the trivialising opens, its coordinates are the pullbacks
of the coordinates (`AlgebraicGeometry.VectorBundle.ofIsPullback_coord`), and its transition
matrices are the pullbacks of the transition matrices.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace VectorBundle

variable {V S V' S' : Scheme.{u}} {d : ℕ} {π : V ⟶ S} (E : VectorBundle d π) {g : S' ⟶ S}
  {g' : V' ⟶ V} {π' : V' ⟶ S'} (sq : IsPullback g' π' π g)

lemma preimage_le_preimage_of_isPullback (U : S.Opens) :
    π' ⁻¹ᵁ g ⁻¹ᵁ U ≤ g' ⁻¹ᵁ π ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, sq.w]

/-- The restriction of `g'` to the preimages of an open `U` of `S`. -/
noncomputable def resPullback (U : S.Opens) :
    (π' ⁻¹ᵁ g ⁻¹ᵁ U).toScheme ⟶ (π ⁻¹ᵁ U).toScheme :=
  g'.resLE (π ⁻¹ᵁ U) (π' ⁻¹ᵁ g ⁻¹ᵁ U) (preimage_le_preimage_of_isPullback sq U)

@[reassoc (attr := simp)]
lemma resPullback_ι (U : S.Opens) :
    resPullback sq U ≫ (π ⁻¹ᵁ U).ι = (π' ⁻¹ᵁ g ⁻¹ᵁ U).ι ≫ g' :=
  Scheme.Hom.resLE_comp_ι _ _

@[reassoc]
lemma resPullback_morphismRestrict (U : S.Opens) :
    resPullback sq U ≫ π ∣_ U = π' ∣_ (g ⁻¹ᵁ U) ≫ g ∣_ U := by
  rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, resPullback_ι_assoc,
    Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc, sq.w]

/-- The base change square restricts to the preimages of an open of the base. -/
lemma isPullback_resPullback (U : S.Opens) :
    IsPullback (resPullback sq U) (π' ∣_ (g ⁻¹ᵁ U)) (π ∣_ U) (g ∣_ U) := by
  have h₁ : IsPullback (resPullback sq U ≫ (π ⁻¹ᵁ U).ι) (π' ∣_ (g ⁻¹ᵁ U)) π
      (g ∣_ U ≫ U.ι) := by
    rw [resPullback_ι, morphismRestrict_ι]
    exact (isPullback_morphismRestrict π' (g ⁻¹ᵁ U)).flip.paste_horiz sq
  exact IsPullback.of_right h₁ (resPullback_morphismRestrict sq U)
    (isPullback_morphismRestrict π U).flip

/-- The chart of `π` over `U i`, base changed to the affine space over `g⁻¹(U i)`, is a pullback
of `π ∣_ U i` along `g`. -/
lemma isPullback_map_chart (i : E.ι) :
    IsPullback (AffineSpace.map (ULift.{u} (Fin d)) (g ∣_ E.U i) ≫ (E.chart i).inv)
      (𝔸(ULift.{u} (Fin d); g ⁻¹ᵁ E.U i) ↘ g ⁻¹ᵁ E.U i) (π ∣_ E.U i) (g ∣_ E.U i) := by
  have h : IsPullback (E.chart i).inv (𝔸(ULift.{u} (Fin d); E.U i) ↘ E.U i) (π ∣_ E.U i)
      (𝟙 _) := IsPullback.of_horiz_isIso ⟨by rw [← E.chart_over, Iso.inv_hom_id_assoc,
        Category.comp_id]⟩
  simpa using (AffineSpace.isPullback_map (n := ULift.{u} (Fin d)) (g ∣_ E.U i)).paste_horiz h

/-- The charts of the base change. -/
noncomputable def chartOfIsPullback (i : E.ι) :
    (π' ⁻¹ᵁ g ⁻¹ᵁ E.U i).toScheme ≅ 𝔸(ULift.{u} (Fin d); g ⁻¹ᵁ E.U i) :=
  (isPullback_resPullback sq (E.U i)).isoIsPullback _ _ (E.isPullback_map_chart i)

@[reassoc (attr := simp)]
lemma chartOfIsPullback_hom_over (i : E.ι) :
    (E.chartOfIsPullback sq i).hom ≫ 𝔸(ULift.{u} (Fin d); g ⁻¹ᵁ E.U i) ↘ g ⁻¹ᵁ E.U i =
      π' ∣_ (g ⁻¹ᵁ E.U i) :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

@[reassoc (attr := simp)]
lemma chartOfIsPullback_hom_map (i : E.ι) :
    (E.chartOfIsPullback sq i).hom ≫ AffineSpace.map (ULift.{u} (Fin d)) (g ∣_ E.U i) =
      resPullback sq (E.U i) ≫ (E.chart i).hom := by
  rw [← cancel_mono (E.chart i).inv, Category.assoc, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]
  exact IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The coordinates of the charts of the base change are the pullbacks of the coordinates. -/
lemma chartOfIsPullback_hom_appTop_coord (i : E.ι) (a : Fin d) :
    (E.chartOfIsPullback sq i).hom.appTop (AffineSpace.coord _ (ULift.up a)) =
      (resPullback sq (E.U i)).appTop (E.coord i a) := by
  have key : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z) (x : Γ(Z, ⊤)),
      (f ≫ h).appTop x = f.appTop (h.appTop x) := fun f h x ↦ by
    rw [Scheme.Hom.comp_appTop]
    rfl
  rw [coord, ← key, ← chartOfIsPullback_hom_map, key, AffineSpace.map_appTop_coord]

/-- The zero section of the base change. -/
noncomputable def zeroOfIsPullback : S' ⟶ V' :=
  sq.lift (g ≫ E.zero) (𝟙 S') (by simp)

@[reassoc (attr := simp)]
lemma zeroOfIsPullback_comp : E.zeroOfIsPullback sq ≫ π' = 𝟙 S' :=
  sq.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma zeroOfIsPullback_g' : E.zeroOfIsPullback sq ≫ g' = g ≫ E.zero :=
  sq.lift_fst _ _ _

lemma zeroOfIsPullback_resLE_resPullback (U : S.Opens) :
    (E.zeroOfIsPullback sq).resLE (π' ⁻¹ᵁ g ⁻¹ᵁ U) (g ⁻¹ᵁ U)
        (Scheme.Hom.le_preimage_preimage_of_comp_eq_id (E.zeroOfIsPullback_comp sq) _) ≫
      resPullback sq U = g ∣_ U ≫ E.zeroRes U := by
  rw [← cancel_mono (π ⁻¹ᵁ U).ι, Category.assoc, resPullback_ι, Scheme.Hom.resLE_comp_ι_assoc,
    zeroOfIsPullback_g', Category.assoc, zeroRes_ι, morphismRestrict_ι_assoc]

/-- Blueprint `def-asd-vector-bundle-zero-section`: Vector bundles

**Base change.** The base change `π' : V' ⟶ S'` of a vector bundle `π : V ⟶ S` of rank `d`
along `g : S' ⟶ S` is a vector bundle of rank `d`, trivialised over the preimages of the
trivialising opens of `π`, with the base changed charts. -/
noncomputable def ofIsPullback : VectorBundle d π' where
  zero := E.zeroOfIsPullback sq
  zero_comp := E.zeroOfIsPullback_comp sq
  ι := E.ι
  U i := g ⁻¹ᵁ E.U i
  iSup_U := by
    rw [← Scheme.Hom.preimage_iSup, E.iSup_U]
    rfl
  chart i := E.chartOfIsPullback sq i
  chart_over i := E.chartOfIsPullback_hom_over sq i
  zero_chart i := by
    refine AffineSpace.hom_ext ?_ fun ⟨a⟩ ↦ ?_
    · rw [Category.assoc, chartOfIsPullback_hom_over, AffineSpace.zeroSection_over,
        ← cancel_mono (g ⁻¹ᵁ E.U i).ι, Category.assoc, morphismRestrict_ι,
        Scheme.Hom.resLE_comp_ι_assoc, zeroOfIsPullback_comp, Category.comp_id,
        Category.id_comp]
    · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, chartOfIsPullback_hom_appTop_coord,
        ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        zeroOfIsPullback_resLE_resPullback, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        ← zeroRes_eq_zeroRestrict, coord_zeroRestrict, map_zero,
        AffineSpace.zeroSection_appTop_coord]
  linear i j := by
    obtain ⟨M, hM, hlin⟩ := E.linear i j
    let r : (g ⁻¹ᵁ (E.U i ⊓ E.U j)).toScheme ⟶ (E.U i ⊓ E.U j).toScheme := g ∣_ (E.U i ⊓ E.U j)
    refine ⟨M.map r.appTop.hom, ?_, fun a ↦ ?_⟩
    · have h := hM.map r.appTop.hom
      rw [RingHom.map_det] at h
      exact h
    have key : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z) (x : Γ(Z, ⊤)),
        (f ≫ h).appTop x = f.appTop (h.appTop x) := fun f h x ↦ by
      rw [Scheme.Hom.comp_appTop]
      rfl
    have hL : ∀ k : E.ι, ∀ (hk : π' ⁻¹ᵁ g ⁻¹ᵁ (E.U i ⊓ E.U j) ≤ π' ⁻¹ᵁ g ⁻¹ᵁ E.U k)
        (hk' : π ⁻¹ᵁ (E.U i ⊓ E.U j) ≤ π ⁻¹ᵁ E.U k),
        V'.homOfLE hk ≫ resPullback sq (E.U k) =
          resPullback sq (E.U i ⊓ E.U j) ≫ V.homOfLE hk' := fun k hk hk' ↦ by
      rw [← cancel_mono (π ⁻¹ᵁ E.U k).ι, Category.assoc, resPullback_ι, Category.assoc,
        Scheme.homOfLE_ι, Scheme.homOfLE_ι_assoc, resPullback_ι]
    have hr : resPullback sq (E.U i ⊓ E.U j) ≫ π ∣_ (E.U i ⊓ E.U j) =
        π' ∣_ (g ⁻¹ᵁ (E.U i ⊓ E.U j)) ≫ r :=
      resPullback_morphismRestrict sq _
    change (V'.homOfLE _ ≫ (E.chartOfIsPullback sq j).hom).appTop _ =
      ∑ b, (π' ∣_ (g ⁻¹ᵁ (E.U i ⊓ E.U j))).appTop (r.appTop (M a b)) *
        (V'.homOfLE _ ≫ (E.chartOfIsPullback sq i).hom).appTop _
    simp only [key _ (E.chartOfIsPullback sq _).hom, chartOfIsPullback_hom_appTop_coord, coord]
    rw [← key, ← key, hL j _ (π.preimage_mono inf_le_right), key, key, hlin a, map_sum]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [map_mul, ← key, hr, key, ← key (V'.homOfLE _), ← key,
      hL i _ (π.preimage_mono inf_le_left), key, key]

@[simp]
lemma ofIsPullback_U (i : E.ι) : (E.ofIsPullback sq).U i = g ⁻¹ᵁ E.U i := rfl

@[simp]
lemma ofIsPullback_zero : (E.ofIsPullback sq).zero = E.zeroOfIsPullback sq := rfl

/-- The coordinates of the base changed charts are the pullbacks of the coordinates. -/
lemma ofIsPullback_coord (i : E.ι) (a : Fin d) :
    (E.ofIsPullback sq).coord i a = (resPullback sq (E.U i)).appTop (E.coord i a) :=
  E.chartOfIsPullback_hom_appTop_coord sq i a

end VectorBundle

end AlgebraicGeometry
