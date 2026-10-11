/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleLimitDescent
public import WeilConjectures.AlgebraicGeometry.Sites.UpperStarSections

/-!
# Sections of inverse images of étale sheaves at a cofiltered limit

Let `X = lim Dⱼ` be a cofiltered limit of quasi-compact quasi-separated schemes over a scheme
`R` with affine transition maps, and let `G` be an abelian étale sheaf on `R`. For a
quasi-compact quasi-separated étale `Dₖ`-scheme `Y` with base change `V = Y ×_{Dₖ} X`, we show
that the sections of the inverse image of `G` over `V` are the filtered colimit of the sections
of the inverse images of `G` over the base changes `Y ×_{Dₖ} Dⱼ`:

- `AlgebraicGeometry.Etale.exists_restrictAlong_eq_zero_of_isLimit`: a section over `Y` which
  vanishes on `V` vanishes on `Y ×_{Dₖ} Dⱼ` for `j` large;
- `AlgebraicGeometry.Etale.exists_restrictAlong_eq_of_isLimit`: every section over `V` comes
  from a section over `Y ×_{Dₖ} Dⱼ` for `j` large.

Both statements are proved by representing sections étale locally by sections of `G`
(`AlgebraicGeometry.Etale.exists_pullSection_eq`), descending the finitely many local data to a
stage (`AlgebraicGeometry.exists_etale_refinement_of_isLimit`,
`AlgebraicGeometry.exists_hom_descent_of_isLimit`, `AlgebraicGeometry.exists_eq_descent_of_isLimit`)
and descending the covering property (`AlgebraicGeometry.exists_forall_mem_range_of_isLimit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace CategoryTheory.IsCofiltered

/-- In a cofiltered category, finitely many morphisms `fᵢ : kᵢ ⟶ k` with common target are
dominated by a single morphism `h : K ⟶ k`: there are `gᵢ : K ⟶ kᵢ` with `gᵢ ≫ fᵢ = h`. -/
lemma exists_comp_eq_of_finite {C : Type*} [Category* C] [IsCofiltered C] {ι : Type*} [Finite ι]
    {k : C} (k₁ : ι → C) (f₁ : ∀ i, k₁ i ⟶ k) :
    ∃ (K : C) (h : K ⟶ k) (g : ∀ i, K ⟶ k₁ i), ∀ i, g i ≫ f₁ i = h := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨S, hS⟩ := IsCofiltered.inf_objs_exists
    (Finset.univ.image (fun i ↦ Over.mk (f₁ i)))
  have hg (i : ι) : Nonempty (S ⟶ Over.mk (f₁ i)) := hS (Finset.mem_image_of_mem _ (by simp))
  exact ⟨S.left, S.hom, fun i ↦ (hg i).some.left, fun i ↦ Over.w (hg i).some⟩

end CategoryTheory.IsCofiltered

namespace AlgebraicGeometry

namespace Etale

variable {J : Type u} [SmallCategory J] [IsCofiltered J] {D : J ⥤ Scheme.{u}} {c : Cone D}
  (hc : IsLimit c) {R : Scheme.{u}} (π : D ⟶ (Functor.const J).obj R) (P : c.pt ⟶ R)
  (hP : ∀ j, P = c.π.app j ≫ π.app j)

include hc hP in
/-- **Local descent of a morphism to an étale `R`-scheme.** Let `Y` be étale over a stage `Dₖ`,
`m : V ⟶ Y` a morphism over `X ⟶ Dₖ` from an étale `X`-scheme, `a : V'' ⟶ V` étale and
`φ : V'' ⟶ U` a morphism over `R` to an étale `R`-scheme. Around every point of `V''` there is an
affine scheme `E` étale over a later stage `Dₖ₁`, with a morphism `e : E ⟶ Y` and a morphism
`ψ : E ⟶ U` over `R`, such that `E ×_{Dₖ₁} X` maps to `V''` compatibly with `e` and `ψ`. -/
lemma exists_local_descent_of_isLimit [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)] {k : J}
    (Y : (D.obj k).Etale) {V : c.pt.Etale} (m : V.left ⟶ Y.left)
    (hm : m ≫ Y.hom = V.hom ≫ c.π.app k) {V'' : c.pt.Etale} (a : V'' ⟶ V) {U : R.Etale}
    (φ : V''.left ⟶ U.left) (hφ : φ ≫ U.hom = V''.hom ≫ P) (z : V''.left) :
    ∃ (k₁ : J) (f₁ : k₁ ⟶ k) (E : (D.obj k₁).Etale) (_ : IsAffine E.left) (e : E.left ⟶ Y.left)
      (_ : e ≫ Y.hom = E.hom ≫ D.map f₁) (ψ : E.left ⟶ U.left)
      (_ : ψ ≫ U.hom = E.hom ≫ π.app k₁) (Z : c.pt.Etale) (u : Z.left ⟶ E.left)
      (_ : IsPullback u Z.hom E.hom (c.π.app k₁)) (w : Z ⟶ V''),
      u ≫ e = w.left ≫ a.left ≫ m ∧ u ≫ ψ = w.left ≫ φ ∧ z ∈ Set.range w.left := by
  let β : V''.left ⟶ pullback Y.hom (c.π.app k) := pullback.lift (a.left ≫ m) V''.hom (by
    rw [Category.assoc, hm, MorphismProperty.Over.w_assoc])
  have : Etale (β ≫ pullback.snd _ _) := by
    rw [pullback.lift_snd]
    infer_instance
  have : Etale β := Etale.of_comp β (pullback.snd _ _)
  obtain ⟨k', f, E, hE, q, hq, e, he, E', π₁, π₂, hπ, γ, hγ, hz⟩ :=
    exists_etale_refinement_of_isLimit D c hc Y.hom β z
  have hγ₂ : γ ≫ V''.hom = π₂ := by
    have := congrArg (· ≫ pullback.snd Y.hom (c.π.app k)) hγ
    simpa [β] using this
  have hγ₁ : γ ≫ a.left ≫ m = π₁ ≫ e := by
    have := congrArg (· ≫ pullback.fst Y.hom (c.π.app k)) hγ
    simpa [β] using this
  obtain ⟨k'', f', ψ, hψ, hψφ⟩ := exists_hom_descent_of_isLimit D c hc π q U.hom
    (hπ.isoPullback.inv ≫ γ ≫ φ) (by
      rw [Category.assoc, Category.assoc, hφ, reassoc_of% hγ₂, IsPullback.isoPullback_inv_snd_assoc,
        hP])
  have : IsAffineHom (pullback.fst q (D.map f')) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have : IsAffine (pullback q (D.map f')) := isAffine_of_isAffineHom (pullback.fst q (D.map f'))
  have : Etale π₂ := MorphismProperty.of_isPullback hπ hq
  let u : E' ⟶ pullback q (D.map f') :=
    pullback.lift π₁ (π₂ ≫ c.π.app k'') (by rw [hπ.w, Category.assoc, c.w f'])
  have hu : IsPullback u π₂ (pullback.snd q (D.map f')) (c.π.app k'') := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback q (D.map f'))
    rw [pullback.lift_fst, c.w f']
    exact hπ
  have hu' : u = hπ.isoPullback.hom ≫ pullback.map q (c.π.app k') q (D.map f') (𝟙 _)
      (c.π.app k'') (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [u]
  refine ⟨k'', f' ≫ f, MorphismProperty.Over.mk ⊤ (pullback.snd q (D.map f')) inferInstance,
    ‹IsAffine (pullback q (D.map f'))›, pullback.fst q (D.map f') ≫ e, ?_, ψ, hψ,
    MorphismProperty.Over.mk ⊤ π₂ inferInstance, u, hu, MorphismProperty.Over.homMk γ hγ₂,
    ?_, ?_, hz⟩
  · simp [he, pullback.condition_assoc]
  · simp [u, hγ₁]
  · simp [hu', hψφ]

include hc in
/-- **Local data covering at the limit cover at a stage.** Let `Y` be quasi-compact and étale
over a stage `Dₖ`, with base change `m : V ⟶ Y` to the limit, and let `eᵢ : Eᵢ ⟶ Y` be finitely
many morphisms over `Dₖᵢ ⟶ Dₖ` from étale `Dₖᵢ`-schemes, such that the points of `V` are covered
by étale `X`-schemes mapping compatibly to `V` and the `Eᵢ`. Then there is a stage `K` over all
the `kᵢ` such that for every `m' : V' ⟶ Y` over a later stage `Dₖ' ⟶ D_K ⟶ Dₖ`, every point of
`V'` lies in the image of some `Eᵢ`, in the sense that its image in `Y ×_{Dₖ} Dₖᵢ` lies in the
image of `Eᵢ`. -/
lemma exists_forall_mem_range_lift_of_isLimit [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ j, CompactSpace (D.obj j)]
    {k : J} (Y : (D.obj k).Etale) [CompactSpace Y.left] {V : c.pt.Etale} (m : V.left ⟶ Y.left)
    (hm : IsPullback m V.hom Y.hom (c.π.app k)) {ι : Type*} [Finite ι] (k₁ : ι → J)
    (f₁ : ∀ i, k₁ i ⟶ k) (E : ∀ i, (D.obj (k₁ i)).Etale) (e : ∀ i, (E i).left ⟶ Y.left)
    (he : ∀ i, e i ≫ Y.hom = (E i).hom ≫ D.map (f₁ i))
    (hcov : ∀ x : V.left, ∃ (i : ι) (Z : c.pt.Etale) (u : Z.left ⟶ (E i).left)
      (_ : u ≫ (E i).hom = Z.hom ≫ c.π.app (k₁ i)) (v : Z ⟶ V),
        u ≫ e i = v.left ≫ m ∧ x ∈ Set.range v.left) :
    ∃ (K : J) (h : K ⟶ k) (g : ∀ i, K ⟶ k₁ i) (hg : ∀ i, g i ≫ f₁ i = h),
      ∀ ⦃K' : J⦄ (h' : K' ⟶ K) (V' : (D.obj K').Etale) (m' : V'.left ⟶ Y.left)
        (hm' : m' ≫ Y.hom = V'.hom ≫ D.map (h' ≫ h)) (y : V'.left), ∃ i : ι,
        pullback.lift m' (V'.hom ≫ D.map (h' ≫ g i))
          (by rw [hm', Category.assoc, ← Functor.map_comp, Category.assoc, hg])
          y ∈ Set.range (pullback.lift (e i) (E i).hom (he i)) := by
  obtain ⟨K, h, g, hg⟩ := IsCofiltered.exists_comp_eq_of_finite k₁ f₁
  -- the base changes of the `Eᵢ` to the stage `K`, étale over `Y ×_{Dₖ} D_K`
  let eK (i : ι) : pullback (E i).hom (D.map (g i)) ⟶ pullback Y.hom (D.map h) :=
    pullback.map _ _ _ _ (e i) (𝟙 _) (D.map (f₁ i)) (he i).symm (by simp [← hg i])
  have (i : ι) : Etale (eK i) := by
    have : Etale (eK i ≫ pullback.snd Y.hom (D.map h)) := by
      rw [pullback.lift_snd, Category.comp_id]
      infer_instance
    exact Etale.of_comp (eK i) (pullback.snd Y.hom (D.map h))
  have : CompactSpace ↥(pullback Y.hom (D.map h)) := baseChange_compactSpace (Y := Y.left) h Y.hom
  obtain ⟨K₁, f, H⟩ := exists_forall_mem_range_of_isLimit D c hc
    (pullback.snd Y.hom (D.map h)) eK (fun x ↦ by
      let L : pullback (pullback.snd Y.hom (D.map h)) (c.π.app K) ⟶ V.left :=
        hm.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _) (by
          rw [Category.assoc, pullback.condition, pullback.condition_assoc, c.w])
      obtain ⟨i, Z, u, hu, v, hv, z, hz⟩ := hcov (L x)
      let M : V.left ⟶ pullback Y.hom (D.map h) :=
        pullback.lift m (V.hom ≫ c.π.app K) (by rw [hm.w, Category.assoc, c.w])
      have hLM : L ≫ M = pullback.fst _ _ := by
        apply pullback.hom_ext
        · simp [L, M]
        · simp [L, M, pullback.condition]
      let uK : Z.left ⟶ pullback (E i).hom (D.map (g i)) :=
        pullback.lift u (Z.hom ≫ c.π.app K) (by rw [hu, Category.assoc, c.w])
      have huv : uK ≫ eK i = v.left ≫ M := by
        apply pullback.hom_ext
        · simp [uK, eK, M, hv]
        · simp [uK, eK, M]
      refine ⟨i, uK z, ?_⟩
      rw [← Scheme.Hom.comp_apply, huv, Scheme.Hom.comp_apply, hz, ← Scheme.Hom.comp_apply, hLM])
  refine ⟨K₁, f ≫ h, fun i ↦ f ≫ g i, fun i ↦ by rw [Category.assoc, hg], ?_⟩
  intro K' h' V' m' hm' y
  let Λ : V'.left ⟶ pullback Y.hom (D.map h) :=
    pullback.lift m' (V'.hom ≫ D.map (h' ≫ f)) (by
      rw [hm', Category.assoc, ← Functor.map_comp, Category.assoc])
  obtain ⟨i, ε, hε⟩ := H K' h' (pullback.lift Λ V'.hom (by simp [Λ]) y)
  rw [← Scheme.Hom.comp_apply, pullback.lift_fst] at hε
  let ρ : pullback Y.hom (D.map h) ⟶ pullback Y.hom (D.map (f₁ i)) :=
    pullback.map _ _ _ _ (𝟙 _) (D.map (g i)) (𝟙 _) (by simp) (by simp [← hg i])
  have key₁ : eK i ≫ ρ = pullback.fst _ _ ≫ pullback.lift (e i) (E i).hom (he i) := by
    apply pullback.hom_ext
    · simp [eK, ρ]
    · simp [eK, ρ, pullback.condition]
  have key₂ : Λ ≫ ρ = pullback.lift m' (V'.hom ≫ D.map (h' ≫ f ≫ g i)) (by
      rw [hm', Category.assoc, ← Functor.map_comp, Category.assoc, Category.assoc, hg]) := by
    apply pullback.hom_ext
    · simp [Λ, ρ]
    · simp [Λ, ρ]
  refine ⟨i, pullback.fst (E i).hom (D.map (g i)) ε, ?_⟩
  calc _ = ρ (eK i ε) := by
        rw [← Scheme.Hom.comp_apply (eK i) ρ, key₁, Scheme.Hom.comp_apply]
        rfl
    _ = ρ (Λ y) := by rw [hε]
    _ = _ := by rw [← Scheme.Hom.comp_apply Λ ρ, key₂]

omit [IsCofiltered J] in
/-- The structure morphisms of the stages to `R` are compatible with the transition maps. -/
lemma app_eq_map_comp_app {k k' : J} (g : k' ⟶ k) : π.app k' = D.map g ≫ π.app k := by
  simpa using (π.naturality g).symm

variable (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- `restrictAlong` only depends on the morphism of base schemes through its value. -/
lemma restrictAlong_congr_hom {T T' : Scheme.{u}} (t : T ⟶ R) {f₁ f₂ : T' ⟶ T} (t' : T' ⟶ R)
    (ht' : t' = f₁ ≫ t) (h : f₁ = f₂) {V : T.Etale} {V' : T'.Etale} (m : V'.left ⟶ V.left)
    (hm : m ≫ V.hom = V'.hom ≫ f₁) :
    restrictAlong t G f₁ t' ht' m hm = restrictAlong t G f₂ t' (h ▸ ht') m (h ▸ hm) := by
  subst h
  rfl

include hc hP in
/-- (Implementation) **Local vanishing at a stage.** If a section `s` over an étale `Dₖ`-scheme
`Y` vanishes on the base change `V` of `Y` to the limit, then every point of `V` is covered by
an étale `X`-scheme mapping compatibly to `V` and to an étale scheme `E` over a later stage,
mapping to `Y`, on which `s` vanishes. -/
lemma exists_local_restrictAlong_eq_zero_of_isLimit [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)] {k : J}
    (Y : (D.obj k).Etale) {V : c.pt.Etale} (m : V.left ⟶ Y.left)
    (hm : m ≫ Y.hom = V.hom ≫ c.π.app k)
    (s : ((π.app k)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op Y))
    (hs : restrictAlong (π.app k) G (c.π.app k) P (hP k) m hm s = 0) (x : V.left) :
    ∃ (k₁ : J) (f₁ : k₁ ⟶ k) (E : (D.obj k₁).Etale) (e : E.left ⟶ Y.left)
      (he : e ≫ Y.hom = E.hom ≫ D.map f₁)
      (_ : restrictAlong (π.app k) G (D.map f₁) (π.app k₁) (app_eq_map_comp_app π f₁) e he s = 0)
      (Z : c.pt.Etale) (u : Z.left ⟶ E.left) (_ : u ≫ E.hom = Z.hom ≫ c.π.app k₁) (v : Z ⟶ V),
      u ≫ e = v.left ≫ m ∧ x ∈ Set.range v.left := by
  obtain ⟨Ya, b, U, φ, hφ, g, ⟨ya, hya⟩, hsa⟩ := exists_pullSection_eq (π.app k) G s (m x)
  obtain ⟨xa, hxa₁, hxa₂⟩ := Scheme.Pullback.exists_preimage_pullback x ya hya.symm
  have hsnd : pullback.snd m b.left ≫ Ya.hom = (pullbackObj m b).hom ≫ c.π.app k := by
    rw [pullbackObj_hom, Category.assoc, ← hm, ← MorphismProperty.Over.w b,
      pullback.condition_assoc]
  have h0 : pullSection P G (V := pullbackObj m b) (pullback.snd m b.left ≫ φ)
      (by rw [Category.assoc, hφ, reassoc_of% hsnd, ← hP]) g = 0 := by
    calc _ = restrictAlong (π.app k) G (c.π.app k) P (hP k) _ hsnd
          (pullSection (π.app k) G φ hφ g) :=
          (restrictAlong_pullSection (π.app k) G (c.π.app k) P (hP k) _ hsnd φ hφ g).symm
      _ = restrictAlong (π.app k) G (c.π.app k) P (hP k) (pullback.snd m b.left ≫ b.left)
          (by rw [Category.assoc, MorphismProperty.Over.w b, hsnd]) s := by
        rw [← hsa, restrictAlong_map]
      _ = restrictAlong (π.app k) G (c.π.app k) P (hP k) ((pullbackObjFst m b).left ≫ m)
          (by rw [Category.assoc, hm, ← Category.assoc, MorphismProperty.Over.w]) s :=
        ConcreteCategory.congr_hom (restrictAlong_congr _ _ _ _ _ _ pullback.condition.symm) s
      _ = 0 := by rw [← map_restrictAlong _ _ _ _ _ (pullbackObjFst m b) m hm, hs, map_zero]
  obtain ⟨V'', a, U', b', φ', hφ', ⟨z, hz⟩, hfac, hg0⟩ :=
    exists_of_pullSection_eq_zero P G _ _ g h0 xa
  obtain ⟨k₁, f₁, E, hE, e, he, ψ, hψ, Z, u, hu, w, hue, huψ, ⟨z', hz'⟩⟩ :=
    exists_local_descent_of_isLimit hc π P hP Ya (pullback.snd m b.left) hsnd a φ' hφ' z
  have : CompactSpace ↥((𝟭 Scheme).obj E.left) := inferInstanceAs (CompactSpace E.left)
  obtain ⟨k₂, f₂, heq⟩ := exists_eq_descent_of_isLimit D c hc π E.hom U.hom (ψ ≫ b'.left)
    (e ≫ φ) (by rw [Category.assoc, MorphismProperty.Over.w b', hψ])
    (by rw [Category.assoc, hφ, reassoc_of% he, ← app_eq_map_comp_app])
    (by
      rw [← hu.isoPullback_inv_fst, Category.assoc, Category.assoc, reassoc_of% huψ, hfac,
        reassoc_of% hue])
  let E₂ : (D.obj k₂).Etale :=
    MorphismProperty.Over.mk ⊤ (pullback.snd E.hom (D.map f₂)) inferInstance
  have he₂ : (pullback.fst E.hom (D.map f₂) ≫ e) ≫ Ya.hom = E₂.hom ≫ D.map (f₂ ≫ f₁) := by
    simp [E₂, he, pullback.condition_assoc]
  refine ⟨k₂, f₂ ≫ f₁, E₂, pullback.fst E.hom (D.map f₂) ≫ e ≫ b.left, ?_, ?_, Z,
    pullback.lift u (Z.hom ≫ c.π.app k₂) (by rw [hu.w, Category.assoc, c.w]),
    pullback.lift_snd _ _ _, w ≫ a ≫ pullbackObjFst m b, ?_, ?_⟩
  · simp [E₂, he, pullback.condition_assoc]
  · calc _ = restrictAlong (π.app k) G (D.map (f₂ ≫ f₁)) (π.app k₂) (app_eq_map_comp_app π _)
          ((pullback.fst E.hom (D.map f₂) ≫ e) ≫ b.left)
          (by rw [Category.assoc, MorphismProperty.Over.w b, he₂]) s :=
          ConcreteCategory.congr_hom
            (restrictAlong_congr _ _ _ _ _ _ (Category.assoc _ _ _).symm) s
      _ = _ :=
          (restrictAlong_map _ _ _ _ _ b _ he₂ s).symm
      _ = pullSection (π.app k₂) G (V := E₂) ((pullback.fst E.hom (D.map f₂) ≫ e) ≫ φ)
          (by rw [Category.assoc, hφ, ← Category.assoc, he₂, Category.assoc,
            ← app_eq_map_comp_app]) g := by
        rw [hsa, restrictAlong_pullSection]
      _ = pullSection (π.app k₂) G (V := E₂) ((pullback.fst E.hom (D.map f₂) ≫ ψ) ≫ b'.left)
          (by rw [Category.assoc, MorphismProperty.Over.w b', Category.assoc, hψ]
              simp [E₂, pullback.condition_assoc]) g :=
        pullSection_congr _ _ _ (by simpa using heq.symm) g
      _ = 0 := by
        rw [pullSection_comp (hφ := by
          rw [Category.assoc, hψ]
          simp [E₂, pullback.condition_assoc]), hg0, pullSection_zero]
  · simp [reassoc_of% hue, pullback.condition]
  · refine ⟨z', ?_⟩
    rw [← hxa₁, ← hz, ← hz']
    rfl

include hc hP in
/-- **Injectivity of the comparison of sections at a cofiltered limit.** Let `Y` be a
quasi-compact étale scheme over a stage `Dₖ`, with base change `m : V ⟶ Y` to the limit `X`, and
let `s` be a section of the inverse image of `G` over `Y` whose restriction to `V` vanishes. Then
the restriction of `s` along every morphism `V' ⟶ Y` over a late enough stage `Dₖ'' ⟶ Dₖ`
vanishes. -/
theorem exists_restrictAlong_eq_zero_of_isLimit [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)] {k : J}
    (Y : (D.obj k).Etale) [CompactSpace Y.left] {V : c.pt.Etale} (m : V.left ⟶ Y.left)
    (hm : IsPullback m V.hom Y.hom (c.π.app k))
    (s : ((π.app k)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op Y))
    (hs : restrictAlong (π.app k) G (c.π.app k) P (hP k) m hm.w s = 0) :
    ∃ (k' : J) (f : k' ⟶ k), ∀ ⦃k'' : J⦄ (g' : k'' ⟶ k') (g : k'' ⟶ k), g' ≫ f = g →
      ∀ (V' : (D.obj k'').Etale) (m' : V'.left ⟶ Y.left) (hm' : m' ≫ Y.hom = V'.hom ≫ D.map g),
        restrictAlong (π.app k) G (D.map g) (π.app k'') (app_eq_map_comp_app π g) m' hm' s = 0 := by
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  have : QuasiCompact Y.hom := @quasiCompact_of_compactSpace _ _ Y.hom
    (inferInstanceAs (CompactSpace Y.left)) (inferInstanceAs (QuasiSeparatedSpace (D.obj k)))
  have : QuasiCompact V.hom := MorphismProperty.of_isPullback hm this
  have : CompactSpace V.left := @QuasiCompact.compactSpace_of_compactSpace _ _ V.hom _
    (inferInstanceAs (CompactSpace c.pt))
  choose k₁ f₁ E e he hvan Z u hu v hv hx using
    exists_local_restrictAlong_eq_zero_of_isLimit hc π P hP G Y m hm.w s hs
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ Set.range (v x).left)
    (fun x ↦ (v x).left.isOpenMap.isOpen_range) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hx x⟩)
  obtain ⟨K, h, g₀, hg₀, H⟩ := exists_forall_mem_range_lift_of_isLimit hc Y m hm (ι := t)
    (fun i ↦ k₁ i) (fun i ↦ f₁ i) (fun i ↦ E i) (fun i ↦ e i) (fun i ↦ he i) (fun x ↦ by
      obtain ⟨i, hi, hxi⟩ : ∃ i ∈ t, x ∈ Set.range (v i).left := by
        simpa using ht (Set.mem_univ x)
      exact ⟨⟨i, hi⟩, Z i, u i, hu i, v i, hv i, hxi⟩)
  refine ⟨K, h, fun k'' g' g hg V' m' hm' ↦ ?_⟩
  subst hg
  let τ (i : t) : (E i).left ⟶ pullback Y.hom (D.map (f₁ i)) :=
    pullback.lift (e i) (E i).hom (he i)
  have (i : t) : Etale (τ i) := by
    have : Etale (τ i ≫ pullback.snd Y.hom (D.map (f₁ i))) := by
      rw [pullback.lift_snd]
      infer_instance
    exact Etale.of_comp (τ i) (pullback.snd Y.hom (D.map (f₁ i)))
  let Λ' (i : t) : V'.left ⟶ pullback Y.hom (D.map (f₁ i)) :=
    pullback.lift m' (V'.hom ≫ D.map (g' ≫ g₀ i))
      (by rw [hm', Category.assoc, ← Functor.map_comp, Category.assoc, hg₀])
  let W (i : t) : (D.obj k'').Etale :=
    MorphismProperty.Over.mk ⊤ (pullback.fst (Λ' i) (τ i) ≫ V'.hom) inferInstance
  let a (i : t) : W i ⟶ V' := MorphismProperty.Over.homMk (pullback.fst (Λ' i) (τ i)) rfl
  refine eq_zero_of_forall_map_eq_zero _ a (fun y ↦ ?_) _ (fun i ↦ ?_)
  · obtain ⟨i, hi⟩ := H g' V' m' hm' y
    refine ⟨i, ?_⟩
    show y ∈ Set.range (pullback.fst (Λ' i) (τ i))
    rw [Scheme.Pullback.range_fst]
    exact hi
  · have hsnd : pullback.snd (Λ' i) (τ i) ≫ (E i).hom = (W i).hom ≫ D.map (g' ≫ g₀ i) := by
      have := pullback.condition (f := Λ' i) (g := τ i) =≫ pullback.snd _ _
      simpa [τ, Λ', W] using this.symm
    have hfst : (a i).left ≫ m' = pullback.snd (Λ' i) (τ i) ≫ e i := by
      have := pullback.condition (f := Λ' i) (g := τ i) =≫ pullback.fst _ _
      simpa [τ, Λ', a] using this
    have e₁ : D.map (g' ≫ h) = D.map (g' ≫ g₀ i) ≫ D.map (f₁ i) := by
      rw [← Functor.map_comp, Category.assoc, hg₀]
    rw [map_restrictAlong, restrictAlong_congr_hom G (π.app k) (π.app k'') _ e₁,
      restrictAlong_congr (h := hfst), ← restrictAlong_restrictAlong (π.app k) G (D.map (f₁ i))
        (π.app (k₁ i)) (app_eq_map_comp_app π _) (D.map (g' ≫ g₀ i)) (π.app k'')
        (app_eq_map_comp_app π _) (e i) (he i) _ hsnd s, hvan, map_zero]

end Etale

end AlgebraicGeometry
