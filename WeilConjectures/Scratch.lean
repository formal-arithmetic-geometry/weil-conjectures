module

public import WeilConjectures.Blowup.EliminationOfIndeterminacy

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Transporting an extension along a lift of a blow-up over an open of the base.** -/
theorem exists_extend_of_lift {X X' Y Bl : Scheme.{u}} {p : Y ⟶ X} {π : X' ⟶ X} {V : X.Opens}
    {b : Bl ⟶ V.toScheme} {ρ : (π ⁻¹ᵁ V).toScheme ⟶ Bl} (hρ : ρ ≫ b = π ∣_ V)
    {W : Bl.Opens} {g : W.toScheme ⟶ (p ⁻¹ᵁ V).toScheme}
    (hg : g ≫ (p ∣_ V) = W.ι ≫ b)
    (hclosed : IsClosed (Set.range (pullback.lift g W.ι hg))) :
    ∃ (W' : X'.Opens) (hW' : W' ≤ π ⁻¹ᵁ V) (G : W'.toScheme ⟶ Y)
      (hG : G ≫ p = W'.ι ≫ π) (e : W'.toScheme ⟶ W.toScheme),
      (∀ x : (π ⁻¹ᵁ V).toScheme, x.1 ∈ W' ↔ ρ x ∈ W) ∧
      e ≫ W.ι = X'.homOfLE hW' ≫ ρ ∧
      G = e ≫ g ≫ (p ⁻¹ᵁ V).ι ∧
      IsClosed (⇑((pullback.snd p π) ⁻¹ᵁ (π ⁻¹ᵁ V)).ι ⁻¹'
        Set.range (pullback.lift G W'.ι hG)) := by
  have hW' : (π ⁻¹ᵁ V).ι ''ᵁ (ρ ⁻¹ᵁ W) ≤ π ⁻¹ᵁ V := (π ⁻¹ᵁ V).ι_image_le _
  have hεinv : ((π ⁻¹ᵁ V).ι.isoImage (ρ ⁻¹ᵁ W)).inv ≫ (ρ ⁻¹ᵁ W).ι = X'.homOfLE hW' :=
    (π ⁻¹ᵁ V).isoImage_ι_inv_ι _
  have he : (((π ⁻¹ᵁ V).ι.isoImage (ρ ⁻¹ᵁ W)).inv ≫ (ρ ∣_ W)) ≫ W.ι =
      X'.homOfLE hW' ≫ ρ := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hεinv]
  have key : ρ ≫ b ≫ V.ι = (π ⁻¹ᵁ V).ι ≫ π := by
    rw [← Category.assoc, hρ, morphismRestrict_ι]
  have hg' : g ≫ (p ⁻¹ᵁ V).ι ≫ p = W.ι ≫ b ≫ V.ι := by
    rw [← morphismRestrict_ι p V, ← Category.assoc, hg, Category.assoc]
  have hG'' : ((ρ ∣_ W) ≫ g ≫ (p ⁻¹ᵁ V).ι) ≫ p = ((ρ ⁻¹ᵁ W).ι ≫ (π ⁻¹ᵁ V).ι) ≫ π := by
    calc ((ρ ∣_ W) ≫ g ≫ (p ⁻¹ᵁ V).ι) ≫ p
        = (ρ ∣_ W) ≫ (g ≫ (p ⁻¹ᵁ V).ι ≫ p) := by simp only [Category.assoc]
      _ = ((ρ ∣_ W) ≫ W.ι) ≫ b ≫ V.ι := by rw [hg']; simp only [Category.assoc]
      _ = (ρ ⁻¹ᵁ W).ι ≫ (ρ ≫ b ≫ V.ι) := by
          rw [morphismRestrict_ι]; simp only [Category.assoc]
      _ = ((ρ ⁻¹ᵁ W).ι ≫ (π ⁻¹ᵁ V).ι) ≫ π := by rw [key]; simp only [Category.assoc]
  have hG : ((((π ⁻¹ᵁ V).ι.isoImage (ρ ⁻¹ᵁ W)).inv ≫ (ρ ∣_ W)) ≫ g ≫ (p ⁻¹ᵁ V).ι) ≫ p =
      ((π ⁻¹ᵁ V).ι ''ᵁ (ρ ⁻¹ᵁ W)).ι ≫ π := by
    calc ((((π ⁻¹ᵁ V).ι.isoImage (ρ ⁻¹ᵁ W)).inv ≫ (ρ ∣_ W)) ≫ g ≫ (p ⁻¹ᵁ V).ι) ≫ p
        = ((π ⁻¹ᵁ V).ι.isoImage (ρ ⁻¹ᵁ W)).inv ≫
            (((ρ ∣_ W) ≫ g ≫ (p ⁻¹ᵁ V).ι) ≫ p) := by simp only [Category.assoc]
      _ = (((π ⁻¹ᵁ V).ι.isoImage (ρ ⁻¹ᵁ W)).inv ≫ (ρ ⁻¹ᵁ W).ι) ≫ (π ⁻¹ᵁ V).ι ≫ π := by
          rw [hG'']; simp only [Category.assoc]
      _ = ((π ⁻¹ᵁ V).ι ''ᵁ (ρ ⁻¹ᵁ W)).ι ≫ π := by
          rw [hεinv, ← Category.assoc, Scheme.homOfLE_ι]
  refine ⟨_, hW', _, hG, _, fun x ↦ ?_, he, rfl, ?_⟩
  · rw [Scheme.Opens.mem_ι_image_iff]
    exact Iff.rfl
  -- the graph is closed over `V`
  · -- the local graph is a closed immersion
    have hpreΓl : IsPreimmersion (pullback.lift g W.ι hg) := by
      have h : IsPreimmersion ((pullback.lift g W.ι hg) ≫ pullback.snd (p ∣_ V) b) := by
        rw [pullback.lift_snd]; infer_instance
      exact IsPreimmersion.of_comp' _ (pullback.snd (p ∣_ V) b)
    have hciΓl : IsClosedImmersion (pullback.lift g W.ι hg) := .of_isPreimmersion _ hclosed
    -- the locus of `Y ×_X X'` above `V` is `(π ⁻¹ᵁ V) ×_X Y`
    have hS : IsPullback ((pullback.snd p π) ∣_ (π ⁻¹ᵁ V))
        (((pullback.snd p π) ⁻¹ᵁ (π ⁻¹ᵁ V)).ι ≫ pullback.fst p π) ((π ⁻¹ᵁ V).ι ≫ π) p :=
      (isPullback_morphismRestrict (pullback.snd p π) (π ⁻¹ᵁ V)).paste_vert
        (IsPullback.of_hasPullback p π).flip
    have hwu : (((pullback.snd p π) ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) ≫ V.ι =
        (((pullback.snd p π) ⁻¹ᵁ (π ⁻¹ᵁ V)).ι ≫ pullback.fst p π) ≫ p := by
      rw [Category.assoc, morphismRestrict_ι]; exact hS.w
    obtain ⟨u, hufst, husnd⟩ :
        ∃ u : ((pullback.snd p π) ⁻¹ᵁ (π ⁻¹ᵁ V)).toScheme ⟶ (p ⁻¹ᵁ V).toScheme,
          u ≫ (p ⁻¹ᵁ V).ι = ((pullback.snd p π) ⁻¹ᵁ (π ⁻¹ᵁ V)).ι ≫ pullback.fst p π ∧
          u ≫ (p ∣_ V) = ((pullback.snd p π) ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V) :=
      ⟨(isPullback_morphismRestrict p V).lift _ _ hwu,
        (isPullback_morphismRestrict p V).lift_snd _ _ hwu,
        (isPullback_morphismRestrict p V).lift_fst _ _ hwu⟩
    have hs2 : IsPullback ((pullback.snd p π) ∣_ (π ⁻¹ᵁ V)) u (π ∣_ V) (p ∣_ V) := by
      refine IsPullback.of_bot ?_ husnd.symm (isPullback_morphismRestrict p V)
      rw [hufst, morphismRestrict_ι]
      exact hS
    obtain ⟨Θ, hΘfst, hΘsnd⟩ :
        ∃ Θ : ((pullback.snd p π) ⁻¹ᵁ (π ⁻¹ᵁ V)).toScheme ⟶ pullback (p ∣_ V) b,
          Θ ≫ pullback.fst (p ∣_ V) b = u ∧
          Θ ≫ pullback.snd (p ∣_ V) b = ((pullback.snd p π) ∣_ (π ⁻¹ᵁ V)) ≫ ρ := by
      refine ⟨pullback.lift u (((pullback.snd p π) ∣_ (π ⁻¹ᵁ V)) ≫ ρ) ?_,
        pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
      rw [husnd, Category.assoc, hρ]
    have hK : IsPullback ((pullback.snd p π) ∣_ (π ⁻¹ᵁ V)) Θ ρ (pullback.snd (p ∣_ V) b) := by
      refine IsPullback.of_bot ?_ hΘsnd.symm (IsPullback.of_hasPullback (p ∣_ V) b).flip
      rw [hΘfst, hρ]
      exact hs2
    obtain ⟨Γ₀, hΓ₀fst, hΓ₀snd⟩ :
        ∃ Γ₀ : (ρ ⁻¹ᵁ W).toScheme ⟶ ((pullback.snd p π) ⁻¹ᵁ (π ⁻¹ᵁ V)).toScheme,
          Γ₀ ≫ ((pullback.snd p π) ∣_ (π ⁻¹ᵁ V)) = (ρ ⁻¹ᵁ W).ι ∧
          Γ₀ ≫ ((pullback.snd p π) ⁻¹ᵁ (π ⁻¹ᵁ V)).ι =
            pullback.lift ((ρ ∣_ W) ≫ g ≫ (p ⁻¹ᵁ V).ι) ((ρ ⁻¹ᵁ W).ι ≫ (π ⁻¹ᵁ V).ι) hG'' :=
      ⟨(isPullback_morphismRestrict (pullback.snd p π) (π ⁻¹ᵁ V)).lift _ _
          (pullback.lift_snd _ _ _).symm,
        IsPullback.lift_fst _ _ _ _, IsPullback.lift_snd _ _ _ _⟩
    have hsq : IsPullback Γ₀ (ρ ∣_ W) Θ (pullback.lift g W.ι hg) := by
      refine IsPullback.of_right ?_ ?_ hK
      · rw [hΓ₀fst, pullback.lift_snd]
        exact (isPullback_morphismRestrict ρ W).flip
      · apply pullback.hom_ext
        · rw [Category.assoc, hΘfst, Category.assoc, pullback.lift_fst,
            ← cancel_mono (p ⁻¹ᵁ V).ι, Category.assoc, hufst, Category.assoc,
            ← Category.assoc Γ₀, hΓ₀snd, pullback.lift_fst]
        · rw [Category.assoc, hΘsnd, Category.assoc, pullback.lift_snd, ← Category.assoc,
            hΓ₀fst, morphismRestrict_ι]
    have hciΓ₀ : IsClosedImmersion Γ₀ :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip hciΓl
    have hclosed₀ : IsClosed (Set.range Γ₀) := Γ₀.isClosedEmbedding.isClosed_range
    -- the two graphs have the same range
    have hΓeq : ((π ⁻¹ᵁ V).ι.isoImage (ρ ⁻¹ᵁ W)).inv ≫
        pullback.lift ((ρ ∣_ W) ≫ g ≫ (p ⁻¹ᵁ V).ι) ((ρ ⁻¹ᵁ W).ι ≫ (π ⁻¹ᵁ V).ι) hG'' =
        pullback.lift ((((π ⁻¹ᵁ V).ι.isoImage (ρ ⁻¹ᵁ W)).inv ≫ (ρ ∣_ W)) ≫ g ≫ (p ⁻¹ᵁ V).ι)
          ((π ⁻¹ᵁ V).ι ''ᵁ (ρ ⁻¹ᵁ W)).ι hG := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
        simp only [Category.assoc]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc, hεinv,
          Scheme.homOfLE_ι]
    have hr : Set.range ⇑(pullback.lift
          ((((π ⁻¹ᵁ V).ι.isoImage (ρ ⁻¹ᵁ W)).inv ≫ (ρ ∣_ W)) ≫ g ≫ (p ⁻¹ᵁ V).ι)
          ((π ⁻¹ᵁ V).ι ''ᵁ (ρ ⁻¹ᵁ W)).ι hG) =
        Set.range ⇑(pullback.lift ((ρ ∣_ W) ≫ g ≫ (p ⁻¹ᵁ V).ι)
          ((ρ ⁻¹ᵁ W).ι ≫ (π ⁻¹ᵁ V).ι) hG'') := by
      refine Set.Subset.antisymm ?_ ?_
      · rintro _ ⟨x, rfl⟩
        refine ⟨((π ⁻¹ᵁ V).ι.isoImage (ρ ⁻¹ᵁ W)).inv x, ?_⟩
        rw [← Scheme.Hom.comp_apply, hΓeq]
      · rintro _ ⟨y, rfl⟩
        refine ⟨((π ⁻¹ᵁ V).ι.isoImage (ρ ⁻¹ᵁ W)).hom y, ?_⟩
        rw [← Scheme.Hom.comp_apply, ← hΓeq, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [hr, ← hΓ₀snd]
    have hcoe : Set.range ⇑(Γ₀ ≫ ((pullback.snd p π) ⁻¹ᵁ (π ⁻¹ᵁ V)).ι) =
        ⇑((pullback.snd p π) ⁻¹ᵁ (π ⁻¹ᵁ V)).ι '' Set.range ⇑Γ₀ := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext fun x ↦ Scheme.Hom.comp_apply _ _ _)
    rw [hcoe, Set.preimage_image_eq _
      ((pullback.snd p π ⁻¹ᵁ (π ⁻¹ᵁ V)).ι.isOpenEmbedding.injective)]
    exact hclosed₀

end AlgebraicGeometry
