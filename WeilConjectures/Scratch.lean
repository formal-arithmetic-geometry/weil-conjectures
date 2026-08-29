module

public import WeilConjectures.Blowup.EliminationOfIndeterminacy
public import WeilConjectures.Blowup.Extension
public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Transporting an extension along a lift of a blow-up over an open of the base.** -/
theorem exists_extend_of_lift {X X' Y Bl : Scheme.{u}} {p : Y ⟶ X} {π : X' ⟶ X}
    {U V : X.Opens} {f : U.toScheme ⟶ Y}
    {b : Bl ⟶ V.toScheme} {ρ : (π ⁻¹ᵁ V).toScheme ⟶ Bl} (hρ : ρ ≫ b = π ∣_ V)
    {W : Bl.Opens} (hUW : b ⁻¹ᵁ (V.ι ⁻¹ᵁ U) ≤ W)
    {g : W.toScheme ⟶ (p ⁻¹ᵁ V).toScheme} (hg : g ≫ (p ∣_ V) = W.ι ≫ b)
    {fV : (V.ι ⁻¹ᵁ U).toScheme ⟶ (p ⁻¹ᵁ V).toScheme}
    (hfV : fV ≫ (p ⁻¹ᵁ V).ι = (V.ι ∣_ U) ≫ f)
    (hagree : Bl.homOfLE hUW ≫ g = (b ∣_ (V.ι ⁻¹ᵁ U)) ≫ fV)
    (hclosed : IsClosed (Set.range (pullback.lift g W.ι hg))) :
    ∃ (W' : X'.Opens) (_ : W' ≤ π ⁻¹ᵁ V) (G : W'.toScheme ⟶ Y)
      (hG : G ≫ p = W'.ι ≫ π),
      π ⁻¹ᵁ U ⊓ π ⁻¹ᵁ V ≤ W' ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ W'.toScheme) (m : T ⟶ U.toScheme),
          m ≫ U.ι = t ≫ W'.ι ≫ π → t ≫ G = m ≫ f) ∧
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
  have hpt : ∀ y : (π ⁻¹ᵁ V).toScheme, V.ι (b (ρ y)) = π y.1 := by
    intro y
    have h := congr($key y)
    simpa [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] using h
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
  refine ⟨_, hW', _, hG, ?_, ?_, ?_⟩
  -- the inverse image of `U ⊓ V` is contained in the extension locus
  · intro z hz
    have hzV : z ∈ π ⁻¹ᵁ V := hz.2
    have h1 : V.ι (b (ρ (⟨z, hzV⟩ : (π ⁻¹ᵁ V).toScheme))) ∈ U := by
      rw [hpt ⟨z, hzV⟩]
      exact hz.1
    have hmem : (⟨z, hzV⟩ : (π ⁻¹ᵁ V).toScheme) ∈ ρ ⁻¹ᵁ W := hUW h1
    exact (Scheme.Opens.mem_ι_image_iff (x := (⟨z, hzV⟩ : (π ⁻¹ᵁ V).toScheme))).mpr hmem
  -- the extension agrees with `f` wherever both are defined
  · intro T t m hmt
    have hw' : m ≫ U.ι = (t ≫ X'.homOfLE hW' ≫ ρ ≫ b) ≫ V.ι := by
      rw [hmt]
      calc t ≫ ((π ⁻¹ᵁ V).ι ''ᵁ (ρ ⁻¹ᵁ W)).ι ≫ π
          = t ≫ (X'.homOfLE hW' ≫ (π ⁻¹ᵁ V).ι) ≫ π := by
            rw [Scheme.homOfLE_ι]
        _ = t ≫ X'.homOfLE hW' ≫ (ρ ≫ b ≫ V.ι) := by
            rw [key]; simp only [Category.assoc]
        _ = (t ≫ X'.homOfLE hW' ≫ ρ ≫ b) ≫ V.ι := by simp only [Category.assoc]
    obtain ⟨k, hkfst, hksnd⟩ :
        ∃ k : T ⟶ (V.ι ⁻¹ᵁ U).toScheme, k ≫ (V.ι ∣_ U) = m ∧
          k ≫ (V.ι ⁻¹ᵁ U).ι = t ≫ X'.homOfLE hW' ≫ ρ ≫ b :=
      ⟨(isPullback_morphismRestrict V.ι U).lift _ _ hw',
        (isPullback_morphismRestrict V.ι U).lift_fst _ _ hw',
        (isPullback_morphismRestrict V.ι U).lift_snd _ _ hw'⟩
    obtain ⟨c, hcfst, hcsnd⟩ :
        ∃ c : T ⟶ (b ⁻¹ᵁ (V.ι ⁻¹ᵁ U)).toScheme, c ≫ (b ∣_ (V.ι ⁻¹ᵁ U)) = k ∧
          c ≫ (b ⁻¹ᵁ (V.ι ⁻¹ᵁ U)).ι = t ≫ X'.homOfLE hW' ≫ ρ :=
      ⟨(isPullback_morphismRestrict b (V.ι ⁻¹ᵁ U)).lift _ _
          (by rw [hksnd]; simp only [Category.assoc]),
        (isPullback_morphismRestrict b (V.ι ⁻¹ᵁ U)).lift_fst _ _ _,
        (isPullback_morphismRestrict b (V.ι ⁻¹ᵁ U)).lift_snd _ _ _⟩
    have hcW : c ≫ Bl.homOfLE hUW =
        t ≫ (((π ⁻¹ᵁ V).ι.isoImage (ρ ⁻¹ᵁ W)).inv ≫ (ρ ∣_ W)) := by
      rw [← cancel_mono W.ι, Category.assoc, Scheme.homOfLE_ι, hcsnd, Category.assoc, he]
    calc t ≫ ((((π ⁻¹ᵁ V).ι.isoImage (ρ ⁻¹ᵁ W)).inv ≫ (ρ ∣_ W)) ≫ g ≫ (p ⁻¹ᵁ V).ι)
        = (c ≫ Bl.homOfLE hUW) ≫ g ≫ (p ⁻¹ᵁ V).ι := by
          rw [hcW]; simp only [Category.assoc]
      _ = c ≫ ((b ∣_ (V.ι ⁻¹ᵁ U)) ≫ fV) ≫ (p ⁻¹ᵁ V).ι := by
          rw [← hagree]; simp only [Category.assoc]
      _ = k ≫ (fV ≫ (p ⁻¹ᵁ V).ι) := by rw [← hcfst]; simp only [Category.assoc]
      _ = (k ≫ (V.ι ∣_ U)) ≫ f := by rw [hfV]; simp only [Category.assoc]
      _ = m ≫ f := by rw [hkfst]
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

/-- **Conrad's Theorem 2.4, Case 1 over an affine open of a qcqs base**, with the center
extended to the whole base. -/
theorem exists_isAdmissible_isPullback_of_isQuasiAffine
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] {U : X.Opens}
    (hU : IsCompact (U : Set X)) {V : X.Opens} (hV : IsAffineOpen V)
    {Z : Scheme.{u}} [Z.IsQuasiAffine] {q : Z ⟶ V.toScheme} [LocallyOfFiniteType q]
    (fV : (V.ι ⁻¹ᵁ U).toScheme ⟶ Z) (hfV : fV ≫ q = (V.ι ⁻¹ᵁ U).ι) :
    ∃ (C : IsAdmissible X U) (Bl : Scheme.{u}) (b : Bl ⟶ V.toScheme) (h : Bl ⟶ C.I.blowup)
      (_ : IsPullback b h V.ι C.I.blowupMap) (W : Bl.Opens)
      (hUW : b ⁻¹ᵁ (V.ι ⁻¹ᵁ U) ≤ W) (g : W.toScheme ⟶ Z) (hg : g ≫ q = W.ι ≫ b),
      Bl.homOfLE hUW ≫ g = (b ∣_ (V.ι ⁻¹ᵁ U)) ≫ fV ∧
        IsClosed (Set.range (pullback.lift g W.ι hg)) := by
  have : IsAffine V.toScheme := hV
  have : QuasiCompact V.ι := V.quasiCompact_ι hV.isCompact
  have hUV : IsCompact ((V.ι ⁻¹ᵁ U : V.toScheme.Opens) : Set V.toScheme) :=
    V.ι.isCompact_preimage hU
  obtain ⟨B, W, hUW, g, hg, hagree, hclosed, -⟩ :=
    exists_isAdmissible_extend_of_isQuasiAffine hUV fV hfV
  obtain ⟨C, h, -, hpb⟩ :=
    IsAdmissible.exists_extend_of_disjoint hV.isCompact hU B.I B.finiteType B.disjoint_support
  exact ⟨C, _, _, h, hpb, W, hUW, g, hg, hagree, hclosed⟩


set_option maxHeartbeats 1000000 in
/-- **Conrad's Theorem 2.4, Case 2: a quasi-affine target over a qcqs base** (Conrad,
*Deligne's notes on Nagata compactifications*, proof of Theorem 2.4, Case 2, pp. 15–16).
Let `X` be quasi-compact and quasi-separated, `U` a quasi-compact open of `X`,
`p : Y ⟶ X` a separated, quasi-affine morphism locally of finite type, and
`f : U ⟶ Y` a morphism over `X`. Then there are a `U`-admissible blow-up `B` of `X` in
which the inverse image of `U` is scheme-theoretically dense, an open `W` of the blow-up
containing that inverse image, and a morphism `g : W ⟶ Y` over `X` agreeing with `f`
over `U` whose graph `W ⟶ Y ×_X Bl` has closed range.
(Blueprint: `lemma:nagata-conrad-quasi-affine-equal-opens`.) -/
theorem exists_isAdmissible_extend_of_isQuasiAffineHom
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {U : X.Opens} (hU : IsCompact (U : Set X))
    {Y : Scheme.{u}} {p : Y ⟶ X} [IsSeparated p] [LocallyOfFiniteType p]
    [IsQuasiAffineHom p] (f : U.toScheme ⟶ Y) (hf : f ≫ p = U.ι) :
    ∃ (B : IsAdmissible X U) (W : B.I.blowup.Opens) (hUW : B.I.blowupMap ⁻¹ᵁ U ≤ W)
      (g : W.toScheme ⟶ Y) (hg : g ≫ p = W.ι ≫ B.I.blowupMap),
      B.I.blowup.homOfLE hUW ≫ g = (B.I.blowupMap ∣_ U) ≫ f ∧
        IsClosed (Set.range (pullback.lift g W.ι hg)) ∧
        IsSchemeTheoreticallyDominant (B.I.blowupMap ⁻¹ᵁ U).ι := by
  -- Step 1: a finite affine open cover of `X`
  obtain ⟨ιV, _, Vs, hVsaff, hVscov⟩ :
      ∃ (ιV : Type u) (_ : Fintype ιV) (Vs : ιV → X.Opens),
        (∀ i, IsAffineOpen (Vs i)) ∧ ⨆ i, Vs i = ⊤ := by
    refine ⟨X.affineCover.finiteSubcover.I₀, inferInstance,
      fun i ↦ (X.affineCover.finiteSubcover.f i).opensRange, fun i ↦ ?_,
      X.affineCover.finiteSubcover.iSup_opensRange⟩
    have : IsAffine (X.affineCover.finiteSubcover.X i) := by
      rw [Scheme.OpenCover.finiteSubcover_X]; infer_instance
    exact isAffineOpen_opensRange _
  -- Step 2: restrict `f` over each member of the cover
  have hfVex : ∀ i, ∃ fV : ((Vs i).ι ⁻¹ᵁ U).toScheme ⟶ (p ⁻¹ᵁ (Vs i)).toScheme,
      fV ≫ (p ∣_ (Vs i)) = ((Vs i).ι ⁻¹ᵁ U).ι ∧
      fV ≫ (p ⁻¹ᵁ (Vs i)).ι = ((Vs i).ι ∣_ U) ≫ f := by
    intro i
    refine ⟨(isPullback_morphismRestrict p (Vs i)).lift _ _ ?_,
      (isPullback_morphismRestrict p (Vs i)).lift_fst _ _ _,
      (isPullback_morphismRestrict p (Vs i)).lift_snd _ _ _⟩
    rw [Category.assoc, hf, morphismRestrict_ι]
  choose fV hfV₁ hfV₂ using hfVex
  -- Step 3: Case 1 over each member of the cover, with the center extended to `X`
  have hloc : ∀ i, ∃ (C : IsAdmissible X U) (Bl : Scheme.{u}) (b : Bl ⟶ (Vs i).toScheme)
      (h : Bl ⟶ C.I.blowup) (_ : IsPullback b h (Vs i).ι C.I.blowupMap) (W : Bl.Opens)
      (hUW : b ⁻¹ᵁ ((Vs i).ι ⁻¹ᵁ U) ≤ W) (g : W.toScheme ⟶ (p ⁻¹ᵁ (Vs i)).toScheme)
      (hg : g ≫ (p ∣_ (Vs i)) = W.ι ≫ b),
      Bl.homOfLE hUW ≫ g = (b ∣_ ((Vs i).ι ⁻¹ᵁ U)) ≫ fV i ∧
        IsClosed (Set.range (pullback.lift g W.ι hg)) := by
    intro i
    have := (hVsaff i).isQuasiAffine_preimage p
    exact exists_isAdmissible_isPullback_of_isQuasiAffine hU (hVsaff i) (fV i) (hfV₁ i)
  choose Cs Bls bs hs hpbs Ws' hUWs gs hgs hagrees hcloseds using hloc
  -- Step 4: the global center: the product of the local ones times a boundary center
  obtain ⟨K, hKft, hKsupp⟩ := X.exists_finiteType_ideal_coe_support_eq_compl U hU
  have hCsupp : ∀ i, ((Cs i).I.support : Set X) ⊆ (U : Set X)ᶜ := fun i ↦
    Set.subset_compl_iff_disjoint_left.mpr (Cs i).disjoint_support
  have hprod : ∀ s : Finset ιV, (∏ i ∈ s, (Cs i).I).ofFiniteType ∧
      ((∏ i ∈ s, (Cs i).I).support : Set X) ⊆ (U : Set X)ᶜ := by
    intro s
    induction s using Finset.induction with
    | empty =>
        refine ⟨?_, ?_⟩
        · simpa using Scheme.IdealSheafData.ofFiniteType_top
        · simp
    | insert a s ha ih =>
        rw [Finset.prod_insert ha]
        refine ⟨(Cs a).finiteType.mul ih.1, ?_⟩
        rw [Scheme.IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup]
        exact Set.union_subset (hCsupp a) ih.2
  have hJsupp : (((∏ i, (Cs i).I) * K).support : Set X) = (U : Set X)ᶜ := by
    rw [Scheme.IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup, hKsupp]
    exact Set.union_eq_self_of_subset_left (hprod _).2
  obtain ⟨B, hBI⟩ : ∃ B : IsAdmissible X U, B.I = (∏ i, (Cs i).I) * K :=
    ⟨⟨(∏ i, (Cs i).I) * K, (hprod _).1.mul hKft,
      by rw [hJsupp]; exact disjoint_compl_right⟩, rfl⟩
  have hpres : B.I.support.compl = U := by
    apply TopologicalSpace.Opens.ext
    show (B.I.support : Set X)ᶜ = (U : Set X)
    rw [hBI, hJsupp, compl_compl]
  -- properness of the blow-up, and density of the inverse image of `U`
  have hproper := B.isProper_blowupMap
  have : CompactSpace B.I.blowup := QuasiCompact.compactSpace_of_compactSpace B.I.blowupMap
  have : QuasiSeparatedSpace B.I.blowup :=
    quasiSeparatedSpace_of_quasiSeparated B.I.blowupMap
  have hUcompact : IsCompact ((B.I.blowupMap ⁻¹ᵁ U : B.I.blowup.Opens) : Set B.I.blowup) :=
    QuasiCompact.isCompact_preimage (f := B.I.blowupMap) _ U.isOpen hU
  have hqcι : QuasiCompact (B.I.blowupMap ⁻¹ᵁ U).ι :=
    (B.I.blowupMap ⁻¹ᵁ U).quasiCompact_ι hUcompact
  have hdom : IsSchemeTheoreticallyDominant (B.I.blowupMap ⁻¹ᵁ U).ι := by
    have h := B.I.isSchemeTheoreticallyDominant_blowupMap_preimage_compl_support
    rwa [hpres] at h
  have hdense : Dense ((B.I.blowupMap ⁻¹ᵁ U : B.I.blowup.Opens) : Set B.I.blowup) := by
    have h := B.dense_coe_preimage_preservedOpen
    rwa [show B.preservedOpen = U from hpres] at h
  -- Step 5: the canonical lifts to the local blow-ups
  have hlift : ∀ i, ∃ πi : B.I.blowup ⟶ (Cs i).I.blowup,
      πi ≫ (Cs i).I.blowupMap = B.I.blowupMap := by
    intro i
    refine (Cs i).I.exists_lift_blowup ?_
    obtain ⟨R, hR⟩ : (Cs i).I ∣ B.I := by
      rw [hBI]
      exact (Finset.dvd_prod_of_mem (fun j ↦ (Cs j).I) (Finset.mem_univ i)).mul_right K
    have h := B.I.isInvertible_comap_blowupMap
    rw [hR, Scheme.IdealSheafData.comap_mul] at h
    exact Scheme.IdealSheafData.IsInvertible.of_mul_left h
  choose πs hπs using hlift
  have hρex : ∀ i, ∃ ρ : (B.I.blowupMap ⁻¹ᵁ (Vs i)).toScheme ⟶ Bls i,
      ρ ≫ bs i = B.I.blowupMap ∣_ (Vs i) := by
    intro i
    refine ⟨(hpbs i).lift _ ((B.I.blowupMap ⁻¹ᵁ (Vs i)).ι ≫ πs i) ?_,
      (hpbs i).lift_fst _ _ _⟩
    rw [morphismRestrict_ι, Category.assoc, hπs i]
  choose ρs hρs using hρex
  -- Step 6: transport the local extensions to the global blow-up
  have htr := fun i ↦ exists_extend_of_lift (U := U) (f := f) (hρs i) (hUWs i) (hgs i)
    (hfV₂ i) (hagrees i) (hcloseds i)
  choose Ws hWsle Gs hGs hUWs' hagr hclos using htr
  -- Step 7: the extension locus and the glued morphism
  have hUW : B.I.blowupMap ⁻¹ᵁ U ≤ ⨆ i, Ws i := by
    intro z hz
    have hz' : B.I.blowupMap z ∈ (⊤ : X.Opens) := trivial
    rw [← hVscov, TopologicalSpace.Opens.mem_iSup] at hz'
    obtain ⟨i, hi⟩ := hz'
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hUWs' i ⟨hz, hi⟩⟩
  have hmU : ∀ {N : B.I.blowup.Opens} (hNU : N ≤ B.I.blowupMap ⁻¹ᵁ U),
      (B.I.blowup.homOfLE hNU ≫ (B.I.blowupMap ∣_ U)) ≫ U.ι = N.ι ≫ B.I.blowupMap := by
    intro N hNU
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  -- the local extensions agree on the overlaps
  have hoverlap : ∀ i j, B.I.blowup.homOfLE (inf_le_left : Ws i ⊓ Ws j ≤ Ws i) ≫ Gs i =
      B.I.blowup.homOfLE (inf_le_right : Ws i ⊓ Ws j ≤ Ws j) ≫ Gs j := by
    intro i j
    have hdomN : IsSchemeTheoreticallyDominant (B.I.blowup.homOfLE
        (inf_le_right : (B.I.blowupMap ⁻¹ᵁ U) ⊓ (Ws i ⊓ Ws j) ≤ Ws i ⊓ Ws j)) :=
      .of_isPullback (isPullback_opens_inf (B.I.blowupMap ⁻¹ᵁ U) (Ws i ⊓ Ws j))
    refine ext_of_isSchemeTheoreticallyDominant_of_isSeparated p ?_ _ ?_
    · rw [Category.assoc, Category.assoc, hGs i, hGs j, ← Category.assoc, ← Category.assoc,
        Scheme.homOfLE_ι, Scheme.homOfLE_ι]
    · have hNi : (B.I.blowupMap ⁻¹ᵁ U) ⊓ (Ws i ⊓ Ws j) ≤ Ws i :=
        le_trans inf_le_right inf_le_left
      have hNj : (B.I.blowupMap ⁻¹ᵁ U) ⊓ (Ws i ⊓ Ws j) ≤ Ws j :=
        le_trans inf_le_right inf_le_right
      have e1 : B.I.blowup.homOfLE
          (inf_le_right : (B.I.blowupMap ⁻¹ᵁ U) ⊓ (Ws i ⊓ Ws j) ≤ Ws i ⊓ Ws j) ≫
          B.I.blowup.homOfLE (inf_le_left : Ws i ⊓ Ws j ≤ Ws i) =
          B.I.blowup.homOfLE hNi := by
        rw [← cancel_mono (Ws i).ι, Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι,
          Scheme.homOfLE_ι]
      have e2 : B.I.blowup.homOfLE
          (inf_le_right : (B.I.blowupMap ⁻¹ᵁ U) ⊓ (Ws i ⊓ Ws j) ≤ Ws i ⊓ Ws j) ≫
          B.I.blowup.homOfLE (inf_le_right : Ws i ⊓ Ws j ≤ Ws j) =
          B.I.blowup.homOfLE hNj := by
        rw [← cancel_mono (Ws j).ι, Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι,
          Scheme.homOfLE_ι]
      rw [← Category.assoc, ← Category.assoc, e1, e2,
        hagr i (B.I.blowup.homOfLE hNi) _
          (by rw [hmU (inf_le_left : (B.I.blowupMap ⁻¹ᵁ U) ⊓ (Ws i ⊓ Ws j) ≤ _),
            ← Category.assoc, Scheme.homOfLE_ι]),
        hagr j (B.I.blowup.homOfLE hNj) _
          (by rw [hmU (inf_le_left : (B.I.blowupMap ⁻¹ᵁ U) ⊓ (Ws i ⊓ Ws j) ≤ _),
            ← Category.assoc, Scheme.homOfLE_ι])]
  obtain ⟨g, hgi⟩ : ∃ g : (⨆ i, Ws i).toScheme ⟶ Y,
      ∀ i, B.I.blowup.homOfLE (le_iSup Ws i) ≫ g = Gs i :=
    ⟨(Scheme.Opens.iSupOpenCover Ws).glueMorphisms Gs (fun i j ↦
        IsPullback.fst_comp_eq_snd_comp
          (isPullback_opens_inf_le (le_iSup Ws i) (le_iSup Ws j)) (Gs i) (Gs j) (hoverlap i j)),
      fun i ↦ (Scheme.Opens.iSupOpenCover Ws).ι_glueMorphisms _ _ i⟩
  have hgp : g ≫ p = (⨆ i, Ws i).ι ≫ B.I.blowupMap := by
    refine (Scheme.Opens.iSupOpenCover Ws).hom_ext _ _ (fun i ↦ ?_)
    rw [← Category.assoc, ← Category.assoc, hgi i, hGs i, Scheme.homOfLE_ι]
  have hΓi : ∀ i, B.I.blowup.homOfLE (le_iSup Ws i) ≫ pullback.lift g (⨆ i, Ws i).ι hgp =
      pullback.lift (Gs i) (Ws i).ι (hGs i) := by
    intro i
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hgi i]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Scheme.homOfLE_ι]
  refine ⟨B, ⨆ i, Ws i, hUW, g, hgp, ?_, ?_, hdom⟩
  -- the glued extension agrees with `f` over `U`
  · have hcov' : TopologicalSpace.IsOpenCover
        (fun i ↦ (B.I.blowupMap ⁻¹ᵁ U).ι ⁻¹ᵁ Ws i) := by
      refine TopologicalSpace.IsOpenCover.mk (TopologicalSpace.Opens.ext ?_)
      refine Set.eq_univ_of_forall (fun x ↦ ?_)
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hUW x.2)
      exact TopologicalSpace.Opens.coe_iSup _ ▸ Set.mem_iUnion.mpr ⟨i, hi⟩
    refine ((B.I.blowupMap ⁻¹ᵁ U).toScheme.openCoverOfIsOpenCover _ hcov').hom_ext _ _
      (fun i ↦ ?_)
    have hMι : ((B.I.blowupMap ⁻¹ᵁ U).ι ⁻¹ᵁ Ws i).ι ≫ B.I.blowup.homOfLE hUW =
        ((B.I.blowupMap ⁻¹ᵁ U).ι ∣_ (Ws i)) ≫ B.I.blowup.homOfLE (le_iSup Ws i) := by
      rw [← cancel_mono (⨆ i, Ws i).ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι,
        Scheme.homOfLE_ι, morphismRestrict_ι]
    rw [← Category.assoc, hMι, Category.assoc, hgi i,
      hagr i ((B.I.blowupMap ⁻¹ᵁ U).ι ∣_ (Ws i))
        (((B.I.blowupMap ⁻¹ᵁ U).ι ⁻¹ᵁ Ws i).ι ≫ (B.I.blowupMap ∣_ U)) ?_]
    · simp only [Category.assoc]
    · rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, morphismRestrict_ι]
      simp only [Category.assoc]
  -- the graph of the glued extension is closed
  · -- the range of the glued graph is the union of the ranges of the local graphs
    have hrangeU : Set.range ⇑(pullback.lift g (⨆ i, Ws i).ι hgp) =
        ⋃ i, Set.range ⇑(pullback.lift (Gs i) (Ws i).ι (hGs i)) := by
      refine Set.Subset.antisymm ?_ (Set.iUnion_subset (fun i ↦ ?_))
      · rintro _ ⟨x, rfl⟩
        obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp x.2
        refine Set.mem_iUnion.mpr ⟨i, ⟨⟨x.1, hi⟩, ?_⟩⟩
        rw [← hΓi i, Scheme.Hom.comp_apply]
        congr 1
        exact Subtype.ext (Scheme.homOfLE_apply _ _)
      · rw [← hΓi i]
        rintro _ ⟨y, rfl⟩
        exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
    -- the local graphs are compatible over the parts of the base where both are defined
    have hstepG : ∀ i j,
        ⇑((pullback.snd p B.I.blowupMap) ⁻¹ᵁ (B.I.blowupMap ⁻¹ᵁ Vs i)).ι ⁻¹'
            Set.range ⇑(pullback.lift (Gs j) (Ws j).ι (hGs j)) ⊆
          ⇑((pullback.snd p B.I.blowupMap) ⁻¹ᵁ (B.I.blowupMap ⁻¹ᵁ Vs i)).ι ⁻¹'
            Set.range ⇑(pullback.lift (Gs i) (Ws i).ι (hGs i)) := by
      intro i j
      have hNi : ((B.I.blowupMap ⁻¹ᵁ U) ⊓ (B.I.blowupMap ⁻¹ᵁ Vs i)) ⊓ Ws j ≤ Ws i :=
        le_trans inf_le_left (hUWs' i)
      have hNj : ((B.I.blowupMap ⁻¹ᵁ U) ⊓ (B.I.blowupMap ⁻¹ᵁ Vs i)) ⊓ Ws j ≤ Ws j :=
        inf_le_right
      have hNU : ((B.I.blowupMap ⁻¹ᵁ U) ⊓ (B.I.blowupMap ⁻¹ᵁ Vs i)) ⊓ Ws j ≤
          B.I.blowupMap ⁻¹ᵁ U := le_trans inf_le_left inf_le_left
      -- the two local graphs agree over the overlap
      have heq : B.I.blowup.homOfLE hNi ≫ pullback.lift (Gs i) (Ws i).ι (hGs i) =
          B.I.blowup.homOfLE hNj ≫ pullback.lift (Gs j) (Ws j).ι (hGs j) := by
        apply pullback.hom_ext
        · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst,
            hagr i (B.I.blowup.homOfLE hNi) _
              (by rw [hmU hNU, ← Category.assoc, Scheme.homOfLE_ι]),
            hagr j (B.I.blowup.homOfLE hNj) _
              (by rw [hmU hNU, ← Category.assoc, Scheme.homOfLE_ι])]
        · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd,
            Scheme.homOfLE_ι, Scheme.homOfLE_ι]
      -- the graph over the overlap lands in the range of the `i`-th local graph
      have hDsub : Set.range ⇑(B.I.blowup.homOfLE hNj ≫
            pullback.lift (Gs j) (Ws j).ι (hGs j)) ⊆
          Set.range ⇑(pullback.lift (Gs i) (Ws i).ι (hGs i)) := by
        rw [← heq]
        rintro _ ⟨x, rfl⟩
        exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
      -- the inverse image of `U` is dense in the `j`-th extension locus
      have hRj : Dense (⇑(Ws j).ι ⁻¹' ((B.I.blowupMap ⁻¹ᵁ U : B.I.blowup.Opens) :
          Set B.I.blowup)) := hdense.preimage (Ws j).ι.isOpenEmbedding.isOpenMap
      have hMrange : Set.range ⇑(B.I.blowup.homOfLE hNj) =
          (((Ws j).ι ⁻¹ᵁ (B.I.blowupMap ⁻¹ᵁ Vs i) : (Ws j).toScheme.Opens) :
              Set (Ws j).toScheme) ∩
            (⇑(Ws j).ι ⁻¹' ((B.I.blowupMap ⁻¹ᵁ U : B.I.blowup.Opens) : Set B.I.blowup)) := by
        ext y
        rw [show Set.range ⇑(B.I.blowup.homOfLE hNj) =
            ((B.I.blowup.homOfLE hNj).opensRange : Set (Ws j).toScheme) from rfl,
          TopologicalSpace.Opens.mem_coe, mem_opensRange_homOfLE hNj]
        exact ⟨fun h ↦ ⟨h.1.2, h.1.1⟩, fun h ↦ ⟨⟨h.2, h.1⟩, y.2⟩⟩
      intro z hz
      obtain ⟨y, hy⟩ := hz
      -- `y` lies over `Vs i`
      have hyV : y ∈ ((Ws j).ι ⁻¹ᵁ (B.I.blowupMap ⁻¹ᵁ Vs i) : (Ws j).toScheme.Opens) := by
        have h1 : (pullback.snd p B.I.blowupMap)
            (((pullback.snd p B.I.blowupMap) ⁻¹ᵁ (B.I.blowupMap ⁻¹ᵁ Vs i)).ι z) ∈
            B.I.blowupMap ⁻¹ᵁ Vs i := z.2
        rw [← hy, ← Scheme.Hom.comp_apply, pullback.lift_snd] at h1
        exact h1
      -- `y` is in the closure of the overlap
      have hyclos : y ∈ closure (Set.range ⇑(B.I.blowup.homOfLE hNj)) := by
        rw [hMrange]
        exact hRj.open_subset_closure_inter
          ((Ws j).ι ⁻¹ᵁ (B.I.blowupMap ⁻¹ᵁ Vs i)).isOpen hyV
      have himg : Set.range ⇑(B.I.blowup.homOfLE hNj ≫
            pullback.lift (Gs j) (Ws j).ι (hGs j)) =
          ⇑(pullback.lift (Gs j) (Ws j).ι (hGs j)) ''
            Set.range ⇑(B.I.blowup.homOfLE hNj) := by
        rw [← Set.range_comp]
        exact congrArg Set.range (funext fun x ↦ Scheme.Hom.comp_apply _ _ _)
      have hzclos : ((pullback.snd p B.I.blowupMap) ⁻¹ᵁ (B.I.blowupMap ⁻¹ᵁ Vs i)).ι z ∈
          closure (Set.range ⇑(B.I.blowup.homOfLE hNj ≫
            pullback.lift (Gs j) (Ws j).ι (hGs j))) := by
        rw [← hy, himg]
        exact (pullback.lift (Gs j) (Ws j).ι (hGs j)).continuous.image_closure ⟨y, hyclos, rfl⟩
      have hfin : z ∈ closure (⇑((pullback.snd p B.I.blowupMap) ⁻¹ᵁ
          (B.I.blowupMap ⁻¹ᵁ Vs i)).ι ⁻¹' Set.range ⇑(pullback.lift (Gs i) (Ws i).ι (hGs i))) :=
        closure_mono (Set.preimage_mono hDsub)
          (((pullback.snd p B.I.blowupMap) ⁻¹ᵁ
            (B.I.blowupMap ⁻¹ᵁ Vs i)).ι.isOpenEmbedding.isOpenMap.preimage_closure_subset_closure_preimage
              hzclos)
      rwa [(hclos i).closure_eq] at hfin
    -- assemble
    have hOcov : TopologicalSpace.IsOpenCover
        (fun i ↦ (pullback.snd p B.I.blowupMap) ⁻¹ᵁ (B.I.blowupMap ⁻¹ᵁ Vs i)) := by
      refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr fun z _ ↦ ?_)
      have hz : B.I.blowupMap ((pullback.snd p B.I.blowupMap) z) ∈ (⊤ : X.Opens) := trivial
      rw [← hVscov, TopologicalSpace.Opens.mem_iSup] at hz
      obtain ⟨i, hi⟩ := hz
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
    rw [hOcov.isClosed_iff_coe_preimage]
    intro i
    rw [hrangeU, Set.preimage_iUnion,
      (Set.iUnion_subset (hstepG i)).antisymm (Set.subset_iUnion _ i)]
    exact hclos i

end AlgebraicGeometry
