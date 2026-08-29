module

public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import WeilConjectures.Blowup.EliminationOfIndeterminacy
public import WeilConjectures.Blowup.QuasiAffineGeneralReduction

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- A qcqs scheme covered by quasi-affine basic opens of global sections is quasi-affine. -/
lemma Scheme.IsQuasiAffine.of_forall_exists_isQuasiAffine_basicOpen (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (H : ∀ x : X, ∃ r : Γ(X, ⊤), (X.basicOpen r).toScheme.IsQuasiAffine ∧ x ∈ X.basicOpen r) :
    X.IsQuasiAffine := by
  suffices IsOpenImmersion X.toSpecΓ by constructor
  refine IsZariskiLocalAtTarget.of_forall_source_exists_preimage _ fun x ↦ ?_
  obtain ⟨r, hr, hxr⟩ := H x
  refine ⟨PrimeSpectrum.basicOpen r, (X.toSpecΓ_preimage_basicOpen r).ge hxr, ?_⟩
  suffices IsOpenImmersion ((X.basicOpen r).ι ≫ X.toSpecΓ) by
    convert! this <;> rw [Scheme.toSpecΓ_preimage_basicOpen]
  rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top]
  have := isLocalization_basicOpen_of_qcqs (X := X) isCompact_univ isQuasiSeparated_univ r
  have : IsOpenImmersion (X.basicOpen r).toSpecΓ := by
    delta Scheme.Opens.toSpecΓ
    infer_instance
  exact MorphismProperty.comp_mem _ _ _ inferInstance (.of_isLocalization r)

/-- The fibre product of a quasi-affine scheme and an affine scheme over an affine scheme is
quasi-affine. -/
lemma Scheme.IsQuasiAffine.pullback_of_isAffine {A B C : Scheme.{u}}
    [A.IsQuasiAffine] [IsAffine B] [IsAffine C] (α : A ⟶ B) (β : C ⟶ B) :
    (pullback α β).IsQuasiAffine := by
  -- `α` factors through the affine hull of `A`, by an affine morphism
  obtain ⟨γ, hγ, rfl⟩ : ∃ γ : Spec Γ(A, ⊤) ⟶ B, IsAffineHom γ ∧ A.toSpecΓ ≫ γ = α :=
    ⟨Spec.map α.appTop ≫ (Scheme.isoSpec B).inv, inferInstance, by
      rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
        show B.toSpecΓ = (Scheme.isoSpec B).hom from rfl, Iso.hom_inv_id, Category.comp_id]⟩
  haveI : IsAffine (pullback γ β) := isAffine_of_isAffineHom (pullback.snd γ β)
  haveI : QuasiCompact (A.toSpecΓ ≫ γ) := quasiCompact_of_compactSpace _
  haveI := QuasiCompact.compactSpace_of_compactSpace (pullback.snd (A.toSpecΓ ≫ γ) β)
  haveI : IsOpenImmersion (pullback.map (A.toSpecΓ ≫ γ) β γ β A.toSpecΓ (𝟙 C) (𝟙 B)
      (by simp) (by simp)) :=
    MorphismProperty.of_isPullback (isPullback_pullback_map_left A.toSpecΓ γ β) inferInstance
  exact .of_isImmersion (pullback.map (A.toSpecΓ ≫ γ) β γ β A.toSpecΓ (𝟙 C) (𝟙 B)
    (by simp) (by simp))

/-- The base change of a quasi-affine morphism along a morphism from an affine scheme has
quasi-affine source. -/
theorem Scheme.IsQuasiAffine.of_isPullback_of_isAffine {S Y W T : Scheme.{u}} {p : Y ⟶ S}
    [IsQuasiAffineHom p] [QuasiCompact p] [QuasiSeparated p] [IsAffine W]
    {h : W ⟶ S} {u : T ⟶ Y} {q : T ⟶ W} (H : IsPullback u q p h) : T.IsQuasiAffine := by
  haveI : QuasiCompact q := MorphismProperty.of_isPullback H ‹QuasiCompact p›
  haveI : QuasiSeparated q := MorphismProperty.of_isPullback H ‹QuasiSeparated p›
  haveI := QuasiCompact.compactSpace_of_compactSpace q
  haveI := quasiSeparatedSpace_of_quasiSeparated q
  refine .of_forall_exists_isQuasiAffine_basicOpen _ fun t ↦ ?_
  -- an affine open `V` of `S` around the image of `t`
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := S) (x := p (u t)) (U := ⊤) trivial
  -- a basic open `O` of the affine `W` around the image of `t`, inside `h ⁻¹ V`
  have hb : h.base (q.base t) = p.base (u.base t) := by
    have hw : (q ≫ h).base t = (u ≫ p).base t := by rw [H.w]
    simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] using hw
  have htV : q t ∈ h ⁻¹ᵁ V := by
    change h.base (q.base t) ∈ V
    rw [hb]
    exact hxV
  obtain ⟨_, ⟨r₀, rfl⟩, htr, hrV⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.isBasis_basicOpen W) htV
  refine ⟨q.appTop r₀, ?_, by rwa [← Scheme.preimage_basicOpen_top]⟩
  rw [← Scheme.preimage_basicOpen_top]
  -- the preimage of `O` in `T` is the fibre product of `p ⁻¹ V` and `O` over `V`
  haveI : IsAffine (W.basicOpen r₀).toScheme := (isAffineOpen_top W).basicOpen r₀
  haveI : IsAffine V.toScheme := hV
  haveI : (p ⁻¹ᵁ V).toScheme.IsQuasiAffine := hV.isQuasiAffine_preimage p
  set O : W.Opens := W.basicOpen r₀ with hO
  set k : O.toScheme ⟶ V.toScheme := W.homOfLE hrV ≫ (h ∣_ V) with hk
  have hkV : k ≫ V.ι = O.ι ≫ h := by
    rw [hk, Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  have hbig : IsPullback (q ∣_ O) ((q ⁻¹ᵁ O).ι ≫ u) (O.ι ≫ h) p :=
    (isPullback_morphismRestrict q O).paste_vert H.flip
  have hmr := isPullback_morphismRestrict p V
  have hw : (q ∣_ O ≫ k) ≫ V.ι = ((q ⁻¹ᵁ O).ι ≫ u) ≫ p := by
    rw [Category.assoc, hkV, ← Category.assoc, morphismRestrict_ι, Category.assoc,
      Category.assoc, H.w]
  set a : (q ⁻¹ᵁ O).toScheme ⟶ (p ⁻¹ᵁ V).toScheme := hmr.lift (q ∣_ O ≫ k) ((q ⁻¹ᵁ O).ι ≫ u) hw
    with ha
  have hsq : IsPullback (q ∣_ O) a k (p ∣_ V) := by
    refine IsPullback.of_bot ?_ ?_ hmr
    · rw [ha, hmr.lift_snd, hkV]
      exact hbig
    · rw [ha, hmr.lift_fst]
  haveI : (pullback (p ∣_ V) k).IsQuasiAffine :=
    Scheme.IsQuasiAffine.pullback_of_isAffine (p ∣_ V) k
  exact .of_isIso hsq.flip.isoPullback.hom


/-- Quasi-affine morphisms are stable under base change. -/
theorem IsQuasiAffineHom.of_isPullback {S Y Z T : Scheme.{u}} {p : Y ⟶ S} {g : Z ⟶ S}
    [IsQuasiAffineHom p] [QuasiCompact p] [QuasiSeparated p]
    {u : T ⟶ Y} {q : T ⟶ Z} (H : IsPullback u q p g) : IsQuasiAffineHom q where
  isQuasiAffine_preimage W hW := by
    haveI : IsAffine W.toScheme := hW
    exact Scheme.IsQuasiAffine.of_isPullback_of_isAffine
      ((isPullback_morphismRestrict q W).paste_vert H.flip).flip

instance {S Y Z : Scheme.{u}} (p : Y ⟶ S) (g : Z ⟶ S)
    [IsQuasiAffineHom p] [QuasiCompact p] [QuasiSeparated p] :
    IsQuasiAffineHom (pullback.snd p g) :=
  .of_isPullback (IsPullback.of_hasPullback p g)


section Case3

variable {X : Scheme.{u}}

theorem exists_isAdmissible_extend_of_isQuasiAffineHom_of_le
    [CompactSpace X] [QuasiSeparatedSpace X] {U V : X.Opens} (hUV : U ≤ V)
    (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    {Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y] {p : Y ⟶ X}
    [IsSeparated p] [LocallyOfFiniteType p] [IsQuasiAffineHom p]
    (f : U.toScheme ⟶ Y) (hf : f ≫ p = U.ι)
    (hfc : IsClosed ((p ⁻¹ᵁ V).ι ⁻¹' Set.range f)) :
    ∃ (B : IsAdmissible X V) (W : B.I.blowup.Opens) (hUW : B.I.blowupMap ⁻¹ᵁ U ≤ W)
      (g : W.toScheme ⟶ Y) (hg : g ≫ p = W.ι ≫ B.I.blowupMap),
      B.I.blowup.homOfLE hUW ≫ g = (B.I.blowupMap ∣_ U) ≫ f ∧
        IsClosed (Set.range (pullback.lift g W.ι hg)) := by
  classical
  haveI : QuasiCompact p := quasiCompact_of_compactSpace p
  -- Step 1: the disjointness blow-up
  obtain ⟨B₁, hB₁⟩ := exists_isAdmissible_disjoint_closure_range_of_le hUV hU hV f hf hfc
  set X₁ : Scheme.{u} := B₁.I.blowup with hX₁
  set π₁ : X₁ ⟶ X := B₁.I.blowupMap with hπ₁
  haveI : IsProper π₁ := B₁.isProper_blowupMap
  haveI : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace π₁
  haveI : QuasiSeparatedSpace X₁ := quasiSeparatedSpace_of_quasiSeparated π₁
  -- the base change of `p` along the blow-up
  obtain ⟨Y₁, r, p₁, hpb₁⟩ :
      ∃ (Y₁ : Scheme.{u}) (r : Y₁ ⟶ Y) (p₁ : Y₁ ⟶ X₁), IsPullback r p₁ p π₁ :=
    ⟨_, _, _, IsPullback.of_hasPullback p π₁⟩
  haveI : IsSeparated p₁ := MorphismProperty.of_isPullback hpb₁ ‹IsSeparated p›
  haveI : LocallyOfFiniteType p₁ := MorphismProperty.of_isPullback hpb₁ ‹LocallyOfFiniteType p›
  haveI : QuasiCompact p₁ := MorphismProperty.of_isPullback hpb₁ ‹QuasiCompact p›
  haveI : IsQuasiAffineHom p₁ := .of_isPullback hpb₁
  haveI : CompactSpace Y₁ := QuasiCompact.compactSpace_of_compactSpace p₁
  haveI : QuasiSeparatedSpace Y₁ := quasiSeparatedSpace_of_quasiSeparated p₁
  -- the section over the preimage of `U`
  have hfcond : ((π₁ ∣_ U) ≫ f) ≫ p = (π₁ ⁻¹ᵁ U).ι ≫ π₁ := by
    rw [Category.assoc, hf, morphismRestrict_ι]
  set f₁ : (π₁ ⁻¹ᵁ U).toScheme ⟶ Y₁ := hpb₁.lift ((π₁ ∣_ U) ≫ f) (π₁ ⁻¹ᵁ U).ι hfcond with hf₁
  have hf₁r : f₁ ≫ r = (π₁ ∣_ U) ≫ f := hpb₁.lift_fst _ _ _
  have hf₁p : f₁ ≫ p₁ = (π₁ ⁻¹ᵁ U).ι := hpb₁.lift_snd _ _ _
  have hU₁c : IsCompact ((π₁ ⁻¹ᵁ U : X₁.Opens) : Set X₁) := π₁.isCompact_preimage hU
  have hV₁c : IsCompact ((π₁ ⁻¹ᵁ V : X₁.Opens) : Set X₁) := π₁.isCompact_preimage hV
  haveI : CompactSpace (π₁ ⁻¹ᵁ U).toScheme := isCompact_iff_compactSpace.mp hU₁c
  haveI : QuasiCompact f₁ := quasiCompact_of_compactSpace f₁
  have hdisj := hB₁ hpb₁.w hf₁r
  -- Step 2: a quasi-compact open of the blow-up meeting the preimage of `V` in that of `U`
  have hScpt : IsCompact (p₁ '' closure (Set.range f₁)) :=
    (isClosed_closure.isCompact).image p₁.continuous
  have hSdisj : Disjoint (p₁ '' closure (Set.range f₁))
      (closure (((π₁ ⁻¹ᵁ V : X₁.Opens) : Set X₁) \ ((π₁ ⁻¹ᵁ U : X₁.Opens) : Set X₁))) := by
    rw [Set.disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ hmem
    exact Set.disjoint_left.mp hdisj hy hmem
  obtain ⟨X₀, hX₀c, hSX₀, hU₁X₀, hX₀V⟩ :=
    exists_isCompact_opens_inf_eq_of_disjoint_closure_sdiff
      (π₁.preimage_mono hUV) hU₁c hScpt hSdisj
  -- Step 3: Case 2 over the smaller base `X₀`
  haveI : CompactSpace X₀.toScheme := isCompact_iff_compactSpace.mp hX₀c
  haveI : QuasiSeparatedSpace X₀.toScheme := quasiSeparatedSpace_of_quasiSeparated X₀.ι
  haveI : QuasiCompact X₀.ι := quasiCompact_of_compactSpace X₀.ι
  set U₀ : X₀.toScheme.Opens := X₀.ι ⁻¹ᵁ (π₁ ⁻¹ᵁ U) with hU₀
  have hU₀c : IsCompact ((U₀ : X₀.toScheme.Opens) : Set X₀.toScheme) :=
    X₀.ι.isCompact_preimage hU₁c
  have hf₀cond : U₀.ι ≫ X₀.ι = ((X₀.ι ∣_ (π₁ ⁻¹ᵁ U)) ≫ f₁) ≫ p₁ := by
    rw [Category.assoc, hf₁p, morphismRestrict_ι]
  set f₀ : U₀.toScheme ⟶ (p₁ ⁻¹ᵁ X₀).toScheme :=
    (isPullback_morphismRestrict p₁ X₀).lift U₀.ι ((X₀.ι ∣_ (π₁ ⁻¹ᵁ U)) ≫ f₁) hf₀cond with hf₀
  have hf₀q : f₀ ≫ (p₁ ∣_ X₀) = U₀.ι := (isPullback_morphismRestrict p₁ X₀).lift_fst _ _ _
  have hf₀ι : f₀ ≫ (p₁ ⁻¹ᵁ X₀).ι = (X₀.ι ∣_ (π₁ ⁻¹ᵁ U)) ≫ f₁ :=
    (isPullback_morphismRestrict p₁ X₀).lift_snd _ _ _
  obtain ⟨C, W₀, hUW₀, g₀, hg₀, hagree₀, hclosed₀, hdom₀⟩ :=
    exists_isAdmissible_extend_of_isQuasiAffineHom hU₀c f₀ hf₀q
  -- Step 4: extend the centre from `X₀` to the blow-up `X₁`
  have hV₀ : X₀.ι ⁻¹ᵁ (π₁ ⁻¹ᵁ V) = U₀ := by
    refine le_antisymm (fun x hx ↦ ?_) (X₀.ι.preimage_mono (π₁.preimage_mono hUV))
    have h1 : X₀.ι x ∈ (X₀ : Set X₁) := by
      rw [← Scheme.Opens.range_ι]
      exact Set.mem_range_self x
    have h2 : X₀.ι x ∈ ((X₀ ⊓ (π₁ ⁻¹ᵁ V) : X₁.Opens) : Set X₁) := ⟨h1, hx⟩
    rw [hX₀V] at h2
    exact h2
  obtain ⟨D, hmap, hmapw, hpbD⟩ :=
    IsAdmissible.exists_extend_of_disjoint (X := X₁) (A := X₀) (B := π₁ ⁻¹ᵁ V) hX₀c hV₁c
      C.I C.finiteType (by rw [hV₀]; exact C.disjoint_support)
  set ρiso : (D.I.blowupMap ⁻¹ᵁ X₀).toScheme ≅ C.I.blowup :=
    (isPullback_morphismRestrict D.I.blowupMap X₀).isoIsPullback _ _ hpbD
    with hρisodef
  have hρ : ρiso.hom ≫ C.I.blowupMap = D.I.blowupMap ∣_ X₀ :=
    (isPullback_morphismRestrict D.I.blowupMap X₀).isoIsPullback_hom_fst _ _ hpbD
  obtain ⟨W', hW'X₀, G, hG, hUW', hagreeG, hclosedG⟩ :=
    exists_extend_of_lift (p := p₁) (π := D.I.blowupMap) (U := π₁ ⁻¹ᵁ U) (V := X₀) (f := f₁)
      (b := C.I.blowupMap) (ρ := ρiso.hom) hρ hUW₀ hg₀ hf₀ι hagree₀ hclosed₀
  -- Step 5: compose the two admissible blow-ups
  obtain ⟨K, hKft, hKdisj, iso, hiso⟩ := IsAdmissible.exists_comp B₁ D
  have hUW'' : D.I.blowupMap ⁻¹ᵁ (π₁ ⁻¹ᵁ U) ≤ W' :=
    le_trans (le_inf le_rfl (D.I.blowupMap.preimage_mono hU₁X₀)) hUW'
  have hKbm : iso.inv ≫ D.I.blowupMap ≫ π₁ = K.blowupMap := by
    rw [← hiso, ← Category.assoc, iso.inv_hom_id, Category.id_comp]
  have hUW : K.blowupMap ⁻¹ᵁ U ≤ iso.inv ⁻¹ᵁ W' := by
    rw [← hKbm]
    simp only [Scheme.Hom.comp_preimage]
    exact iso.inv.preimage_mono hUW''
  have hg : ((iso.inv ∣_ W') ≫ G ≫ r) ≫ p = (iso.inv ⁻¹ᵁ W').ι ≫ K.blowupMap := by
    simp only [Category.assoc]
    rw [hpb₁.w, ← Category.assoc G, hG]
    simp only [Category.assoc]
    rw [← Category.assoc (iso.inv ∣_ W'), morphismRestrict_ι]
    simp only [Category.assoc]
    rw [hKbm]
  refine ⟨⟨K, hKft, hKdisj⟩, iso.inv ⁻¹ᵁ W', hUW, (iso.inv ∣_ W') ≫ G ≫ r, hg, ?_, ?_⟩
  · -- the extension agrees with `f` over `U`
    have hmcond : (K.blowupMap ∣_ U) ≫ U.ι =
        ((K.blowup.homOfLE hUW ≫ (iso.inv ∣_ W')) ≫ W'.ι ≫ D.I.blowupMap) ≫ π₁ := by
      rw [morphismRestrict_ι]
      simp only [Category.assoc]
      rw [← Category.assoc (iso.inv ∣_ W'), morphismRestrict_ι]
      simp only [Category.assoc]
      rw [hKbm, ← Category.assoc, Scheme.homOfLE_ι]
    have hm1 := (isPullback_morphismRestrict π₁ U).lift_fst (K.blowupMap ∣_ U)
      ((K.blowup.homOfLE hUW ≫ (iso.inv ∣_ W')) ≫ W'.ι ≫ D.I.blowupMap) hmcond
    have hm2 := (isPullback_morphismRestrict π₁ U).lift_snd (K.blowupMap ∣_ U)
      ((K.blowup.homOfLE hUW ≫ (iso.inv ∣_ W')) ≫ W'.ι ≫ D.I.blowupMap) hmcond
    have hagr := hagreeG (K.blowup.homOfLE hUW ≫ (iso.inv ∣_ W')) _ hm2
    calc K.blowup.homOfLE hUW ≫ (iso.inv ∣_ W') ≫ G ≫ r
        = ((K.blowup.homOfLE hUW ≫ (iso.inv ∣_ W')) ≫ G) ≫ r := by
          simp only [Category.assoc]
      _ = _ ≫ f := by rw [hagr, Category.assoc, hf₁r, ← Category.assoc, hm1]
  · sorry

end Case3


end AlgebraicGeometry
