module

public import WeilConjectures.Blowup.EliminationOfIndeterminacy

@[expose] public section

noncomputable section
universe u
open CategoryTheory Limits HomogeneousLocalization
namespace AlgebraicGeometry
open AffineSpace


namespace CategoryTheory

-- placeholder

/-- Composing both legs of a commutative square with a monomorphism does not change whether
it is a pullback square. -/
lemma _root_.CategoryTheory.IsPullback.comp_mono_iff {C : Type*} [Category C] {P S T Z Z' : C} {p : P ⟶ S}
    {q : P ⟶ T} {α : S ⟶ Z} {β : T ⟶ Z} (j : Z ⟶ Z') [Mono j] :
    IsPullback p q (α ≫ j) (β ≫ j) ↔ IsPullback p q α β := by
  have hw : ∀ {D : C} (a : D ⟶ S) (b : D ⟶ T), a ≫ α ≫ j = b ≫ β ≫ j ↔ a ≫ α = b ≫ β := by
    intro D a b
    rw [← Category.assoc, ← Category.assoc, cancel_mono]
  constructor
  · intro h
    refine IsPullback.of_isLimit' ⟨(hw p q).mp h.w⟩
      (Limits.PullbackCone.IsLimit.mk _ (fun s ↦ h.lift s.fst s.snd
        ((hw s.fst s.snd).mpr s.condition)) (fun s ↦ h.lift_fst _ _ _)
        (fun s ↦ h.lift_snd _ _ _) fun s m h₁ h₂ ↦ h.hom_ext ?_ ?_)
    · rw [h₁, h.lift_fst]
    · rw [h₂, h.lift_snd]
  · intro h
    refine IsPullback.of_isLimit' ⟨(hw p q).mpr h.w⟩
      (Limits.PullbackCone.IsLimit.mk _ (fun s ↦ h.lift s.fst s.snd
        ((hw s.fst s.snd).mp s.condition)) (fun s ↦ h.lift_fst _ _ _)
        (fun s ↦ h.lift_snd _ _ _) fun s m h₁ h₂ ↦ h.hom_ext ?_ ?_)
    · rw [h₁, h.lift_fst]
    · rw [h₂, h.lift_snd]

/-- Two morphisms out of the two legs of a pullback square which agree on a scheme realizing
the square agree on the chosen pullback. -/
lemma _root_.CategoryTheory.IsPullback.fst_comp_eq_snd_comp {C : Type*} [Category C]
    {P S T Z : C} {p : P ⟶ S} {q : P ⟶ T} {α : S ⟶ Z} {β : T ⟶ Z} (h : IsPullback p q α β)
    [Limits.HasPullback α β] {Y : C} (v : S ⟶ Y) (w : T ⟶ Y) (hvw : p ≫ v = q ≫ w) :
    Limits.pullback.fst α β ≫ v = Limits.pullback.snd α β ≫ w := by
  rw [← cancel_epi h.isoPullback.hom, ← Category.assoc, ← Category.assoc,
    h.isoPullback_hom_fst, h.isoPullback_hom_snd, hvw]

end CategoryTheory

/-- The `j`-th coordinate of a morphism to relative affine space precomposed with `m` is the
pullback along `m` of the `j`-th defining section. -/
lemma AffineSpace.comp_homOfVector_appTop_coord {n : Type u} {S T Y : Scheme.{u}} (m : T ⟶ Y)
    (h : Y ⟶ S) (v : n → Γ(Y, ⊤)) (j : n) :
    (m ≫ AffineSpace.homOfVector h v).appTop (AffineSpace.coord S j) = m.appTop (v j) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.homOfVector_appTop_coord]

/-- Two morphisms from `Spec T` to a relative affine space, given by ring maps out of `R` and
`S` together with defining vectors of sections of `R` and `S`, agree as soon as the underlying
morphisms to the base agree and the defining sections have the same image in `T`. -/
lemma AffineSpace.specMap_comp_homOfVector_eq {X : Scheme.{u}} {σ : Type u}
    {R S T : CommRingCat.{u}} (φ : R ⟶ T) (ψ : S ⟶ T) (pR : Spec R ⟶ X) (pS : Spec S ⟶ X)
    (hp : Spec.map φ ≫ pR = Spec.map ψ ≫ pS) (vR : σ → R) (vS : σ → S)
    (hv : ∀ j, φ (vR j) = ψ (vS j)) :
    Spec.map φ ≫ AffineSpace.homOfVector pR (fun j ↦ (Scheme.ΓSpecIso R).inv (vR j)) =
      Spec.map ψ ≫ AffineSpace.homOfVector pS (fun j ↦ (Scheme.ΓSpecIso S).inv (vS j)) := by
  refine AffineSpace.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, AffineSpace.homOfVector_over,
      AffineSpace.homOfVector_over, hp]
  · intro j
    rw [AffineSpace.comp_homOfVector_appTop_coord, AffineSpace.comp_homOfVector_appTop_coord,
      ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      ← Scheme.ΓSpecIso_inv_naturality, ← Scheme.ΓSpecIso_inv_naturality,
      CommRingCat.comp_apply, CommRingCat.comp_apply, hv j]

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- The product of two slopes on the same chart depends only on the product of the
numerators. -/
lemma AffineBlowup.awaySlope_mul_awaySlope {a b b' d d' : A} (ha : a ∈ I) (hb : b ∈ I)
    (hb' : b' ∈ I) (hd : d ∈ I) (hd' : d' ∈ I) (h : b * b' = d * d') :
    AffineBlowup.awaySlope I ha hb * AffineBlowup.awaySlope I ha hb' =
      AffineBlowup.awaySlope I ha hd * AffineBlowup.awaySlope I ha hd' := by
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.val_mul, AffineBlowup.awaySlope, AffineBlowup.awaySlope,
    AffineBlowup.awaySlope, AffineBlowup.awaySlope, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, Localization.mk_mul, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, Subtype.ext ?_⟩
  simp [Polynomial.monomial_mul_monomial, h]

/-- The two chart transition maps exhibit `Spec` of the chart ring at a product of two
degree-one Rees elements as the intersection of the two charts. -/
lemma AffineBlowup.isPullback_chart {a b : A} (ha : a ∈ I) (hb : b ∈ I) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading I)
        (reesX_mem I b hb) (rfl : reesX I a ha * reesX I b hb = reesX I a ha * reesX I b hb))))
      (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading I)
        (reesX_mem I a ha) (mul_comm (reesX I a ha) (reesX I b hb)))))
      (AffineBlowup.chart I (reesX I a ha) (reesX_mem I a ha))
      (AffineBlowup.chart I (reesX I b hb) (reesX_mem I b hb)) := by
  refine IsPullback.of_iso_pullback ⟨?_⟩
    (Proj.pullbackAwayιIso (reesGrading I) (reesX_mem I a ha) one_pos (reesX_mem I b hb)
      one_pos (rfl : reesX I a ha * reesX I b hb = reesX I a ha * reesX I b hb)).symm
    ?_ ?_
  · rw [AffineBlowup.chart, AffineBlowup.chart, Proj.SpecMap_awayMap_awayι,
      Proj.SpecMap_awayMap_awayι]
  · exact Proj.pullbackAwayιIso_inv_fst ..
  · exact Proj.pullbackAwayιIso_inv_snd (hx := rfl) ..

variable {X : Scheme.{u}}



set_option maxHeartbeats 1000000 in
-- Unifying the `HomogeneousLocalization` chart rings exceeds the default heartbeat limit.
/-- The chart of the blow-up at a product of two degree-one Rees elements is the
intersection of the two charts. -/
lemma Scheme.IdealSheafData.isPullback_blowupChart {X : Scheme.{u}} (K : X.IdealSheafData)
    (V : X.affineOpens) {a b : Γ(X, V.1)} (ha : a ∈ K.ideal V) (hb : b ∈ K.ideal V) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading (K.ideal V))
        (reesX_mem (K.ideal V) b hb) rfl)))
      (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading (K.ideal V))
        (reesX_mem (K.ideal V) a ha)
        (mul_comm (reesX (K.ideal V) a ha) (reesX (K.ideal V) b hb)))))
      (K.blowupChart V ha) (K.blowupChart V hb) := by
  unfold Scheme.IdealSheafData.blowupChart
  rw [IsPullback.comp_mono_iff (K.blowupι V)]
  exact AffineBlowup.isPullback_chart _ _

set_option maxHeartbeats 1000000 in
-- Unifying the `HomogeneousLocalization` chart rings exceeds the default heartbeat limit.
/-- **The chart-local extensions agree on the overlap.** The exact relations
`b j * a' = b' j * a` between the numerators make the two degree-one slopes restrict to the
same section of the chart at `a · a'`. -/
lemma Scheme.IdealSheafData.homOfVector_awaySlope_compat {X : Scheme.{u}}
    (K : X.IdealSheafData) (V : X.affineOpens) {σ : Type u} {a a' : Γ(X, V.1)}
    (ha : a ∈ K.ideal V) (ha' : a' ∈ K.ideal V) {b b' : σ → Γ(X, V.1)}
    (hb : ∀ j, b j ∈ K.ideal V) (hb' : ∀ j, b' j ∈ K.ideal V)
    (hrel : ∀ j, b j * a' = b' j * a) :
    Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading (K.ideal V))
        (reesX_mem (K.ideal V) a' ha') rfl)) ≫
        AffineSpace.homOfVector (K.blowupChart V ha ≫ K.blowupMap)
          (fun j ↦ (Scheme.ΓSpecIso _).inv
            (AffineBlowup.awaySlope (K.ideal V) ha (hb j))) =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading (K.ideal V))
        (reesX_mem (K.ideal V) a ha)
        (mul_comm (reesX (K.ideal V) a ha) (reesX (K.ideal V) a' ha')))) ≫
        AffineSpace.homOfVector (K.blowupChart V ha' ≫ K.blowupMap)
          (fun j ↦ (Scheme.ΓSpecIso _).inv
            (AffineBlowup.awaySlope (K.ideal V) ha' (hb' j))) := by
  refine AffineSpace.specMap_comp_homOfVector_eq _ _ (K.blowupChart V ha ≫ K.blowupMap)
    (K.blowupChart V ha' ≫ K.blowupMap) ?_ _ _ fun j ↦ ?_
  · rw [← Category.assoc, ← Category.assoc, K.specMap_awayMap_blowupChart V ha ha']
  · exact AffineBlowup.awayMap_awaySlope_eq ha ha' (hb j) (hb' j) (hrel j)

set_option maxHeartbeats 2000000 in
-- Unifying the `HomogeneousLocalization` chart rings exceeds the default heartbeat limit.
/-- **Gluing the chart-local extensions.** Let `a i` and `b i j` be sections of the centre
`K` over an affine open `V` satisfying the exact relations `b i j * a i' = b i' j * a i`.
On the chart of the blow-up at `a i` the degree-one slope `b i j / a i` extends the `j`-th
coordinate, and the relations make the chart transitions hold on the nose, so these local
morphisms to `𝔸(σ; X)` glue over the union `W` of the charts. -/
lemma Scheme.IdealSheafData.exists_hom_affineSpace_of_awaySlope {X : Scheme.{u}}
    (K : X.IdealSheafData) (V : X.affineOpens) {σ ι : Type u}
    {a : ι → Γ(X, V.1)} (ha : ∀ i, a i ∈ K.ideal V)
    {b : ι → σ → Γ(X, V.1)} (hb : ∀ i j, b i j ∈ K.ideal V)
    (hrel : ∀ i i' j, b i j * a i' = b i' j * a i)
    (W : K.blowup.Opens) (hW : W = ⨆ i, (K.blowupChart V (ha i)).opensRange)
    (ci : ∀ i : ι, Spec (.of (HomogeneousLocalization.Away (reesGrading (K.ideal V))
      (reesX (K.ideal V) (a i) (ha i)))) ⟶ W.toScheme)
    (hci : ∀ i, ci i ≫ W.ι = K.blowupChart V (ha i)) :
    ∃ g : W.toScheme ⟶ 𝔸(σ; X), g ≫ 𝔸(σ; X) ↘ X = W.ι ≫ K.blowupMap ∧
      ∀ i, ci i ≫ g = AffineSpace.homOfVector (K.blowupChart V (ha i) ≫ K.blowupMap)
        (fun j ↦ (Scheme.ΓSpecIso _).inv
          (AffineBlowup.awaySlope (K.ideal V) (ha i) (hb i j))) := by
  haveI : ∀ i, IsOpenImmersion (ci i) := by
    intro i
    have h1 : IsOpenImmersion (ci i ≫ W.ι) := by rw [hci i]; infer_instance
    exact IsOpenImmersion.of_comp _ W.ι
  have hcov : ∀ x : W.toScheme, ∃ i y, (ci i) y = x := by
    intro x
    have hx : (x.1 : K.blowup) ∈ ⨆ i : ι, (K.blowupChart V (ha i)).opensRange := by
      rw [← hW]; exact x.2
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨y, hy⟩ := hi
    refine ⟨i, y, W.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hci i, hy]
    rfl
  have hcompat : ∀ i i' : ι,
      pullback.fst (ci i) (ci i') ≫ AffineSpace.homOfVector
          (K.blowupChart V (ha i) ≫ K.blowupMap)
          (fun j ↦ (Scheme.ΓSpecIso _).inv
            (AffineBlowup.awaySlope (K.ideal V) (ha i) (hb i j))) =
        pullback.snd (ci i) (ci i') ≫ AffineSpace.homOfVector
          (K.blowupChart V (ha i') ≫ K.blowupMap)
          (fun j ↦ (Scheme.ΓSpecIso _).inv
            (AffineBlowup.awaySlope (K.ideal V) (ha i') (hb i' j))) := by
    intro i i'
    have hpb : IsPullback
        (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading (K.ideal V))
          (reesX_mem (K.ideal V) (a i') (ha i')) rfl)))
        (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading (K.ideal V))
          (reesX_mem (K.ideal V) (a i) (ha i))
          (mul_comm (reesX (K.ideal V) (a i) (ha i)) (reesX (K.ideal V) (a i') (ha i'))))))
        (ci i) (ci i') := by
      rw [← IsPullback.comp_mono_iff W.ι, hci i, hci i']
      exact K.isPullback_blowupChart V (ha i) (ha i')
    exact hpb.fst_comp_eq_snd_comp _ _
      (K.homOfVector_awaySlope_compat V (ha i) (ha i') (hb i) (hb i') (hrel i i'))
  set 𝒰 : W.toScheme.OpenCover := Scheme.Cover.mkOfCovers ι _ ci hcov with h𝒰def
  have hcompat' : ∀ i i' : ι, pullback.fst (𝒰.f i) (𝒰.f i') ≫ AffineSpace.homOfVector
        (K.blowupChart V (ha i) ≫ K.blowupMap)
        (fun j ↦ (Scheme.ΓSpecIso _).inv
          (AffineBlowup.awaySlope (K.ideal V) (ha i) (hb i j))) =
      pullback.snd (𝒰.f i) (𝒰.f i') ≫ AffineSpace.homOfVector
        (K.blowupChart V (ha i') ≫ K.blowupMap)
        (fun j ↦ (Scheme.ΓSpecIso _).inv
          (AffineBlowup.awaySlope (K.ideal V) (ha i') (hb i' j))) := hcompat
  refine ⟨𝒰.glueMorphisms _ hcompat', ?_, fun i ↦ 𝒰.ι_glueMorphisms _ hcompat' i⟩
  refine Scheme.Cover.hom_ext 𝒰 _ _ fun i ↦ ?_
  have h2 : 𝒰.f i ≫ W.ι = K.blowupChart V (ha i) := hci i
  rw [← Category.assoc, ← Category.assoc, 𝒰.ι_glueMorphisms _ hcompat' i,
    AffineSpace.homOfVector_over, h2]


end AlgebraicGeometry
