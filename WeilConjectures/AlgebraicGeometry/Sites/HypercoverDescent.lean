/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleHypercover
public import WeilConjectures.AlgebraicGeometry.Sites.UpperStarSectionsLimitModule
public import WeilConjectures.AlgebraicTopology.SemiSimplicialObject.Coskeleton

/-!
# Descent of truncated étale hypercovers to a finite stage

Let `X = lim Dᵢ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition maps, and let `U` be a qcqs hypercover of `X` (a semi-simplicial object of the small
étale site of `X` with quasi-compact quasi-separated terms). We show that the truncation of `U`
in degrees `≤ N` descends to some stage `Dₖ` (blueprint
`lemma-weil-pbc-finite-hypercover-descent`):

- `AlgebraicGeometry.TruncatedDescent`: an `N`-truncated semi-simplicial object `T` of the small
  étale site of `Dₖ` with quasi-compact quasi-separated terms, together with identifications
  `U_n ≅ T_n ×_{Dₖ} X` (`n ≤ N`) compatible with the face maps;
- `AlgebraicGeometry.exists_truncatedDescent`: such data exists at some stage;
- `AlgebraicGeometry.TruncatedDescent.baseChange`: the data can be moved to any later stage;
- `AlgebraicGeometry.TruncatedDescent.exists_isHypercover`: at every late enough stage, the
  coskeletal extension of `T` (`CategoryTheory.SemiSimplicialObject.Truncated.cosk`), which
  continues `T` above degree `N` by the matching objects, is a qcqs hypercover;
- `AlgebraicGeometry.TruncatedDescent.toCosk`: the morphism of semi-simplicial objects from `U`
  to the base change to `X` of the coskeletal extension of `T`, which is the given identification
  in degrees `≤ N`.

Morphisms between truncated hypercovers descend as well
(`AlgebraicGeometry.TruncatedDescent.exists_homDescent`).

The main inputs are the descent of quasi-compact quasi-separated étale schemes, of morphisms, of
equalities of morphisms and of surjectivity to a finite stage
(`AlgebraicGeometry.etale_finite_data_descent_of_isLimit`, blueprint
`lem-weil-pbc-etale-finite-data-descent`), and the fact that matching objects are finite limits,
so that their formation commutes with base change and preserves quasi-compactness and
quasi-separatedness.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Scheme.Etale

variable {X : Scheme.{u}}

/-- The terminal object `X` of the small étale site of `X`. -/
noncomputable def isTerminal (X : Scheme.{u}) :
    IsTerminal (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X) : X.Etale) :=
  MorphismProperty.Over.mkIdTerminal _ X

/-- The isomorphism of underlying schemes induced by an isomorphism of étale `X`-schemes. -/
noncomputable def leftIso {A B : X.Etale} (e : A ≅ B) : A.left ≅ B.left :=
  (MorphismProperty.Over.forget @Etale ⊤ X ⋙ Over.forget X).mapIso e

@[simp]
lemma leftIso_hom {A B : X.Etale} (e : A ≅ B) : (leftIso e).hom = e.hom.left := rfl

@[simp]
lemma leftIso_inv {A B : X.Etale} (e : A ≅ B) : (leftIso e).inv = e.inv.left := rfl

/-- Surjectivity of the underlying morphism of schemes is invariant under isomorphisms of
arrows. -/
lemma surjective_left_iff_of_comm {A B A' B' : X.Etale} (e : A ⟶ B) (e' : A' ⟶ B')
    (i : A ≅ A') (j : B ≅ B') (h : e ≫ j.hom = i.hom ≫ e') :
    Surjective e.left ↔ Surjective e'.left :=
  MorphismProperty.arrow_mk_iso_iff @Surjective
    (Arrow.isoMk (leftIso i) (leftIso j) (by
      simp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, leftIso_hom]
      rw [← MorphismProperty.Comma.comp_left, ← h, MorphismProperty.Comma.comp_left]))

/-- A semi-simplicial object of the small étale site is a hypercover if and only if its
`0`-simplices cover `X` and all its matching maps are surjective. -/
lemma isHypercover_iff_surjective (V : SemiSimplicialObject X.Etale) :
    V.IsHypercover X.smallEtaleTopology ↔
      Surjective (V.obj 0).hom ∧ ∀ n, Surjective (V.toMatching n).left := by
  rw [SemiSimplicialObject.isHypercover_iff _ V (isTerminal X)]
  simp only [ofArrows_mem_smallEtaleTopology_iff, Set.iUnion_const, Set.range_eq_univ,
    ← surjective_iff]
  have h : ((isTerminal X).from (V.obj 0)).left = (V.obj 0).hom := by
    have := MorphismProperty.Over.w ((isTerminal X).from (V.obj 0))
    erw [Category.comp_id] at this
    exact this
  rw [h]

/-- The quasi-compact quasi-separated étale `X`-schemes. -/
def qcqs (X : Scheme.{u}) : ObjectProperty X.Etale :=
  fun V ↦ CompactSpace V.left ∧ QuasiSeparatedSpace V.left

instance : (qcqs X).IsClosedUnderIsomorphisms where
  of_iso {A B} e h := by
    obtain ⟨_, _⟩ := h
    exact ⟨QuasiCompact.compactSpace_of_compactSpace (leftIso e).inv,
      quasiSeparatedSpace_of_quasiSeparated (leftIso e).inv⟩

instance [CompactSpace X] [QuasiSeparatedSpace X] :
    (qcqs X).IsClosedUnderLimitsOfShape (Discrete PEmpty.{1}) where
  limitsOfShape_le := by
    rintro Y ⟨p⟩
    have hY : IsTerminal Y :=
      (IsLimit.equivOfNatIsoOfIso p.diag.uniqueFromEmpty _ _
        (by exact Cone.ext (Iso.refl _) (by rintro ⟨⟨⟩⟩))).1 p.isLimit
    refine (qcqs X).prop_of_iso ((isTerminal X).uniqueUpToIso hY) ?_
    exact ⟨inferInstanceAs (CompactSpace X), inferInstanceAs (QuasiSeparatedSpace X)⟩

instance [QuasiSeparatedSpace X] : (qcqs X).IsClosedUnderLimitsOfShape WalkingCospan where
  limitsOfShape_le := by
    rintro Y ⟨p⟩
    let F := MorphismProperty.Over.forget @Etale ⊤ X ⋙ Over.forget X
    let e : Y.left ≅ pullback (p.diag.map WalkingCospan.Hom.inl).left
        (p.diag.map WalkingCospan.Hom.inr).left :=
      (isLimitOfPreserves F p.isLimit).conePointUniqueUpToIso (limit.isLimit _) ≪≫
        HasLimit.isoOfNatIso (diagramIsoCospan (p.diag ⋙ F))
    obtain ⟨_, _⟩ := p.prop_diag_obj WalkingCospan.left
    obtain ⟨_, _⟩ := p.prop_diag_obj WalkingCospan.right
    obtain ⟨_, _⟩ := p.prop_diag_obj WalkingCospan.one
    have : QuasiCompact (p.diag.map WalkingCospan.Hom.inl).left :=
      quasiCompact_of_compactSpace _
    exact ⟨QuasiCompact.compactSpace_of_compactSpace e.hom,
      @quasiSeparatedSpace_of_quasiSeparated _ _ (e.hom ≫ pullback.fst _ _) _ inferInstance⟩

instance [CompactSpace X] [QuasiSeparatedSpace X] (J : Type) [SmallCategory J] [FinCategory J] :
    (qcqs X).IsClosedUnderLimitsOfShape J := by
  have := hasFiniteLimits_of_hasTerminal_and_pullbacks (C := (qcqs X).FullSubcategory)
  have : PreservesFiniteLimits (qcqs X).ι :=
    preservesFiniteLimits_of_preservesTerminal_and_pullbacks _
  exact (qcqs X).isClosedUnderLimitsOfShape_of_preservesLimitsOfShape_ι _

/-- Matching objects of quasi-compact quasi-separated étale schemes over a quasi-compact
quasi-separated scheme are quasi-compact and quasi-separated. -/
lemma qcqs_matching [CompactSpace X] [QuasiSeparatedSpace X] (V : SemiSimplicialObject X.Etale)
    (n : ℕ) (hV : ∀ k, k ≤ n → qcqs X (V.obj k)) : qcqs X (V.matching n) := by
  cases n with
  | zero => exact (qcqs X).prop_pi _ fun _ ↦ hV 0 le_rfl
  | succ m =>
    refine (qcqs X).prop_limit _ fun j ↦ ?_
    cases j
    · exact (qcqs X).prop_pi _ fun _ ↦ hV (m + 1) le_rfl
    · exact (qcqs X).prop_pi _ fun _ ↦ hV m (by omega)

end Scheme.Etale

section Stage

variable {I : Type u} [SmallCategory I] [IsCofiltered I] {D : I ⥤ Scheme.{u}} {c : Cone D}
  (hc : IsLimit c)

/-- (Implementation) The structure morphisms `Dⱼ ⟶ Dₖ` of the stages over a stage `k`. -/
@[simps]
def overStageπ (k : I) : Over.forget k ⋙ D ⟶ (Functor.const (Over k)).obj (D.obj k) where
  app j := D.map j.hom
  naturality j j' f := by simp [← D.map_comp]

include hc in
/-- (Implementation) The limit is also the limit of the stages over a stage `k`. -/
noncomputable def isLimitOverStage (k : I) : IsLimit (c.whisker (Over.forget k)) :=
  (Functor.Initial.isLimitWhiskerEquiv (Over.forget k) c).symm hc

omit [IsCofiltered I] in
/-- A pullback square from the limit to a stage `k` induces a pullback square from the limit to
any later stage `k'`. -/
lemma isPullback_lift_of_isPullback {k k' : I} (g : k' ⟶ k) {Y : (D.obj k).Etale}
    {V : c.pt.Etale} {m : V.left ⟶ Y.left} (hm : IsPullback m V.hom Y.hom (c.π.app k)) :
    IsPullback (pullback.lift m (V.hom ≫ c.π.app k')
        (by rw [hm.w, Category.assoc, c.w g]) : V.left ⟶ pullback Y.hom (D.map g))
      V.hom (pullback.snd Y.hom (D.map g)) (c.π.app k') := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [pullback.lift_fst, c.w g]
  exact hm

variable [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]

omit [∀ i, CompactSpace (D.obj i)] in
include hc in
/-- The limit is quasi-separated. -/
lemma quasiSeparatedSpace_pt : QuasiSeparatedSpace c.pt := by
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  have := isAffineHom_π_app D c hc i
  exact quasiSeparatedSpace_of_quasiSeparated (c.π.app i)

include hc in
/-- **Quasi-compact quasi-separated étale schemes descend** to a stage. -/
lemma exists_isPullback_etale (V : c.pt.Etale) [CompactSpace V.left]
    [QuasiSeparatedSpace V.left] :
    ∃ (k : I) (Y : (D.obj k).Etale) (_ : CompactSpace Y.left) (_ : QuasiSeparatedSpace Y.left)
      (m : V.left ⟶ Y.left), IsPullback m V.hom Y.hom (c.π.app k) := by
  have := quasiSeparatedSpace_pt hc
  have : CompactSpace ((𝟭 Scheme).obj V.left) := inferInstanceAs (CompactSpace V.left)
  have : QuasiSeparatedSpace ((𝟭 Scheme).obj V.left) := inferInstanceAs (QuasiSeparatedSpace V.left)
  have : QuasiSeparatedSpace ((Functor.fromPUnit c.pt).obj V.right) := quasiSeparatedSpace_pt hc
  have : QuasiCompact V.hom := quasiCompact_of_compactSpace _
  obtain ⟨k, Y, p, hp, h₁, h₂, m, H⟩ := exists_etale_isPullback_of_isLimit D c hc V.hom
  exact ⟨k, MorphismProperty.Over.mk ⊤ p hp, h₁, h₂, m, H⟩

omit [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
include hc in
/-- **Morphisms descend** to a stage: a morphism over `X ⟶ Dₖ` from the base change `V` of a
quasi-compact quasi-separated étale `Dₖ`-scheme `A` to an étale `Dₖ`-scheme `B` comes from a
morphism `A ×_{Dₖ} Dₖ' ⟶ B ×_{Dₖ} Dₖ'` at every late enough stage. -/
lemma exists_hom_descent_stage {k : I} {A B : (D.obj k).Etale} [CompactSpace A.left]
    [QuasiSeparatedSpace A.left] {V : c.pt.Etale} {mA : V.left ⟶ A.left}
    (hA : IsPullback mA V.hom A.hom (c.π.app k)) (φ : V.left ⟶ B.left)
    (hφ : φ ≫ B.hom = V.hom ≫ c.π.app k) :
    ∃ (k' : I) (g : k' ⟶ k), ∀ (k'' : I) (g' : k'' ⟶ k'),
      ∃ ψ : (MorphismProperty.Over.pullback @Etale ⊤ (D.map (g' ≫ g))).obj A ⟶
          (MorphismProperty.Over.pullback @Etale ⊤ (D.map (g' ≫ g))).obj B,
        pullback.lift mA (V.hom ≫ c.π.app k'') (by rw [hA.w, Category.assoc, c.w]) ≫
          ψ.left ≫ pullback.fst _ _ = φ := by
  have : CompactSpace ((𝟭 Scheme).obj A.left) := inferInstanceAs (CompactSpace A.left)
  have : QuasiSeparatedSpace ((𝟭 Scheme).obj A.left) := inferInstanceAs (QuasiSeparatedSpace A.left)
  have : ∀ {i j : Over k} (f : i ⟶ j), IsAffineHom ((Over.forget k ⋙ D).map f) :=
    fun f ↦ inferInstanceAs (IsAffineHom (D.map f.left))
  obtain ⟨k', f, ψ, hψ, hψφ⟩ := exists_hom_descent_of_isLimit (Over.forget k ⋙ D)
    (c.whisker (Over.forget k)) (isLimitOverStage hc k) (overStageπ k) (k := Over.mk (𝟙 k))
    A.hom B.hom (hA.isoPullback.inv ≫ φ) (by
      simp [hφ, IsPullback.isoPullback_inv_snd_assoc])
  refine ⟨k'.left, f.left, fun k'' g' ↦ ?_⟩
  have hfk : f.left = k'.hom := by simpa using Over.w f
  let ψ' : pullback A.hom (D.map (g' ≫ f.left)) ⟶ B.left :=
    pullback.map A.hom (D.map (g' ≫ f.left)) A.hom (D.map f.left) (𝟙 _) (D.map g') (𝟙 _)
      (by simp) (by simp) ≫ ψ
  have hψ' : ψ' ≫ B.hom = pullback.snd _ _ ≫ D.map (g' ≫ f.left) := by
    have : ψ ≫ B.hom = pullback.snd _ _ ≫ D.map f.left := by
      simpa [← hfk] using hψ
    simp [ψ', this]
  refine ⟨Etale.homToPullback (D.map (g' ≫ f.left)) ψ' hψ', ?_⟩
  rw [Etale.homToPullback_left_fst]
  have e : pullback.lift mA (V.hom ≫ c.π.app k'') (by rw [hA.w, Category.assoc, c.w]) ≫
      pullback.map A.hom (D.map (g' ≫ f.left)) A.hom (D.map f.left) (𝟙 _) (D.map g') (𝟙 _)
        (by simp) (by simp) =
      hA.isoPullback.hom ≫ pullback.map A.hom (c.π.app k) A.hom (D.map f.left) (𝟙 _)
        (c.π.app k'.left) (𝟙 _) (by simp) (by simp [c.w]) := by
    apply pullback.hom_ext <;> simp [c.w]
  calc _ = hA.isoPullback.hom ≫ (pullback.map A.hom (c.π.app k) A.hom (D.map f.left) (𝟙 _)
        (c.π.app k'.left) (𝟙 _) (by simp) (by simp [c.w]) ≫ ψ) := by
          simp only [ψ', ← Category.assoc, e]
    _ = hA.isoPullback.hom ≫ (hA.isoPullback.inv ≫ φ) := congrArg _ hψφ
    _ = φ := by rw [Iso.hom_inv_id_assoc]

omit [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
include hc in
/-- **Equalities of morphisms descend** to a stage. -/
lemma exists_eq_descent_stage {k : I} {A B : (D.obj k).Etale} [CompactSpace A.left]
    {V : c.pt.Etale} {mA : V.left ⟶ A.left} (hA : IsPullback mA V.hom A.hom (c.π.app k))
    (a b : A ⟶ B) (h : mA ≫ a.left = mA ≫ b.left) :
    ∃ (k' : I) (g : k' ⟶ k), ∀ (k'' : I) (g' : k'' ⟶ k'),
      (MorphismProperty.Over.pullback @Etale ⊤ (D.map (g' ≫ g))).map a =
        (MorphismProperty.Over.pullback @Etale ⊤ (D.map (g' ≫ g))).map b := by
  have : CompactSpace ((𝟭 Scheme).obj A.left) := inferInstanceAs (CompactSpace A.left)
  have : ∀ {i j : Over k} (f : i ⟶ j), IsAffineHom ((Over.forget k ⋙ D).map f) :=
    fun f ↦ inferInstanceAs (IsAffineHom (D.map f.left))
  obtain ⟨k', f, hf⟩ := exists_eq_descent_of_isLimit (Over.forget k ⋙ D)
    (c.whisker (Over.forget k)) (isLimitOverStage hc k) (overStageπ k) (k := Over.mk (𝟙 k))
    A.hom B.hom a.left b.left (by simp [MorphismProperty.Over.w a])
    (by simp [MorphismProperty.Over.w b]) (by
      change pullback.fst A.hom (c.π.app k) ≫ a.left = pullback.fst A.hom (c.π.app k) ≫ b.left
      rw [← hA.isoPullback_inv_fst, Category.assoc, Category.assoc, h])
  refine ⟨k'.left, f.left, fun k'' g' ↦ ?_⟩
  apply Etale.hom_ext_pullback
  simp only [Etale.overPullback_map_left, pullback.lift_fst]
  simpa using congrArg (pullback.map A.hom (D.map (g' ≫ f.left)) A.hom (D.map f.left) (𝟙 _)
    (D.map g') (𝟙 _) (by simp) (by simp) ≫ ·) hf

omit [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
include hc in
/-- **Surjectivity descends** to a stage: if the base change to the limit of a morphism of étale
`Dₖ`-schemes with quasi-compact target is surjective, so are its base changes to all late enough
stages. -/
lemma exists_surjective_descent_stage {k : I} {A B : (D.obj k).Etale} [CompactSpace B.left]
    (e : A ⟶ B)
    (h : Surjective ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app k)).map e).left) :
    ∃ (k' : I) (g : k' ⟶ k), ∀ (k'' : I) (g' : k'' ⟶ k'),
      Surjective ((MorphismProperty.Over.pullback @Etale ⊤ (D.map (g' ≫ g))).map e).left := by
  have : CompactSpace ((𝟭 Scheme).obj B.left) := inferInstanceAs (CompactSpace B.left)
  obtain ⟨k', f, hf⟩ := exists_forall_mem_range_of_isLimit D c hc B.hom (ι := PUnit.{u + 1})
    (fun _ ↦ e.left) (fun x ↦ by
      obtain ⟨y, rfl⟩ := h.surj x
      refine ⟨PUnit.unit, pullback.fst A.hom (c.π.app k) y, ?_⟩
      have hcomm : ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app k)).map e).left ≫
          pullback.fst B.hom (c.π.app k) = pullback.fst A.hom (c.π.app k) ≫ e.left := by simp
      exact (congrArg (fun φ ↦ φ.base y) hcomm).symm)
  refine ⟨k', f, fun k'' g' ↦ ⟨fun x ↦ ?_⟩⟩
  obtain ⟨-, a, ha⟩ := hf k'' g' x
  -- the base change of `e` is the base change of `e.left` along `B ×_{Dₖ} Dₖ'' ⟶ B`
  have H : IsPullback (pullback.fst A.hom (D.map (g' ≫ f)))
      ((MorphismProperty.Over.pullback @Etale ⊤ (D.map (g' ≫ f))).map e).left e.left
      (pullback.fst B.hom (D.map (g' ≫ f))) := by
    refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback B.hom (D.map (g' ≫ f)))
    simpa [MorphismProperty.Over.w e] using IsPullback.of_hasPullback A.hom (D.map (g' ≫ f))
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := e.left)
    (g := pullback.fst B.hom (D.map (g' ≫ f))) a x ha
  refine ⟨H.isoPullback.inv z, ?_⟩
  exact (congrArg (fun φ ↦ φ.base z) H.isoPullback_inv_snd).trans hz

end Stage

end AlgebraicGeometry
