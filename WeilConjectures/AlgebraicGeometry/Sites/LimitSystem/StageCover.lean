/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.LimitSystem.Cech

/-!
# Covering stage objects by stage families

Let `D : Iᵒᵖ ⥤ Scheme` be a directed inverse system of quasi-compact quasi-separated schemes with
affine transition maps and limit `X`. Every covering sieve of a stage object `V` of `X_ét` (the
base change of a quasi-compact quasi-separated étale scheme over some stage) contains a stage
family generating a covering sieve
(`AlgebraicGeometry.Etale.SystemData.exists_isStageFamily`), and the Čech nerve of a stage family
consists of stage objects (`AlgebraicGeometry.Etale.SystemData.isStageObject_cechNerveObj`).
Together with `AlgebraicGeometry.Etale.SystemData.exactAt_cechComplex_of_isStageFamily` this
shows that the colimit of a system of injective sheaves has no higher cohomology
(`AlgebraicGeometry.Etale.SystemData.subsingleton_H_succ_of_injective`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Presheaf

namespace AlgebraicGeometry

section AffineSieve

variable {X : Scheme.{u}}

/-- The sieve of the morphisms to `V` whose image lies in an affine open of `V`. -/
def Scheme.Etale.affineSieve (V : X.Etale) : Sieve V where
  arrows _ f := ∃ N : V.left.Opens, IsAffineOpen N ∧ Set.range f.left ⊆ N
  downward_closed {_ _ f} := fun ⟨N, hN, hf⟩ g ↦ ⟨N, hN, fun x ⟨y, hy⟩ ↦ hf ⟨g.left y, by
    rw [← hy]
    rfl⟩⟩

/-- The sieve of the morphisms with image in an affine open is a covering sieve. -/
lemma Scheme.Etale.affineSieve_mem (V : X.Etale) :
    Scheme.Etale.affineSieve V ∈ X.smallEtaleTopology V := by
  let Z (N : V.left.affineOpens) : X.Etale :=
    MorphismProperty.Over.mk ⊤ (N.1.ι ≫ V.hom) inferInstance
  let f (N : V.left.affineOpens) : Z N ⟶ V := MorphismProperty.Over.homMk N.1.ι rfl trivial
  refine X.smallEtaleTopology.superset_covering ?_
    ((Scheme.ofArrows_mem_smallEtaleTopology_iff f).2 ?_)
  · rw [Sieve.generate_le_iff]
    rintro _ _ ⟨N⟩
    exact ⟨N.1, N.2, (Scheme.Opens.range_ι _).subset⟩
  · refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨_, ⟨N, hN, rfl⟩, hxN, -⟩ :=
      V.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact Set.mem_iUnion.2 ⟨⟨N, hN⟩, ⟨⟨x, hxN⟩, rfl⟩⟩

end AffineSieve

namespace Etale.SystemData

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
  {D : Iᵒᵖ ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
  [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
  [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]

omit [IsDirected I (· ≤ ·)] [Nonempty I] [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
  [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)] [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
  in
/-- The Čech nerve of a stage family consists of stage objects. -/
lemma isStageObject_cechNerveObj {V : c.pt.Etale} {n : ℕ} {U : Fin n → Over V}
    (hU : IsStageFamily c V U) {m : ℕ} (y : Fin (m + 1) → Fin n) :
    IsStageObject c (cechNerveObj U y).left := by
  obtain ⟨k, V₀, _, _, e, U₀, hU₀, ⟨ι⟩⟩ := hU
  have : PreservesFiniteProducts (Over.map e.hom) :=
    inferInstanceAs (PreservesFiniteProducts (Over.mapIso e).functor)
  have : PreservesFiniteLimits (Over.post (X := V₀) (c.π.app (op k)).Etale) := inferInstance
  have : PreservesFiniteProducts (Over.post (X := V₀) (c.π.app (op k)).Etale) := inferInstance
  obtain ⟨h₁, h₂⟩ := Scheme.compactSpace_and_quasiSeparatedSpace_piObj
    (fun l ↦ U₀ (y l)) fun l ↦ by
      have := hU₀ (y l)
      exact ⟨inferInstance, inferInstance⟩
  exact ⟨k, (cechNerveObj U₀ y).left, h₁, h₂, ⟨((Over.forget V).mapIso
    (cechNerveObjIso (Over.post (c.π.app (op k)).Etale ⋙ Over.map e.hom) U₀ U ι y)).symm⟩⟩

variable (c) in
/-- The comparison `X ×_{Dₗ} (Dₗ ×_{Dₖ} V₀) ≅ X ×_{Dₖ} V₀` of base changes, for `k ≤ l`. -/
noncomputable def stageBaseChangeIso {k l : I} (hkl : k ≤ l) (V₀ : (D.obj (op k)).Etale) :
    (c.π.app (op l)).Etale.obj ((D.map (homOfLE hkl).op).Etale.obj V₀) ≅
      (c.π.app (op k)).Etale.obj V₀ :=
  ((MorphismProperty.Over.pullbackComp (c.π.app (op l)) (D.map (homOfLE hkl).op)
    (c.π.app (op k)) (c.w _).symm).app V₀).symm

include hc in
/-- An affine étale `X`-scheme `U'` over a stage object `V ≅ X ×_{Dₖ} V₀`, with image in an
affine open of `V`, is the base change of an affine étale scheme over `Dₗ ×_{Dₖ} V₀` for all
large `l`, compatibly with the maps to `V`. -/
lemma exists_stageModel {k : I} {V₀ : (D.obj (op k)).Etale} [CompactSpace V₀.left]
    [QuasiSeparatedSpace V₀.left] {V : c.pt.Etale} (e : (c.π.app (op k)).Etale.obj V₀ ≅ V)
    {U' : c.pt.Etale} [IsAffine U'.left] (g : U' ⟶ V) {N : V.left.Opens} (hN : IsAffineOpen N)
    (hgN : Set.range g.left ⊆ N) :
    ∃ i : I, ∀ (l : I) (hkl : k ≤ l), i ≤ l →
      ∃ (Y : (D.obj (op l)).Etale) (_ : IsAffine Y.left)
        (p : Y ⟶ (D.map (homOfLE hkl).op).Etale.obj V₀)
        (ι : U' ≅ (c.π.app (op l)).Etale.obj Y),
        ι.hom ≫ (c.π.app (op l)).Etale.map p ≫ (stageBaseChangeIso c hkl V₀).hom ≫ e.hom = g := by
  have := isAffineHom_π_app D c hc
  have : Etale V₀.hom := V₀.prop
  have : CompactSpace ↥((𝟭 Scheme).obj V₀.left) := ‹CompactSpace V₀.left›
  have : QuasiSeparatedSpace ↥((𝟭 Scheme).obj V₀.left) := ‹QuasiSeparatedSpace V₀.left›
  have : QuasiSeparatedSpace ↥((Functor.fromPUnit (D.obj (op k))).obj V₀.right) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj (op k)))
  have : QuasiCompact V₀.hom := quasiCompact_of_compactSpace _
  have : QuasiSeparated V₀.hom := QuasiSeparated.of_quasiSeparatedSpace _
  let π₀ : Over.forget (op k) ⋙ D ⟶ (Functor.const (Over (op k))).obj (D.obj (op k)) :=
    { app m := D.map m.hom
      naturality _ _ f := by simp [← D.map_comp, Over.w f] }
  have hck := (Functor.Initial.isLimitWhiskerEquiv (Over.forget (op k)) c).symm hc
  let P := c.π.app (op k)
  have hP : ∀ m, P = (c.whisker (Over.forget (op k))).π.app m ≫ π₀.app m :=
    fun m ↦ by change c.π.app (op k) = _; rw [← c.w m.hom]; rfl
  let D' := baseChangeOverDiagram (Over.forget (op k) ⋙ D) π₀ V₀.hom
  let c' := baseChangeOverCone (Over.forget (op k) ⋙ D) π₀ (c.whisker (Over.forget (op k))) P hP
    V₀.hom
  have hc' := isLimitBaseChangeOverCone (Over.forget (op k) ⋙ D) π₀
    (c.whisker (Over.forget (op k))) P hP V₀.hom hck
  let πV : D' ⟶ (Functor.const (Over (op k))).obj V₀.left :=
    { app m := pullback.fst V₀.hom (π₀.app m)
      naturality _ _ f := by simp [D'] }
  have (m : Over (op k)) : CompactSpace ((Over.forget (op k) ⋙ D).obj m) :=
    inferInstanceAs (CompactSpace (D.obj m.left))
  have (m : Over (op k)) : QuasiSeparatedSpace ((Over.forget (op k) ⋙ D).obj m) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj m.left))
  have {m m' : Over (op k)} (f : m ⟶ m') : IsAffineHom ((Over.forget (op k) ⋙ D).map f) :=
    inferInstanceAs (IsAffineHom (D.map f.left))
  -- `U'` as an étale scheme over `X ×_{Dₖ} V₀`
  have hw : (g ≫ e.inv).left ≫ ((c.π.app (op k)).Etale.obj V₀).hom = U'.hom :=
    MorphismProperty.Over.w _
  have : Etale ((g ≫ e.inv).left ≫ ((c.π.app (op k)).Etale.obj V₀).hom) := by
    rw [hw]; exact U'.prop
  have : Etale (g ≫ e.inv).left := Etale.of_comp _ ((c.π.app (op k)).Etale.obj V₀).hom
  let V' : ((c.π.app (op k)).Etale.obj V₀).left.Etale :=
    MorphismProperty.Over.mk ⊤ (g ≫ e.inv).left this
  have hVN (x : V'.left) : e.hom.left (V'.hom x) ∈ N := by
    refine hgN ⟨x, ?_⟩
    change g.left x = e.hom.left ((g ≫ e.inv).left x)
    rw [← Scheme.Hom.comp_apply, ← MorphismProperty.Comma.comp_left, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have : IsAffine V'.left := ‹IsAffine U'.left›
  obtain ⟨iO, hiO⟩ := exists_hasStageModel (D := D') (π := πV) (c := c') hc'
    (pullback.fst V₀.hom P) (fun m ↦ by simp [c', πV]) V' (hN.preimage e.hom.left)
    (by rintro _ ⟨x, rfl⟩; exact hVN x) (𝟙 V₀.left) (𝟙 V₀.left)
    ((g ≫ e.inv).left ≫ pullback.fst V₀.hom P) (by simp [V'])
    ((g ≫ e.inv).left ≫ pullback.fst V₀.hom P) (by simp [V'])
  refine ⟨iO.left.unop, fun l hkl hil ↦ ?_⟩
  let lO : Over (op k) := Over.mk (homOfLE hkl).op
  obtain ⟨Y, p, h, -, -, hp, hY, hpb, -, -, -, -⟩ :=
    hiO.mono (Over.homMk (homOfLE hil).op (Subsingleton.elim _ _) : lO ⟶ iO)
  have hpb' := hpb.paste_vert (isPullback_baseChangeOverCone_π (Over.forget (op k) ⋙ D) π₀
    (c.whisker (Over.forget (op k))) P hP V₀.hom lO)
  have : Etale p := hp
  have : Etale (pullback.snd V₀.hom (D.map (homOfLE hkl).op)) := inferInstance
  let Y' : (D.obj (op l)).Etale :=
    MorphismProperty.Over.mk ⊤ (p ≫ pullback.snd V₀.hom (D.map (homOfLE hkl).op)) inferInstance
  let p' : Y' ⟶ (D.map (homOfLE hkl).op).Etale.obj V₀ := MorphismProperty.Over.homMk p rfl trivial
  let ι : U' ≅ (c.π.app (op l)).Etale.obj Y' := MorphismProperty.Over.isoMk hpb'.isoPullback (by
    change hpb'.isoPullback.hom ≫ pullback.snd _ _ = _
    rw [IsPullback.isoPullback_hom_snd]
    exact hw)
  refine ⟨Y', hY, p', ι, ?_⟩
  rw [← cancel_mono e.inv, Category.assoc, Category.assoc, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · simp only [Functor.id_obj, Functor.const_obj_obj, Scheme.Hom.Etale,
      MorphismProperty.Over.pullback, homOfLE_leOfHom, Cone.whisker_pt, Functor.comp_obj,
      Over.forget_obj, Cone.whisker_π, Functor.whiskerLeft_app, MorphismProperty.Over.homMk_hom,
      Over.homMk_left, stageBaseChangeIso, Iso.symm_hom, Iso.app_inv, etale_comp_left,
      MorphismProperty.Over.isoMk_hom_left, MorphismProperty.Over.pullbackComp_inv_app_left,
      Category.assoc, limit.lift_π, PullbackCone.mk_π_app, Category.comp_id,
      pullbackLeftPullbackSndIso_hom_fst, Y', ι, p']
    erw [pullback.lift_fst_assoc]
    rw [Category.assoc]
    erw [IsPullback.isoPullback_hom_fst_assoc]
    rw [hpb.w_assoc]
    simp only [c', V', baseChangeOverCone_π_app]
    erw [pullback.lift_fst, Category.comp_id]
    rfl
  · simp only [Functor.const_obj_obj, Functor.id_obj, Scheme.Hom.Etale,
      MorphismProperty.Over.pullback, homOfLE_leOfHom, Cone.whisker_pt, Functor.comp_obj,
      Over.forget_obj, Cone.whisker_π, Functor.whiskerLeft_app, MorphismProperty.Over.homMk_hom,
      Over.homMk_left, stageBaseChangeIso, Iso.symm_hom, Iso.app_inv, etale_comp_left,
      MorphismProperty.Over.isoMk_hom_left, MorphismProperty.Over.pullbackComp_inv_app_left,
      Category.assoc, limit.lift_π, PullbackCone.mk_π_app, Category.comp_id,
      pullbackLeftPullbackSndIso_hom_snd, Y', ι, p']
    erw [pullback.lift_snd, IsPullback.isoPullback_hom_snd]
    simp [V']
    rfl

include hc in
/-- Every covering sieve of a stage object contains a stage family generating a covering sieve.
-/
lemma exists_isStageFamily {V : c.pt.Etale} (hV : IsStageObject c V) {R : Sieve V}
    (hR : R ∈ c.pt.smallEtaleTopology V) :
    ∃ (n : ℕ) (U : Fin n → Over V), IsStageFamily c V U ∧ (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ c.pt.smallEtaleTopology V := by
  obtain ⟨k, V₀, _, _, ⟨e⟩⟩ := hV
  have := isAffineHom_π_app D c hc
  obtain ⟨_, _⟩ := Scheme.compactSpace_and_quasiSeparatedSpace_of_iso e
    (compactSpace_and_quasiSeparatedSpace_pullback_left (c.π.app (op k)) V₀)
  obtain ⟨n, U', g, hgR, hU', hcov⟩ := Scheme.exists_finite_affine_of_mem_smallEtaleTopology
    (c.pt.smallEtaleTopology.intersection_covering hR (Scheme.Etale.affineSieve_mem V))
  choose N hN hgN using fun a ↦ (hgR a).2
  refine ⟨n, fun a ↦ Over.mk (g a), ?_, fun a ↦ (hgR a).1,
    (Scheme.ofArrows_mem_smallEtaleTopology_iff _).2 hcov⟩
  classical
  choose i hi using fun a ↦
    have := hU' a
    exists_stageModel hc e (g a) (hN a) (hgN a)
  obtain ⟨l, hl⟩ := Finset.exists_le (insert k (Finset.univ.image i))
  have hkl : k ≤ l := hl k (Finset.mem_insert_self _ _)
  choose Y hY p ι hι using fun a ↦ hi a l hkl
    (hl _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ a))))
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_pullback_left (D.map (homOfLE hkl).op) V₀
  exact ⟨l, (D.map (homOfLE hkl).op).Etale.obj V₀, ‹_›, ‹_›, stageBaseChangeIso c hkl V₀ ≪≫ e,
    fun a ↦ Over.mk (p a), fun a ↦ hY a, ⟨fun a ↦ Over.isoMk (ι a) (hι a)⟩⟩

include hc in
/-- **The colimit of a system of injective sheaves is acyclic.** Let `(Eᵢ)` be a system of
injective abelian étale sheaves over a directed inverse system of quasi-compact quasi-separated
schemes `Dᵢ` with affine transition maps and limit `X`. Then the colimit `L` on `X` of the
pullbacks of the `Eᵢ` has no higher cohomology. -/
theorem subsingleton_H_succ_of_injective (S : SystemData D c) (hE : ∀ i, Injective (S.F i))
    (q : ℕ) : Subsingleton (Sheaf.H S.L.pt (q + 1)) := by
  obtain ⟨k⟩ := ‹Nonempty I›
  let T₀ : (D.obj (op k)).Etale :=
    MorphismProperty.Over.mk ⊤ (𝟙 (D.obj (op k))) (MorphismProperty.id_mem _ _)
  have hT : IsTerminal ((c.π.app (op k)).Etale.obj T₀) :=
    IsTerminal.isTerminalObj _ _ (MorphismProperty.Over.mkIdTerminal _ _)
  have : CompactSpace T₀.left := inferInstanceAs (CompactSpace (D.obj (op k)))
  have : QuasiSeparatedSpace T₀.left := inferInstanceAs (QuasiSeparatedSpace (D.obj (op k)))
  refine Sheaf.subsingleton_H_succ_of_exactAt_cechComplex_of_good hT (IsStageObject c)
    ⟨k, T₀, ‹_›, ‹_›, ⟨Iso.refl _⟩⟩ (fun V _ U ↦ IsStageFamily c V U) (fun V hV R hR ↦ ?_)
    S.L.pt (fun V _ _ U hU _ _ q ↦ S.exactAt_cechComplex_of_isStageFamily hc hE U hU q) q
  obtain ⟨n, U, hU, hUR, hUJ⟩ := exists_isStageFamily hc hV hR
  exact ⟨n, U, hU, fun _ y ↦ isStageObject_cechNerveObj hU y, hUR, hUJ⟩

end Etale.SystemData

end AlgebraicGeometry
