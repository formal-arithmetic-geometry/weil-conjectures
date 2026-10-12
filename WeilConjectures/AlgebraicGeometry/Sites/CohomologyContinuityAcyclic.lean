/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuityCech
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleLimitDescent
public import WeilConjectures.CategoryTheory.Sites.CechComplexFunctor
public import WeilConjectures.CategoryTheory.Sites.CechCriterionFamily

/-!
# Inverse images of injective sheaves at a cofiltered limit are acyclic

Let `X = lim Dⱼ` be a cofiltered limit of quasi-compact quasi-separated schemes over a scheme
`R`, with affine transition maps, and let `G` be an abelian étale sheaf on `R` whose inverse
images to all the stages `Dⱼ` are injective (for instance an injective sheaf, when all the
`Dⱼ ⟶ R` are étale). Then the inverse image of `G` to `X` has no cohomology in positive degrees.
We apply the Čech criterion
`CategoryTheory.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex_of_good`
We apply the Čech criterion `CategoryTheory.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex_of_good`
to the étale `X`-schemes which are base changes `V' ×_{Dₘ} X` of quasi-compact quasi-separated
étale schemes `V'` over a stage, and to the finite families which are base changes of finite
families of affine étale schemes over a stage. Every étale covering of such a base change is
refined by such a family (`AlgebraicGeometry.Etale.exists_limitFamily`, by the descent of étale
schemes to a stage `AlgebraicGeometry.exists_etale_refinement_of_isLimit`). The Čech complex of
the inverse image of `G` on the base change of a family is the Čech complex of the pushforward
to the stage (`CategoryTheory.Presheaf.exactAt_cechComplex_map_iff`), which is exact in positive
degrees by `AlgebraicGeometry.Etale.exactAt_cechComplex_lowerStar_upperStar_of_isLimit`.

## Main statements

- `AlgebraicGeometry.Etale.subsingleton_H_succ_upperStar_of_isLimit`: the vanishing.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Presheaf

namespace AlgebraicGeometry.Etale

variable {J : Type u} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{u}) (c : Cone D)

/-- Base change from a stage `Dₘ` to the limit `X`, followed by an isomorphism
`W ≅ V' ×_{Dₘ} X`, on objects over `V'`. -/
noncomputable abbrev limitFamilyFunctor {m : J} {W : c.pt.Etale} {V' : (D.obj m).Etale}
    (e : W ≅ (c.π.app m).Etale.obj V') : Over V' ⥤ Over W :=
  Over.post (c.π.app m).Etale ⋙ (Over.mapIso e.symm).functor

/-- `AlgebraicGeometry.Etale.limitFamilyFunctor` lies over the base change functor. -/
noncomputable def limitFamilyFunctorForgetIso {m : J} {W : c.pt.Etale} {V' : (D.obj m).Etale}
    (e : W ≅ (c.π.app m).Etale.obj V') :
    limitFamilyFunctor D c e ⋙ Over.forget W ≅ Over.forget V' ⋙ (c.π.app m).Etale :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl)

instance {m : J} {W : c.pt.Etale} {V' : (D.obj m).Etale} (e : W ≅ (c.π.app m).Etale.obj V') :
    PreservesFiniteProducts (limitFamilyFunctor D c e) := by
  dsimp only [limitFamilyFunctor]
  infer_instance

variable [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
  [∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)]

/-- (Implementation) A base change of a quasi-compact quasi-separated étale scheme over a stage
along an affine morphism is quasi-compact and quasi-separated. -/
lemma compactSpace_and_quasiSeparatedSpace_pullback_of_isAffineHom {Y Z T : Scheme.{u}} (p : Y ⟶ T)
    (g : Z ⟶ T) [IsAffineHom g] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    CompactSpace ↥(pullback p g) ∧ QuasiSeparatedSpace ↥(pullback p g) :=
  ⟨inferInstance, quasiSeparatedSpace_of_quasiSeparated (pullback.fst p g)⟩

omit [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)] in
/-- **Coverings of base changes are refined by base changes of affine families.** Let `W` be
isomorphic to the base change `V' ×_{Dₘ} X` of a quasi-compact quasi-separated étale scheme `V'`
over a stage. Every covering sieve of `W` contains a finite covering family which, up to the
isomorphism `W ≅ V'' ×_{D_K} X` with `V'' = V' ×_{Dₘ} D_K`, is the base change of a finite family
of affine étale schemes over `V''`, for some later stage `K`. -/
theorem exists_limitFamily (hc : IsLimit c) {m : J} (V' : (D.obj m).Etale) [CompactSpace V'.left]
    [QuasiSeparatedSpace V'.left] {W : c.pt.Etale} (e : W ≅ (c.π.app m).Etale.obj V')
    (R : Sieve W) (hR : R ∈ c.pt.smallEtaleTopology W) :
    ∃ (n : ℕ) (K : J) (V'' : (D.obj K).Etale) (_ : CompactSpace V''.left)
      (_ : QuasiSeparatedSpace V''.left) (e' : W ≅ (c.π.app K).Etale.obj V'')
      (U' : Fin n → Over V''), (∀ a, IsAffine (U' a).left.left) ∧
        (∀ a, R ((limitFamilyFunctor D c e').obj (U' a)).hom) ∧
        ⋃ a, Set.range ((limitFamilyFunctor D c e').obj (U' a)).hom.left = Set.univ := by
  classical
  have hπaff (i : J) : IsAffineHom (c.π.app i) := isAffineHom_π_app D c hc i
  -- pointwise refinements by base changes of affine étale schemes over stages
  have hpt (x : W.left) : ∃ (Z : c.pt.Etale) (g : Z ⟶ W) (_ : R g) (k' : J) (f : k' ⟶ m)
      (E : Scheme.{u}) (_ : IsAffine E) (q : E ⟶ D.obj k') (_ : AlgebraicGeometry.Etale q)
      (eE : E ⟶ V'.left) (he : eE ≫ V'.hom = q ≫ D.map f) (E' : Scheme.{u}) (π₁ : E' ⟶ E)
      (π₂ : E' ⟶ c.pt) (hπ : IsPullback π₁ π₂ q (c.π.app k')) (γ : E' ⟶ Z.left),
      γ ≫ (g ≫ e.hom).left = pullback.lift (π₁ ≫ eE) π₂
        (by rw [Category.assoc, he, reassoc_of% hπ.w, c.w f]) ∧
      x ∈ Set.range (γ ≫ g.left) := by
    obtain ⟨Z, g, hg, z, hz⟩ := (Scheme.mem_smallEtaleTopology_iff R).1 hR x
    obtain ⟨k', f, E, hE, q, hq, eE, he, E', π₁, π₂, hπ, γ, -, hγ, ε, hε⟩ :=
      exists_etale_refinement_of_isLimit D c hc V'.hom (g ≫ e.hom).left z
    refine ⟨Z, g, hg, k', f, E, hE, q, hq, eE, he, E', π₁, π₂, hπ, γ, hγ, ε, ?_⟩
    rw [Scheme.Hom.comp_apply, hε, hz]
  choose Z g hg k' f E hE q hq eE he E' π₁ π₂ hπ γ hγ hx using hpt
  -- the images are open
  have hopen (x : W.left) : IsOpen (Set.range (γ x ≫ (g x).left)) := by
    have : AlgebraicGeometry.Etale (π₂ x) := MorphismProperty.of_isPullback (hπ x) (hq x)
    have hcomm : (γ x ≫ (g x).left) ≫ W.hom = π₂ x := by
      rw [Category.assoc, MorphismProperty.Over.w (g x),
        ← MorphismProperty.Over.w (g x ≫ e.hom), ← Category.assoc, hγ x]
      exact pullback.lift_snd _ _ _
    have : AlgebraicGeometry.Etale ((γ x ≫ (g x).left) ≫ W.hom) := by
      rw [hcomm]
      infer_instance
    have : AlgebraicGeometry.Etale (γ x ≫ (g x).left) := Etale.of_comp _ W.hom
    exact (γ x ≫ (g x).left).isOpenMap.isOpen_range
  -- finitely many suffice
  have hWc : CompactSpace W.left := by
    have : CompactSpace ((𝟭 Scheme).obj V'.left) := ‹CompactSpace V'.left›
    have : QuasiSeparatedSpace ((𝟭 Scheme).obj V'.left) := ‹QuasiSeparatedSpace V'.left›
    have := compactSpace_and_quasiSeparatedSpace_pullback_of_isAffineHom V'.hom (c.π.app m)
    exact (Scheme.compactSpace_and_quasiSeparatedSpace_of_iso e.symm this).1
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ Set.range (γ x ≫ (g x).left)) hopen
    (fun x _ ↦ Set.mem_iUnion.2 ⟨x, hx x⟩)
  let n := s.card
  let ι : Fin n ≃ s := s.equivFin.symm
  let xa : Fin n → W.left := fun a ↦ (ι a).1
  -- a common stage
  obtain ⟨K, h, gK, hgK⟩ := exists_comp_eq_of_finite_aux (fun a ↦ k' (xa a)) (fun a ↦ f (xa a))
  let V'' : (D.obj K).Etale := (D.map h).Etale.obj V'
  have : CompactSpace ((𝟭 Scheme).obj V'.left) := ‹CompactSpace V'.left›
  have : QuasiSeparatedSpace ((𝟭 Scheme).obj V'.left) := ‹QuasiSeparatedSpace V'.left›
  have hV'' := compactSpace_and_quasiSeparatedSpace_pullback_of_isAffineHom V'.hom (D.map h)
  have : CompactSpace V''.left := hV''.1
  have : QuasiSeparatedSpace V''.left := hV''.2
  let e' : W ≅ (c.π.app K).Etale.obj V'' :=
    e ≪≫ (MorphismProperty.Over.pullbackComp (c.π.app K) (D.map h) (c.π.app m) (c.w h).symm).app
      V'
  -- the family over `V''`
  let Ea (a : Fin n) : (D.obj K).Etale := Scheme.Etale.mk (pullback.snd (q (xa a)) (D.map (gK a)))
  have hEa (a : Fin n) : pullback.fst (q (xa a)) (D.map (gK a)) ≫ eE (xa a) ≫ V'.hom =
      pullback.snd (q (xa a)) (D.map (gK a)) ≫ D.map h := by
    rw [he, pullback.condition_assoc, ← D.map_comp, hgK]
  let U' (a : Fin n) : Over V'' := Over.mk (Y := Ea a)
    (MorphismProperty.Over.homMk (pullback.lift (pullback.fst _ _ ≫ eE (xa a))
      (pullback.snd _ _) (by rw [Category.assoc, hEa])) (pullback.lift_snd _ _ _))
  -- the base change of each member factors through a member of the sieve
  have hδ (a : Fin n) : ∃ δ : ((limitFamilyFunctor D c e').obj (U' a)).left ⟶ Z (xa a),
      δ ≫ g (xa a) = ((limitFamilyFunctor D c e').obj (U' a)).hom ∧
        Set.range (γ (xa a) ≫ (g (xa a)).left) ⊆
          Set.range ((limitFamilyFunctor D c e').obj (U' a)).hom.left := by
    set x := xa a
    have h₁ := IsPullback.of_hasPullback (Ea a).hom (c.π.app K)
    have h₂ := IsPullback.of_hasPullback (q x) (D.map (gK a))
    have hpaste : IsPullback (pullback.fst (Ea a).hom (c.π.app K) ≫
        pullback.fst (q x) (D.map (gK a))) (pullback.snd (Ea a).hom (c.π.app K)) (q x)
        (c.π.app (k' x)) := by
      have := h₁.paste_horiz h₂
      rwa [c.w] at this
    let φ := hpaste.isoIsPullback _ _ (hπ x)
    have hφ₂ : φ.hom ≫ π₂ x = pullback.snd (Ea a).hom (c.π.app K) :=
      IsPullback.isoIsPullback_hom_snd _ _ hpaste (hπ x)
    have hφ₁ : φ.hom ≫ π₁ x = pullback.fst (Ea a).hom (c.π.app K) ≫
        pullback.fst (q x) (D.map (gK a)) :=
      IsPullback.isoIsPullback_hom_fst _ _ hpaste (hπ x)
    have hw : (φ.hom ≫ γ x) ≫ (Z x).hom = ((limitFamilyFunctor D c e').obj (U' a)).left.hom := by
      rw [← MorphismProperty.Over.w (g x ≫ e.hom), Category.assoc, reassoc_of% (hγ x)]
      change φ.hom ≫ pullback.lift _ _ _ ≫ pullback.snd V'.hom (c.π.app m) = _
      rw [pullback.lift_snd]
      exact hφ₂
    let δ : ((limitFamilyFunctor D c e').obj (U' a)).left ⟶ Z x :=
      MorphismProperty.Over.homMk (φ.hom ≫ γ x) hw
    have hfac : δ ≫ g x = ((limitFamilyFunctor D c e').obj (U' a)).hom := by
      apply MorphismProperty.Over.Hom.ext
      rw [← cancel_mono e.hom.left]
      change (φ.hom ≫ γ x) ≫ (g x).left ≫ e.hom.left = _ ≫ e'.inv.left ≫ e.hom.left
      rw [Category.assoc, ← MorphismProperty.Comma.comp_left, hγ x]
      have he' : e'.inv.left ≫ e.hom.left =
          ((MorphismProperty.Over.pullbackComp (c.π.app K) (D.map h) (c.π.app m)
            (c.w h).symm).inv.app V').left := by
        simp [e', ← MorphismProperty.Comma.comp_left]
      rw [he']
      change _ = ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ (c.π.app K)).map
        (U' a).hom).left ≫ _
      apply pullback.hom_ext
      · simp [U', Ea, reassoc_of% hφ₁, Scheme.Hom.Etale,
          MorphismProperty.Over.pullback_map_left]
        erw [pullback.lift_fst_assoc, Category.assoc, pullback.lift_fst]
      · simp [U', Ea, hφ₂, Scheme.Hom.Etale,
          MorphismProperty.Over.pullback_map_left]
        erw [pullback.lift_snd]
    refine ⟨δ, hfac, ?_⟩
    rintro _ ⟨ε, rfl⟩
    refine ⟨φ.inv ε, ?_⟩
    rw [← hfac, MorphismProperty.Comma.comp_left]
    change (g x).left (γ x (φ.hom (φ.inv ε))) = (g x).left (γ x ε)
    rw [← Scheme.Hom.comp_apply φ.inv φ.hom, Iso.inv_hom_id]
    rfl
  refine ⟨n, K, V'', ‹_›, ‹_›, e', U', fun a ↦ ?_, fun a ↦ ?_, ?_⟩
  · have := hE (xa a)
    have : IsAffineHom (pullback.fst (q (xa a)) (D.map (gK a))) :=
      MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance
    exact isAffine_of_isAffineHom (pullback.fst (q (xa a)) (D.map (gK a)))
  · obtain ⟨δ, hδ₁, -⟩ := hδ a
    rw [← hδ₁]
    exact R.downward_closed (hg (xa a)) δ
  · refine Set.eq_univ_of_forall fun w ↦ ?_
    obtain ⟨x, hxs, hw⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ w))
    have hxa : xa (ι.symm ⟨x, hxs⟩) = x := by simp [xa]
    rw [← hxa] at hw
    exact Set.mem_iUnion.2 ⟨_, (hδ _).choose_spec.2 hw⟩

variable {R : Scheme.{u}} (π : D ⟶ (Functor.const J).obj R) (P : c.pt ⟶ R)
  (hP : ∀ j, P = c.π.app j ≫ π.app j)

include hP in
/-- **Inverse images of injective sheaves at a cofiltered limit are acyclic.** Let `X = lim Dⱼ`
be a cofiltered limit of quasi-compact quasi-separated schemes over a scheme `R`, with affine
transition maps, and let `G` be an abelian étale sheaf on `R` whose inverse images to all the
stages are injective (for instance an injective sheaf, if all the `Dⱼ ⟶ R` are étale). Then the
inverse image of `G` to `X` has no cohomology in positive degrees. -/
theorem subsingleton_H_succ_upperStar_of_isLimit (hc : IsLimit c)
    (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : ∀ j, Injective ((π.app j)^*[AddCommGrpCat.{u + 1}].obj G)) (q : ℕ) :
    Subsingleton (Sheaf.H ((P)^*[AddCommGrpCat.{u + 1}].obj G) (q + 1)) := by
  classical
  have hπaff (i : J) : IsAffineHom (c.π.app i) := isAffineHom_π_app D c hc i
  obtain ⟨m₀⟩ : Nonempty J := IsCofiltered.nonempty
  let T : c.pt.Etale := (c.π.app m₀).Etale.obj (Scheme.Etale.mk (𝟙 (D.obj m₀)))
  have hT : IsTerminal T :=
    IsTerminal.isTerminalObj _ _ (MorphismProperty.Over.mkIdTerminal _ (D.obj m₀))
  let B : c.pt.Etale → Prop := fun W ↦ ∃ (m : J) (V' : (D.obj m).Etale),
    CompactSpace V'.left ∧ QuasiSeparatedSpace V'.left ∧
      Nonempty (W ≅ (c.π.app m).Etale.obj V')
  let good : ∀ (W : c.pt.Etale) {n : ℕ}, (Fin n → Over W) → Prop := fun W n U ↦
    ∃ (m : J) (V' : (D.obj m).Etale) (e : W ≅ (c.π.app m).Etale.obj V')
      (U' : Fin n → Over V'), CompactSpace V'.left ∧ QuasiSeparatedSpace V'.left ∧
        (∀ a, IsAffine (U' a).left.left) ∧
        Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈
          c.pt.smallEtaleTopology W ∧
        U = fun a ↦ (limitFamilyFunctor D c e).obj (U' a)
  have hnerve {m : J} {V' : (D.obj m).Etale} [CompactSpace V'.left] [QuasiSeparatedSpace V'.left]
      {n : ℕ} (U' : Fin n → Over V') (hU' : ∀ a, IsAffine (U' a).left.left) (k : ℕ)
      (y : Fin (k + 1) → Fin n) :
      CompactSpace (cechNerveObj U' y).left.left ∧
        QuasiSeparatedSpace (cechNerveObj U' y).left.left :=
    Scheme.compactSpace_and_quasiSeparatedSpace_piObj _ fun l ↦
      have := hU' (y l)
      ⟨inferInstance, inferInstance⟩
  refine Sheaf.subsingleton_H_succ_of_exactAt_cechComplex_of_good hT B
    ⟨m₀, Scheme.Etale.mk (𝟙 _), inferInstanceAs (CompactSpace (D.obj m₀)),
      inferInstanceAs (QuasiSeparatedSpace (D.obj m₀)), ⟨Iso.refl _⟩⟩ good ?_ ?_ _ ?_ q
  · rintro W ⟨m, V', hV'c, hV'q, ⟨e⟩⟩ R hR
    obtain ⟨n, K, V'', h₁, h₂, e', U', hU'aff, hUR, hUcov⟩ := exists_limitFamily D c hc V' e R hR
    exact ⟨n, _, ⟨K, V'', e', U', h₁, h₂, hU'aff,
      (Scheme.ofArrows_mem_smallEtaleTopology_iff _).2 hUcov, rfl⟩, hUR⟩
  · rintro W - n U ⟨m, V', e, U', h₁, h₂, hU'aff, hcov, rfl⟩
    exact ⟨fun k y ↦ ⟨m, (cechNerveObj U' y).left, (hnerve U' hU'aff k y).1,
      (hnerve U' hU'aff k y).2,
      ⟨cechNerveObjMapIso _ _ (limitFamilyFunctorForgetIso D c e) U' y⟩⟩, hcov⟩
  · rintro W - n U ⟨m, V', e, U', h₁, h₂, hU'aff, -, rfl⟩ q
    rw [exactAt_cechComplex_map_iff (c.π.app m).Etale (limitFamilyFunctor D c e)
      (limitFamilyFunctorForgetIso D c e) U']
    -- the stages below `m`, as a system over `Dₘ`
    let π' : Over.forget m ⋙ D ⟶ (Functor.const (Over m)).obj (D.obj m) :=
      { app j := D.map j.hom
        naturality j k f := by simp [← D.map_comp, Over.w f] }
    have hP' (j : Over m) : c.π.app m = (c.whisker (Over.forget m)).π.app j ≫ π'.app j :=
      (c.w j.hom).symm
    have hc' : IsLimit (c.whisker (Over.forget m)) :=
      (Functor.Initial.isLimitWhiskerEquiv (Over.forget m) c).symm hc
    have (j : Over m) : CompactSpace ((Over.forget m ⋙ D).obj j) :=
      inferInstanceAs (CompactSpace (D.obj j.left))
    have (j : Over m) : QuasiSeparatedSpace ((Over.forget m ⋙ D).obj j) :=
      inferInstanceAs (QuasiSeparatedSpace (D.obj j.left))
    have {j k : Over m} (f : j ⟶ k) : IsAffineHom ((Over.forget m ⋙ D).map f) :=
      inferInstanceAs (IsAffineHom (D.map f.left))
    have hG' (j : Over m) {V : (D.obj m).Etale} {n : ℕ} (U : Fin n → Over V) (q : ℕ) :
        ((cechComplex U).obj ((π'.app j)_*[AddCommGrpCat.{u + 1}].obj
          ((π'.app j)^*[AddCommGrpCat.{u + 1}].obj
            ((π.app m)^*[AddCommGrpCat.{u + 1}].obj G))).obj).ExactAt (q + 1) := by
      have : Injective ((π'.app j)^*[AddCommGrpCat.{u + 1}].obj
          ((π.app m)^*[AddCommGrpCat.{u + 1}].obj G)) :=
        Injective.of_iso ((upperStarComp AddCommGrpCat.{u + 1} (D.map j.hom) (π.app m)
          (π.app j.left) (natTrans_app_eq_map_comp_app π j.hom)).app G) (hG j.left)
      have : Injective ((π'.app j)_*[AddCommGrpCat.{u + 1}].obj
          ((π'.app j)^*[AddCommGrpCat.{u + 1}].obj
            ((π.app m)^*[AddCommGrpCat.{u + 1}].obj G))) :=
        (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (π'.app j)).map_injective _
          inferInstance
      exact Sheaf.exactAt_cechComplex_of_injective _ U q
    have key := exactAt_cechComplex_lowerStar_upperStar_of_isLimit (Over.forget m ⋙ D) π'
      (c.whisker (Over.forget m)) (c.π.app m) hP' hc' ((π.app m)^*[AddCommGrpCat.{u + 1}].obj G)
      hG' U' (hnerve U' hU'aff) q
    exact key.of_iso ((cechComplex U').mapIso ((sheafToPresheaf _ _).mapIso
      ((c.π.app m)_*[AddCommGrpCat.{u + 1}].mapIso
        ((upperStarComp AddCommGrpCat.{u + 1} (c.π.app m) (π.app m) P (hP m)).app G).symm)))

end AlgebraicGeometry.Etale
