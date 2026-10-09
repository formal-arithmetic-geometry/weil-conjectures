/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# Torsors under a finite constant sheaf are representable

Let `Y` be a scheme and `M` a finite abelian group. A torsor `P` under the constant sheaf `M` on
the small étale site of `Y` whose underlying sheaf of sets is represented by a finite étale
`Y`-scheme `Q` comes from an `M`-torsor `Q ⟶ Y`
(`AlgebraicGeometry.Scheme.EtaleTorsor.exists_toSheafTorsor_equiv_of_iso`): the action of the
constant sections `m` of `M` on the identity section of `Q` defines the action of `M` on `Q`, and
the simple transitivity of the action on sections gives `∐_{m ∈ M} Q ≅ Q ×_Y Q`.

## Main statements

- `AlgebraicGeometry.Scheme.EtaleTorsor.exists_toSheafTorsor_equiv_of_iso`: a torsor under the
  constant sheaf `M` whose underlying sheaf is represented by a finite étale `Y`-scheme is the
  sheaf torsor of an `M`-torsor.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleTorsor

variable {M : Type (u + 1)} [AddCommGroup M] [Finite M] {Y : Scheme.{u}}

section Representable

variable [TopologicalSpace M] [DiscreteTopology M]

omit [AddCommGroup M] in
/-- A morphism `κ : Z ⟶ ∐_{m ∈ M} Q` is given on the open fibres of a continuous function
`a : Z → M` by morphisms into the summands. -/
lemma exists_fiberOpens_comp_sigmaι {Z Q : Scheme.{u}} (κ : Z ⟶ ∐ fun _ : M ↦ Q) :
    ∃ a : C(Z, M), ∀ m, ∃ k : (Z.fiberOpens a m).toScheme ⟶ Q,
      (Z.fiberOpens a m).ι ≫ κ = k ≫ Sigma.ι (fun _ : M ↦ Q) m := by
  have hκ (x : Z) : ∃ m y, Sigma.ι (fun _ : M ↦ Q) m y = κ x := by
    obtain ⟨m, y, hy⟩ := (sigmaOpenCover fun _ : M ↦ Q).exists_eq (κ x)
    exact ⟨m, y, hy⟩
  let a₀ (x : Z) : M := (hκ x).choose
  have ha₀ (x : Z) (m : M) (y : Q) (hy : Sigma.ι (fun _ : M ↦ Q) m y = κ x) : a₀ x = m := by
    obtain ⟨y', hy'⟩ := (hκ x).choose_spec
    exact congr_arg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).1 (hy'.trans hy.symm))
  have hfib (m : M) : a₀ ⁻¹' {m} = κ.base ⁻¹' Set.range (Sigma.ι (fun _ : M ↦ Q) m) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_range]
    refine ⟨fun hx ↦ ?_, fun ⟨y, hy⟩ ↦ ha₀ x m y hy⟩
    obtain ⟨y, hy⟩ := (hκ x).choose_spec
    exact ⟨y, hx ▸ hy⟩
  let a : C(Z, M) := ⟨a₀, (IsLocallyConstant.iff_isOpen_fiber.2 fun m ↦ by
    rw [hfib]
    exact (Sigma.ι (fun _ : M ↦ Q) m).isOpenEmbedding.isOpenMap.isOpen_range.preimage
      κ.base.hom.continuous).continuous⟩
  refine ⟨a, fun m ↦ ?_⟩
  have hrange : Set.range ((Z.fiberOpens a m).ι ≫ κ).base ⊆
      Set.range (Sigma.ι (fun _ : M ↦ Q) m).base := by
    rintro _ ⟨v, rfl⟩
    have hv : v.1 ∈ a₀ ⁻¹' {m} := v.2
    rw [hfib] at hv
    obtain ⟨y, hy⟩ := hv
    exact ⟨y, hy.trans (by rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply])⟩
  exact ⟨IsOpenImmersion.lift _ _ hrange, (IsOpenImmersion.lift_fac _ _ _).symm⟩

variable (R : Sheaf.Torsor (Etale.continuousMapSheaf Y M)) {Q : Scheme.{u}} (π : Q ⟶ Y)
  [Etale π] (e : R.sheaf ≅ Y.smallEtaleTopology.uliftYoneda.{u + 1}.obj (Etale.mk π))

/-- The action of a locally constant function on the `Y`-morphisms into `Q`, transported from
the torsor `R` along `e`. -/
noncomputable def reprAct {U : Y.Etale} (f : C(U.left, M)) (φ : U ⟶ Etale.mk π) :
    U ⟶ Etale.mk π :=
  (e.hom.hom.app (op U) (R.vadd (op U) f (e.inv.hom.app (op U) ⟨φ⟩))).down

omit [Finite M] in
lemma reprE_inv_hom {U : Y.Etaleᵒᵖ} (x : R.sheaf.obj.obj U) :
    e.inv.hom.app U (e.hom.hom.app U x) = x := by
  change ((sheafSections _ _).obj U).map (e.hom ≫ e.inv) x = x
  rw [e.hom_inv_id, CategoryTheory.Functor.map_id]
  rfl

omit [Finite M] in
lemma reprE_hom_inv {U : Y.Etaleᵒᵖ}
    (x : (Y.smallEtaleTopology.uliftYoneda.{u + 1}.obj (Etale.mk π)).obj.obj U) :
    e.hom.hom.app U (e.inv.hom.app U x) = x := by
  change ((sheafSections _ _).obj U).map (e.inv ≫ e.hom) x = x
  rw [e.inv_hom_id, CategoryTheory.Functor.map_id]
  rfl

omit [Finite M] in
lemma reprE_hom_map {U V : Y.Etale} (h : V ⟶ U) (x : R.sheaf.obj.obj (op U)) :
    e.hom.hom.app (op V) (R.sheaf.obj.map h.op x) = ⟨h ≫ (e.hom.hom.app (op U) x).down⟩ := by
  have := ConcreteCategory.congr_hom (e.hom.hom.naturality h.op) x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
  exact this

omit [Finite M] in
lemma reprE_inv_map {U V : Y.Etale} (h : V ⟶ U) (φ : U ⟶ Etale.mk π) :
    e.inv.hom.app (op V) ⟨h ≫ φ⟩ = R.sheaf.obj.map h.op (e.inv.hom.app (op U) ⟨φ⟩) := by
  have := ConcreteCategory.congr_hom (e.inv.hom.naturality h.op) ⟨φ⟩
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
  exact this

omit [Finite M] in
lemma comp_reprAct {U V : Y.Etale} (h : V ⟶ U) (f : C(U.left, M)) (φ : U ⟶ Etale.mk π) :
    h ≫ reprAct R π e f φ = reprAct R π e (f.comp h.left.base.hom) (h ≫ φ) := by
  rw [reprAct, reprAct, reprE_inv_map]
  have h₁ := R.map_vadd h.op f (e.inv.hom.app (op U) ⟨φ⟩)
  change _ = R.vadd (op V) (f.comp h.left.base.hom) _ at h₁
  rw [← h₁, reprE_hom_map]

/-- The action of the element `m` on `Q`. -/
noncomputable def reprVadd (m : M) : Q ⟶ Q :=
  (reprAct R π e (ContinuousMap.const _ m) (𝟙 (Etale.mk π))).left

omit [Finite M] in
lemma reprAct_const {U : Y.Etale} (m : M) (φ : U ⟶ Etale.mk π) :
    reprAct R π e (ContinuousMap.const _ m) φ =
      φ ≫ reprAct R π e (ContinuousMap.const _ m) (𝟙 (Etale.mk π)) := by
  rw [comp_reprAct, Category.comp_id]
  rfl

omit [Finite M] in
lemma reprAct_left {U : Y.Etale} (f : C(U.left, M)) (φ : U ⟶ Etale.mk π) :
    (reprAct R π e f φ).left =
      U.left.glueOfContinuousMap f fun m ↦ φ.left ≫ reprVadd R π e m := by
  refine U.left.hom_ext_fiberOpens f fun m ↦ ?_
  rw [Scheme.fiberOpens_ι_glueOfContinuousMap]
  let W : Y.Etale := Etale.mk ((U.left.fiberOpens f m).ι ≫ U.hom)
  let ι : W ⟶ U := MorphismProperty.Over.homMk (U.left.fiberOpens f m).ι rfl
  have hf : f.comp ι.left.base.hom = ContinuousMap.const _ m :=
    ContinuousMap.ext fun x ↦ x.2
  have h := congr_arg (fun χ : W ⟶ Etale.mk π ↦ χ.left) (comp_reprAct R π e ι f φ)
  rw [hf, reprAct_const] at h
  exact h

omit [Finite M] in
lemma reprVadd_π (m : M) : reprVadd R π e m ≫ π = π :=
  MorphismProperty.Over.w (reprAct R π e (ContinuousMap.const _ m) (𝟙 (Etale.mk π)))

omit [Finite M] in
lemma reprVadd_zero : reprVadd R π e 0 = 𝟙 Q := by
  have h₀ : (ContinuousMap.const (Etale.mk π).left (0 : M)) = 0 := rfl
  have h : reprAct R π e (ContinuousMap.const _ 0) (𝟙 (Etale.mk π)) = 𝟙 _ := by
    rw [reprAct, h₀]
    erw [R.zero_vadd]
    rw [reprE_hom_inv]
  exact congr_arg (fun χ : Etale.mk π ⟶ Etale.mk π ↦ χ.left) h

omit [Finite M] in
lemma reprVadd_add (m n : M) : reprVadd R π e (m + n) = reprVadd R π e m ≫ reprVadd R π e n := by
  have h₀ : (ContinuousMap.const (Etale.mk π).left (m + n)) =
      ContinuousMap.const _ n + ContinuousMap.const _ m :=
    ContinuousMap.ext fun _ ↦ add_comm m n
  have h : reprAct R π e (ContinuousMap.const _ (m + n)) (𝟙 (Etale.mk π)) =
      reprAct R π e (ContinuousMap.const _ n)
        (reprAct R π e (ContinuousMap.const _ m) (𝟙 (Etale.mk π))) := by
    rw [reprAct, h₀]
    erw [R.add_vadd]
    rw [reprAct, reprAct]
    simp only [ULift.up_down, reprE_inv_hom]
  rw [reprAct_const R π e n] at h
  exact congr_arg (fun χ : Etale.mk π ⟶ Etale.mk π ↦ χ.left) h

/-- The comparison map `∐_{m ∈ M} Q ⟶ Q ×_Y Q`, `(m, q) ↦ (m • q, q)`. -/
noncomputable abbrev reprSigmaDesc : (∐ fun _ : M ↦ Q) ⟶ pullback π π :=
  Sigma.desc fun m ↦ pullback.lift (reprVadd R π e m) (𝟙 Q) (by simp [reprVadd_π])

omit [Finite M] in
/-- The action of `M` on `Q` is free on every nonempty étale `Y`-scheme. -/
lemma eq_of_reprVadd {V : Y.Etale} (κ : V ⟶ Etale.mk π) {m m' : M}
    (h : κ.left ≫ reprVadd R π e m = κ.left ≫ reprVadd R π e m') (v : V.left) : m = m' := by
  have h₁ : reprAct R π e (ContinuousMap.const _ m) κ =
      reprAct R π e (ContinuousMap.const _ m') κ := by
    refine etaleHom_ext ?_
    rw [reprAct_const R π e m κ, reprAct_const R π e m' κ]
    exact h
  have h₂ : e.hom.hom.app (op V) (R.vadd (op V) (ContinuousMap.const _ m)
        (e.inv.hom.app (op V) ⟨κ⟩)) =
      e.hom.hom.app (op V) (R.vadd (op V) (ContinuousMap.const _ m')
        (e.inv.hom.app (op V) ⟨κ⟩)) :=
    ULift.ext _ _ h₁
  have h₂' := congr_arg (fun z ↦ e.inv.hom.app (op V) z) h₂
  simp only [reprE_inv_hom] at h₂'
  have h₃ := (R.bijective_vadd (op V) (e.inv.hom.app (op V) ⟨κ⟩)).1 h₂'
  exact congr_arg (fun f : C(V.left, M) ↦ f v) h₃

omit [Finite M] in
include R e in
lemma surjective_of_representable : Surjective π := by
  refine ⟨fun y ↦ ?_⟩
  obtain ⟨V, g, ⟨x⟩, v, hv⟩ :=
    (mem_smallEtaleTopology_iff _).1 (R.nonemptySieve_mem (Etale.mk (𝟙 Y))) y
  let φ := (e.hom.hom.app (op V) x).down
  refine ⟨φ.left v, ?_⟩
  have h₁ : φ.left ≫ π = V.hom := MorphismProperty.Over.w φ
  have h₂ : g.left ≫ 𝟙 Y = V.hom := MorphismProperty.Over.w g
  rw [← hv]
  refine (Scheme.Hom.comp_apply φ.left π v).symm.trans ?_
  rw [h₁, ← h₂]
  erw [Category.comp_id]
  rfl

theorem isIso_reprSigmaDesc : IsIso (reprSigmaDesc R π e) := by
  have : Etale (Sigma.desc fun _ : M ↦ π) :=
    IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  let E₁ : Y.Etale := Etale.mk (Sigma.desc fun _ : M ↦ π)
  let E₂ : Y.Etale := Etale.mk (pullback.fst π π ≫ π)
  let D : E₁ ⟶ E₂ := MorphismProperty.Over.homMk (reprSigmaDesc R π e)
    (Sigma.hom_ext _ _ fun m ↦ by simp [reprSigmaDesc, reprVadd_π, E₂, E₁])
  have hD : IsIso D := by
    refine isIso_of_yoneda_map_bijective D fun T ↦ ⟨fun x x' hxx ↦ ?_, fun g ↦ ?_⟩
    · obtain ⟨a, ha⟩ := exists_fiberOpens_comp_sigmaι x.left
      obtain ⟨a', ha'⟩ := exists_fiberOpens_comp_sigmaι x'.left
      refine etaleHom_ext (T.left.hom_ext_fiberOpens (a.prodMk a') fun ⟨m, m'⟩ ↦ ?_)
      let V := T.left.fiberOpens (a.prodMk a') (m, m')
      have h₁ : V ≤ T.left.fiberOpens a m := fun y hy ↦ (Prod.ext_iff.1 hy).1
      have h₂ : V ≤ T.left.fiberOpens a' m' := fun y hy ↦ (Prod.ext_iff.1 hy).2
      obtain ⟨k, hk⟩ := ha m
      obtain ⟨k', hk'⟩ := ha' m'
      have e₁ : V.ι ≫ x.left = (T.left.homOfLE h₁ ≫ k) ≫ Sigma.ι (fun _ : M ↦ Q) m := by
        rw [← T.left.homOfLE_ι h₁, Category.assoc, hk, Category.assoc]
      have e₂ : V.ι ≫ x'.left = (T.left.homOfLE h₂ ≫ k') ≫ Sigma.ι (fun _ : M ↦ Q) m' := by
        rw [← T.left.homOfLE_ι h₂, Category.assoc, hk', Category.assoc]
      have hxD : V.ι ≫ x.left ≫ reprSigmaDesc R π e = V.ι ≫ x'.left ≫ reprSigmaDesc R π e :=
        congr_arg (fun χ : T ⟶ E₂ ↦ V.ι ≫ χ.left) hxx
      simp only [← Category.assoc] at hxD
      rw [e₁, e₂] at hxD
      simp only [Category.assoc, Sigma.ι_desc] at hxD
      have hsnd := congr_arg (· ≫ pullback.snd π π) hxD
      have hfst := congr_arg (· ≫ pullback.fst π π) hxD
      simp only [Category.assoc, pullback.lift_snd, pullback.lift_fst, Category.comp_id] at hsnd hfst
      by_cases hV : IsEmpty V.toScheme
      · exact isInitialOfIsEmpty.hom_ext _ _
      · obtain ⟨v⟩ := not_isEmpty_iff.1 hV
        have hκ : (T.left.homOfLE h₁ ≫ k) ≫ π = V.ι ≫ T.hom := by
          have := congr_arg (· ≫ Sigma.desc fun _ : M ↦ π) e₁
          simp only [Category.assoc, Sigma.ι_desc] at this
          rw [Category.assoc, ← this]
          exact congr_arg _ (MorphismProperty.Over.w x)
        let W : Y.Etale := Etale.mk (V.ι ≫ T.hom)
        let κ : W ⟶ Etale.mk π := MorphismProperty.Over.homMk (T.left.homOfLE h₁ ≫ k) hκ
        have hmm : m = m' := eq_of_reprVadd R π e κ (by
          change (T.left.homOfLE h₁ ≫ k) ≫ reprVadd R π e m =
            (T.left.homOfLE h₁ ≫ k) ≫ reprVadd R π e m'
          rw [Category.assoc, Category.assoc, hfst, ← Category.assoc, ← hsnd,
            Category.assoc]) v
        subst hmm
        rw [e₁, e₂, hsnd]
    · let φe : T ⟶ Etale.mk π := MorphismProperty.Over.homMk (g.left ≫ pullback.fst π π) (by
        rw [Category.assoc]
        exact MorphismProperty.Over.w g)
      let ψe : T ⟶ Etale.mk π := MorphismProperty.Over.homMk (g.left ≫ pullback.snd π π) (by
        change g.left ≫ pullback.snd π π ≫ π = T.hom
        rw [← pullback.condition, ← Category.assoc]
        exact MorphismProperty.Over.w g)
      obtain ⟨f, hf⟩ := (R.bijective_vadd (op T) (e.inv.hom.app (op T) ⟨ψe⟩)).2
        (e.inv.hom.app (op T) ⟨φe⟩)
      have hact : reprAct R π e f ψe = φe := by
        have := congr_arg (fun z ↦ (e.hom.hom.app (op T) z).down) hf
        simp only [reprE_hom_inv] at this
        exact this
      have hglue := reprAct_left R π e f ψe
      rw [hact] at hglue
      refine ⟨MorphismProperty.Over.homMk
        (T.left.glueOfContinuousMap f fun m ↦ ψe.left ≫ Sigma.ι (fun _ : M ↦ Q) m) ?_,
        etaleHom_ext ?_⟩
      · change T.left.glueOfContinuousMap f _ ≫ Sigma.desc (fun _ : M ↦ π) = T.hom
        rw [Scheme.glueOfContinuousMap_comp]
        refine Scheme.glueOfContinuousMap_eq fun m ↦ ?_
        rw [Category.assoc, Sigma.ι_desc]
        exact congr_arg _ (MorphismProperty.Over.w ψe)
      · change T.left.glueOfContinuousMap f _ ≫ reprSigmaDesc R π e = g.left
        refine pullback.hom_ext ?_ ?_
        · rw [Category.assoc, Scheme.glueOfContinuousMap_comp]
          change _ = φe.left
          rw [hglue]
          congr 1
          funext m
          simp [reprSigmaDesc]
        · rw [Category.assoc, Scheme.glueOfContinuousMap_comp]
          change _ = ψe.left
          refine Scheme.glueOfContinuousMap_eq fun m ↦ ?_
          simp only [reprSigmaDesc, Category.assoc, Sigma.ι_desc_assoc, pullback.lift_snd]
          erw [Category.comp_id]
  exact (Etale.forget Y ⋙ Over.forget Y).map_isIso D

variable [IsFinite π]

/-- **The `M`-torsor of a representable torsor.** A torsor `R` under the sheaf of locally constant
`M`-valued functions whose underlying sheaf is represented by a finite étale `Q ⟶ Y`, through
`e`, makes `Q` an `M`-torsor: `m` acts on `Q` as the constant section `m` acts on the identity
section of `Q`. -/
noncomputable def ofRepresentable : EtaleTorsor M Y where
  P := Q
  π := π
  surjective := surjective_of_representable R π e
  vadd := reprVadd R π e
  vadd_π := reprVadd_π R π e
  zero_vadd := reprVadd_zero R π e
  add_vadd := reprVadd_add R π e
  isIso_sigmaDesc := isIso_reprSigmaDesc R π e

/-- The sheaf torsor of `ofRepresentable R π e` is `R`. -/
lemma toSheafTorsorContinuousMap_ofRepresentable_equiv :
    (ofRepresentable R π e).toSheafTorsorContinuousMap ≈ R := by
  refine ⟨⟨e.symm, fun U f x ↦ ?_⟩⟩
  obtain ⟨φ⟩ := x
  have hφ : (ofRepresentable R π e).smulHom f φ = reprAct R π e f φ :=
    etaleHom_ext ((smulHom_left _ f φ).trans (reprAct_left R π e f φ).symm)
  change e.inv.hom.app U ⟨(ofRepresentable R π e).smulHom f φ⟩ = R.vadd U f (e.inv.hom.app U ⟨φ⟩)
  rw [hφ, reprAct]
  simp only [ULift.up_down, reprE_inv_hom]

end Representable

/-- **Torsors with a representable underlying sheaf.** A torsor `P` under the constant sheaf `M`
on the small étale site of `Y` whose underlying sheaf of sets is represented by a finite étale
`Y`-scheme `Q` is the sheaf torsor of an `M`-torsor, with total space `Q`.
(blueprint: `thm-galois-lc-etale`, simply transitive actions) -/
theorem exists_toSheafTorsor_equiv_of_iso
    (P : Sheaf.Torsor ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of M))) {Q : Scheme.{u}} (π : Q ⟶ Y) [IsFinite π] [Etale π]
    (e : P.sheaf ≅ Y.smallEtaleTopology.uliftYoneda.{u + 1}.obj (Etale.mk π)) :
    ∃ t : EtaleTorsor M Y, t.toSheafTorsor ≈ P := by
  let _ : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  let i := Etale.constantSheafIsoContinuousMapSheaf Y M
  let R := Sheaf.Torsor.ofIso i P
  refine ⟨ofRepresentable R π e, Setoid.trans ?_ (Sheaf.Torsor.ofIso_symm_ofIso_equiv i P)⟩
  exact (Sheaf.Torsor.ofIso_equiv_ofIso_iff i.symm).2
    (toSheafTorsorContinuousMap_ofRepresentable_equiv R π e)

end AlgebraicGeometry.Scheme.EtaleTorsor
