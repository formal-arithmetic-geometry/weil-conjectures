/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# The torsor of lifts along a morphism of schemes

Let `P ⟶ Y` be an `M`-torsor and `f : Y' ⟶ Y` a morphism of schemes. The `Y`-morphisms
`U ⟶ P` lifting `U ⟶ Y' ⟶ Y`, for `U` étale over `Y'`, form a torsor on the small étale site of
`Y'` under the sheaf `U ↦ C(U, M)` of locally constant functions: it is the functor of points of
the base change `P ×_Y Y' ⟶ Y'`, on which a locally constant function `a : U → M` acts by `m` on
the open fibre `a⁻¹(m)`. Its global sections are the lifts of `f` to `P`.

## Main definitions

- `AlgebraicGeometry.Scheme.Etale.glueHom`: the morphism of the small étale site which is
  `g m` on the open fibre `a⁻¹(m)` of a continuous function `a` to a discrete space.
- `AlgebraicGeometry.Scheme.EtaleTorsor.pullbackSheafTorsor`: the torsor of lifts of `f` to `P`.

## Main statements

- `AlgebraicGeometry.Scheme.EtaleTorsor.nonempty_pullbackSheafTorsor_iff`: the torsor of lifts
  has a global section if and only if `f` lifts to `P`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

/-! ### Gluing morphisms of the small étale site along a locally constant function -/

section Glue

variable {M : Type*} [TopologicalSpace M] [DiscreteTopology M] {X : Scheme.{u}}

/-- For a continuous function `a : U → M` to a discrete space and morphisms `g m : U ⟶ W` of the
small étale site, the morphism `U ⟶ W` which is `g m` on the open fibre `a⁻¹(m)`. -/
noncomputable def Etale.glueHom {U W : X.Etale} (a : C(U.left, M)) (g : M → (U ⟶ W)) :
    U ⟶ W :=
  MorphismProperty.Over.homMk (U.left.glueOfContinuousMap a fun m ↦ (g m).left) (by
    rw [Scheme.glueOfContinuousMap_comp]
    exact Scheme.glueOfContinuousMap_eq fun m ↦
      congr_arg ((U.left.fiberOpens a m).ι ≫ ·) (MorphismProperty.Over.w (g m)))

lemma Etale.glueHom_left {U W : X.Etale} (a : C(U.left, M)) (g : M → (U ⟶ W)) :
    (Etale.glueHom a g).left = U.left.glueOfContinuousMap a fun m ↦ (g m).left :=
  rfl

lemma Etale.ι_glueHom_left_of_le {U W : X.Etale} (a : C(U.left, M)) (g : M → (U ⟶ W))
    {V : U.left.Opens} {m : M} (hV : V ≤ U.left.fiberOpens a m) :
    V.ι ≫ (Etale.glueHom a g).left = V.ι ≫ (g m).left := by
  rw [Etale.glueHom_left, ← U.left.homOfLE_ι hV, Category.assoc,
    Scheme.fiberOpens_ι_glueOfContinuousMap, ← Category.assoc, Scheme.homOfLE_ι]

lemma Etale.glueHom_const {U W : X.Etale} (c : M) (g : M → (U ⟶ W)) :
    Etale.glueHom (ContinuousMap.const _ c) g = g c := by
  refine EtaleTorsor.etaleHom_ext (Scheme.glueOfContinuousMap_eq fun m ↦ ?_)
  by_cases hm : c = m
  · rw [hm]
  · have : IsEmpty (U.left.fiberOpens (ContinuousMap.const _ c) m).toScheme :=
      ⟨fun x ↦ hm x.2⟩
    exact isInitialOfIsEmpty.hom_ext _ _

lemma Etale.comp_glueHom {U V W : X.Etale} (h : V ⟶ U) (a : C(U.left, M))
    (g : M → (U ⟶ W)) :
    h ≫ Etale.glueHom a g = Etale.glueHom (a.comp h.left.base.hom) fun m ↦ h ≫ g m := by
  refine EtaleTorsor.etaleHom_ext ?_
  change h.left ≫ U.left.glueOfContinuousMap a _ =
    V.left.glueOfContinuousMap _ fun m ↦ (h ≫ g m).left
  rw [Scheme.comp_glueOfContinuousMap]
  rfl

/-- The open fibre `a⁻¹(m)` of a continuous function `a : U → M` on an object `U` of the small
étale site, as an object of the small étale site. -/
noncomputable abbrev Etale.fiber {U : X.Etale} (a : C(U.left, M)) (m : M) : X.Etale :=
  Etale.mk ((U.left.fiberOpens a m).ι ≫ U.hom)

/-- The inclusion of the open fibre `a⁻¹(m)` into `U`. -/
noncomputable def Etale.fiberι {U : X.Etale} (a : C(U.left, M)) (m : M) :
    Etale.fiber a m ⟶ U :=
  MorphismProperty.Over.homMk (U.left.fiberOpens a m).ι rfl

lemma Etale.fiberι_left {U : X.Etale} (a : C(U.left, M)) (m : M) :
    (Etale.fiberι a m).left = (U.left.fiberOpens a m).ι :=
  rfl

end Glue

namespace EtaleTorsor

variable {M : Type (u + 1)} [AddCommGroup M] [Finite M] {Y : Scheme.{u}}

/-- The action of `m` on a torsor, as an endomorphism of its total space in the small étale
site. -/
noncomputable def vaddEtale (t : EtaleTorsor M Y) (m : M) : t.toEtale ⟶ t.toEtale :=
  MorphismProperty.Over.homMk (t.vadd m) (t.vadd_π m)

lemma vaddEtale_left (t : EtaleTorsor M Y) (m : M) : (t.vaddEtale m).left = t.vadd m :=
  rfl

lemma vaddEtale_zero (t : EtaleTorsor M Y) : t.vaddEtale 0 = 𝟙 _ :=
  etaleHom_ext t.zero_vadd

lemma vaddEtale_add (t : EtaleTorsor M Y) (m n : M) :
    t.vaddEtale (m + n) = t.vaddEtale m ≫ t.vaddEtale n :=
  etaleHom_ext (t.add_vadd m n)

variable [TopologicalSpace M] [DiscreteTopology M]

/-- Two morphisms `φ, ψ : Z ⟶ P` to the total space of a torsor which agree over `Y` differ by
a locally constant function `a : Z → M`: `ψ` is `φ` followed by the action of `m` on the open
fibre `a⁻¹(m)`. -/
lemma exists_glueOfContinuousMap_eq (t : EtaleTorsor M Y) {Z : Scheme.{u}} (φ ψ : Z ⟶ t.P)
    (hφψ : ψ ≫ t.π = φ ≫ t.π) :
    ∃ a : C(Z, M), Z.glueOfContinuousMap a (fun m ↦ φ ≫ t.vadd m) = ψ := by
  have := t.isIso_sigmaDesc
  let D := Sigma.desc fun m : M ↦ pullback.lift (f := t.π) (g := t.π) (t.vadd m) (𝟙 t.P)
    (by simp [t.vadd_π])
  let χ : Z ⟶ pullback t.π t.π := pullback.lift ψ φ hφψ
  let κ : Z ⟶ ∐ fun _ : M ↦ t.P := χ ≫ inv D
  have hκ (x : Z) : ∃ m y, Sigma.ι (fun _ : M ↦ t.P) m y = κ x := by
    obtain ⟨m, y, hy⟩ := (sigmaOpenCover fun _ : M ↦ t.P).exists_eq (κ x)
    exact ⟨m, y, hy⟩
  let a₀ (x : Z) : M := (hκ x).choose
  have ha₀ (x : Z) (m : M) (y : t.P) (hy : Sigma.ι (fun _ : M ↦ t.P) m y = κ x) :
      a₀ x = m := by
    obtain ⟨y', hy'⟩ := (hκ x).choose_spec
    exact congr_arg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).1 (hy'.trans hy.symm))
  have hfib (m : M) : a₀ ⁻¹' {m} = κ.base ⁻¹' Set.range (Sigma.ι (fun _ : M ↦ t.P) m) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_range]
    refine ⟨fun hx ↦ ?_, fun ⟨y, hy⟩ ↦ ha₀ x m y hy⟩
    obtain ⟨y, hy⟩ := (hκ x).choose_spec
    exact ⟨y, hx ▸ hy⟩
  let a : C(Z, M) := ⟨a₀, (IsLocallyConstant.iff_isOpen_fiber.2 fun m ↦ by
    rw [hfib]
    exact (Sigma.ι (fun _ : M ↦ t.P) m).isOpenEmbedding.isOpenMap.isOpen_range.preimage
      κ.base.hom.continuous).continuous⟩
  refine ⟨a, Scheme.glueOfContinuousMap_eq fun m ↦ ?_⟩
  let V := Z.fiberOpens a m
  have hrange : Set.range (V.ι ≫ κ).base ⊆ Set.range (Sigma.ι (fun _ : M ↦ t.P) m).base := by
    rintro _ ⟨v, rfl⟩
    have hv : v.1 ∈ a₀ ⁻¹' {m} := v.2
    rw [hfib] at hv
    obtain ⟨y, hy⟩ := hv
    exact ⟨y, hy.trans (Scheme.Hom.comp_apply _ _ _).symm⟩
  let k : V.toScheme ⟶ t.P := IsOpenImmersion.lift (Sigma.ι (fun _ : M ↦ t.P) m) _ hrange
  have hk : V.ι ≫ χ = pullback.lift (k ≫ t.vadd m) k (by simp [t.vadd_π]) := by
    have : V.ι ≫ κ = k ≫ Sigma.ι (fun _ : M ↦ t.P) m := (IsOpenImmersion.lift_fac _ _ _).symm
    rw [← vadd_comp_sigmaDesc t k m, ← Category.assoc k, ← this]
    simp [κ, D]
  have h₁ := congr_arg (· ≫ pullback.fst t.π t.π) hk
  have h₂ := congr_arg (· ≫ pullback.snd t.π t.π) hk
  simp only [Category.assoc, χ, pullback.lift_fst, pullback.lift_snd] at h₁ h₂
  rw [← Category.assoc, h₂, h₁]

/-! ### The torsor of lifts along a morphism `f : Y' ⟶ Y` -/

section PullbackTorsor

variable {Y' : Scheme.{u}} (f : Y' ⟶ Y) (t : EtaleTorsor M Y)

/-- The base change `P ×_Y Y' ⟶ Y'` of the total space of a torsor, as an object of the small
étale site of `Y'`. -/
noncomputable abbrev pullbackEtale : Y'.Etale :=
  f.Etale.obj t.toEtale

/-- The action of `m` on the base change `P ×_Y Y'`. -/
noncomputable abbrev pullbackVadd (m : M) : t.pullbackEtale f ⟶ t.pullbackEtale f :=
  f.Etale.map (t.vaddEtale m)

/-- The action of a locally constant function `a : U → M` on a morphism `φ : U ⟶ P ×_Y Y'`
of the small étale site of `Y'`: on the fibre `a⁻¹(m)` it is `φ` followed by the action of
`m`. -/
noncomputable def pullbackSmulHom {U : Y'.Etale} (a : C(U.left, M))
    (φ : U ⟶ t.pullbackEtale f) : U ⟶ t.pullbackEtale f :=
  Etale.glueHom a fun m ↦ φ ≫ t.pullbackVadd f m

omit [TopologicalSpace M] [DiscreteTopology M] in
lemma pullbackVadd_left_fst (m : M) :
    (t.pullbackVadd f m).left ≫ pullback.fst t.π f = pullback.fst t.π f ≫ t.vadd m :=
  Hom.etale_map_left_comp_fst f (t.vaddEtale m)

omit [TopologicalSpace M] [DiscreteTopology M] in
lemma pullbackVadd_left_snd (m : M) :
    (t.pullbackVadd f m).left ≫ pullback.snd t.π f = pullback.snd t.π f :=
  Hom.etale_map_left_comp_snd f (t.vaddEtale m)

omit [TopologicalSpace M] [DiscreteTopology M] in
lemma pullbackVadd_add (m n : M) :
    t.pullbackVadd f (m + n) = t.pullbackVadd f m ≫ t.pullbackVadd f n := by
  rw [pullbackVadd, vaddEtale_add, Functor.map_comp]

lemma pullbackSmulHom_const {U : Y'.Etale} (c : M) (φ : U ⟶ t.pullbackEtale f) :
    t.pullbackSmulHom f (ContinuousMap.const _ c) φ = φ ≫ t.pullbackVadd f c :=
  Etale.glueHom_const c _

omit [TopologicalSpace M] [DiscreteTopology M] in
lemma pullbackVadd_zero : t.pullbackVadd f 0 = 𝟙 _ := by
  rw [pullbackVadd, vaddEtale_zero, CategoryTheory.Functor.map_id]

lemma ι_pullbackSmulHom_left_of_le {U : Y'.Etale} (a : C(U.left, M))
    (φ : U ⟶ t.pullbackEtale f) {V : U.left.Opens} {m : M} (hV : V ≤ U.left.fiberOpens a m) :
    V.ι ≫ (t.pullbackSmulHom f a φ).left = V.ι ≫ φ.left ≫ (t.pullbackVadd f m).left :=
  Etale.ι_glueHom_left_of_le a _ hV

lemma pullbackSmulHom_add {U : Y'.Etale} (a b : C(U.left, M)) (φ : U ⟶ t.pullbackEtale f) :
    t.pullbackSmulHom f (a + b) φ = t.pullbackSmulHom f a (t.pullbackSmulHom f b φ) := by
  refine etaleHom_ext ?_
  refine U.left.hom_ext_fiberOpens (a.prodMk b) fun ⟨m, n⟩ ↦ ?_
  have ha : U.left.fiberOpens (a.prodMk b) (m, n) ≤ U.left.fiberOpens a m :=
    fun x hx ↦ (Prod.ext_iff.1 hx).1
  have hb : U.left.fiberOpens (a.prodMk b) (m, n) ≤ U.left.fiberOpens b n :=
    fun x hx ↦ (Prod.ext_iff.1 hx).2
  have hab : U.left.fiberOpens (a.prodMk b) (m, n) ≤ U.left.fiberOpens (a + b) (m + n) :=
    fun x hx ↦ by
      have h₁ : a x = m := ha hx
      have h₂ : b x = n := hb hx
      change a x + b x = m + n
      rw [h₁, h₂]
  rw [ι_pullbackSmulHom_left_of_le f t _ _ hab, ι_pullbackSmulHom_left_of_le f t _ _ ha,
    reassoc_of% (ι_pullbackSmulHom_left_of_le f t b φ hb), add_comm, pullbackVadd_add,
    MorphismProperty.Comma.comp_left]

lemma comp_pullbackSmulHom {U V : Y'.Etale} (h : V ⟶ U) (a : C(U.left, M))
    (φ : U ⟶ t.pullbackEtale f) :
    h ≫ t.pullbackSmulHom f a φ = t.pullbackSmulHom f (a.comp h.left.base.hom) (h ≫ φ) := by
  rw [pullbackSmulHom, pullbackSmulHom, Etale.comp_glueHom]
  simp only [Category.assoc]

/-- The action of `M` on lifts is simply transitive. -/
lemma bijective_pullbackSmulHom {U : Y'.Etale} (φ : U ⟶ t.pullbackEtale f) :
    Function.Bijective fun a : C(U.left, M) ↦ t.pullbackSmulHom f a φ := by
  refine ⟨fun a b hab ↦ ContinuousMap.ext fun x ↦ ?_, fun ψ ↦ ?_⟩
  · let W := U.left.fiberOpens (a.prodMk b) (a x, b x)
    have ha : W ≤ U.left.fiberOpens a (a x) := fun y hy ↦ (Prod.ext_iff.1 hy).1
    have hb : W ≤ U.left.fiberOpens b (b x) := fun y hy ↦ (Prod.ext_iff.1 hy).2
    have h := congr_arg (fun χ : U ⟶ t.pullbackEtale f ↦ W.ι ≫ χ.left ≫ pullback.fst t.π f) hab
    simp only at h
    rw [← Category.assoc, ← Category.assoc, ι_pullbackSmulHom_left_of_le f t _ _ ha,
      ι_pullbackSmulHom_left_of_le f t _ _ hb, Category.assoc, Category.assoc, Category.assoc,
      Category.assoc, pullbackVadd_left_fst, pullbackVadd_left_fst] at h
    exact t.eq_of_comp_vadd_eq ((W.ι ≫ φ.left) ≫ pullback.fst t.π f)
      (by simpa only [Category.assoc] using h) ⟨x, rfl⟩
  · obtain ⟨a, ha⟩ := t.exists_glueOfContinuousMap_eq (φ.left ≫ pullback.fst t.π f)
      (ψ.left ≫ pullback.fst t.π f) (by
        rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc,
          ← Category.assoc]
        congr 1
        exact (MorphismProperty.Over.w ψ).trans (MorphismProperty.Over.w φ).symm)
    have hfst : pullback.fst t.toEtale.hom f = pullback.fst t.π f := rfl
    have hsnd : pullback.snd t.toEtale.hom f = pullback.snd t.π f := rfl
    refine ⟨a, etaleHom_ext (pullback.hom_ext ?_ ?_)⟩
    · rw [hfst]
      refine U.left.hom_ext_fiberOpens a fun m ↦ ?_
      rw [← Category.assoc, ι_pullbackSmulHom_left_of_le f t _ _ le_rfl, Category.assoc,
        Category.assoc, pullbackVadd_left_fst, ← ha, Scheme.fiberOpens_ι_glueOfContinuousMap]
      simp only [Category.assoc]
    · rw [hsnd]
      refine U.left.hom_ext_fiberOpens a fun m ↦ ?_
      rw [← Category.assoc, ι_pullbackSmulHom_left_of_le f t _ _ le_rfl, Category.assoc,
        Category.assoc, pullbackVadd_left_snd]
      congr 1
      exact (MorphismProperty.Over.w φ).trans (MorphismProperty.Over.w ψ).symm

/-- **The torsor of lifts.** For an `M`-torsor `P` over `Y` and a morphism `f : Y' ⟶ Y`, the
sheaf on the small étale site of `Y'` of the `Y`-morphisms `U ⟶ P` lifting `U ⟶ Y' ⟶ Y`, that
is, the functor of points of the base change `P ×_Y Y'`, as a torsor under the sheaf
`U ↦ C(U, M)`. Its global sections are the lifts of `f` to `P`
(`AlgebraicGeometry.Scheme.EtaleTorsor.nonempty_pullbackSheafTorsor_iff`). -/
noncomputable def pullbackSheafTorsor :
    Sheaf.Torsor (Etale.continuousMapSheaf Y' M) where
  sheaf := Y'.smallEtaleTopology.uliftYoneda.{u + 1}.obj (t.pullbackEtale f)
  vadd U a φ := ⟨t.pullbackSmulHom f a φ.down⟩
  zero_vadd U φ := ULift.ext _ _ ((t.pullbackSmulHom_const f 0 φ.down).trans (by
    rw [pullbackVadd_zero, Category.comp_id]))
  add_vadd U a b φ := ULift.ext _ _ (t.pullbackSmulHom_add f a b φ.down)
  map_vadd h a φ := ULift.ext _ _ (t.comp_pullbackSmulHom f h.unop a φ.down)
  bijective_vadd U φ :=
    (Equiv.ulift.symm.bijective).comp (t.bijective_pullbackSmulHom f φ.down)
  nonemptySieve_mem U := by
    have := t.surjective
    have : Surjective (t.pullbackEtale f).hom := by
      change Surjective (pullback.snd t.π f)
      infer_instance
    let V : Y'.Etale := Etale.mk (pullback.fst U.hom (t.pullbackEtale f).hom ≫ U.hom)
    let ι : V ⟶ U := MorphismProperty.Over.homMk (pullback.fst U.hom _) rfl
    refine Y'.smallEtaleTopology.superset_covering ?_
      ((ofArrows_mem_smallEtaleTopology_iff (fun _ : PUnit.{1} ↦ ι)).2 ?_)
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨⟩
      exact ⟨⟨MorphismProperty.Over.homMk (pullback.snd U.hom _) pullback.condition.symm⟩⟩
    · simp only [Set.iUnion_const]
      exact Set.range_eq_univ.2 (Surjective.surj (f := pullback.fst U.hom _))

lemma pullbackSheafTorsor_vadd (U : Y'.Etaleᵒᵖ) (a : C(U.unop.left, M))
    (φ : U.unop ⟶ t.pullbackEtale f) :
    (t.pullbackSheafTorsor f).vadd U a ⟨φ⟩ = ⟨t.pullbackSmulHom f a φ⟩ :=
  rfl

/-- The global sections of the torsor of lifts are the lifts of `f` to the total space. -/
lemma nonempty_pullbackSheafTorsor_iff :
    Nonempty ((t.pullbackSheafTorsor f).sheaf.obj.obj (op (⊤_ Y'.Etale))) ↔
      ∃ s : Y' ⟶ t.P, s ≫ t.π = f := by
  let e := terminalIsTerminal.uniqueUpToIso
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Y')
  constructor
  · rintro ⟨⟨φ⟩⟩
    have h : (e.inv ≫ φ).left ≫ pullback.snd t.π f = 𝟙 Y' := MorphismProperty.Over.w (e.inv ≫ φ)
    refine ⟨(e.inv ≫ φ).left ≫ pullback.fst t.π f, ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, h, Category.id_comp]
  · rintro ⟨s, hs⟩
    exact ⟨⟨e.hom ≫ MorphismProperty.Over.homMk (pullback.lift s (𝟙 Y')
      (hs.trans (Category.id_comp f).symm)) (pullback.lift_snd _ _ _)⟩⟩

end PullbackTorsor

end EtaleTorsor

end AlgebraicGeometry.Scheme
