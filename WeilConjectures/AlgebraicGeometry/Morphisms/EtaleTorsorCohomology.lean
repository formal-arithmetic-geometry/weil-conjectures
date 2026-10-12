/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# Naturality of the torsor attached to an étale `H¹`-class

Let `M` be a finite abelian group and `Y` a scheme. Every class `ξ ∈ H¹(Y_ét, M)` of the
constant sheaf `M` is the class of an `M`-torsor `t` over `Y`
(`AlgebraicGeometry.Scheme.EtaleTorsor.exists_quotientEquivSheafH`), and the classification
is natural in `Y`: the pullback of `ξ` along a morphism `f : Y' ⟶ Y` is the class of the
pulled-back torsor `t ×_Y Y'`. Since a torsor has class zero exactly when it has a section,
the pullback of `ξ` along `f` vanishes exactly when `f` lifts to the total space of `t`.

This is the form in which the vanishing theorem `sk-thm-vanishing` uses the classification:
it kills a class of `H¹` by pulling it back to a cover over which the torsor acquires a
section.

## Main definitions

- `AlgebraicGeometry.Scheme.EtaleTorsor.pullbackSheafTorsor`: for an `M`-torsor `P` over `Y`
  and `f : Y' ⟶ Y`, the sheaf of lifts `U ⟶ P` of `U ⟶ Y' ⟶ Y` on the small étale site of
  `Y'`, as a torsor under `U ↦ C(U, M)`.

## Main statements

- `AlgebraicGeometry.Scheme.EtaleTorsor.exists_forall_cohomologyMap_eq_zero_iff`: a class of
  `H¹(Y_ét, M)` is represented by an `M`-torsor `t`, in the sense that it dies after pullback
  along `f` exactly when `f` lifts to `t`.

## Implementation notes

Write `t` as the torsor of local lifts of a global section `s` of `Q` along `I ⟶ Q`, for an
injective resolution `0 → M → I → Q → 0`; then `ξ = δ(s)`. The pullback `f^*` is exact, so the
pullback of `ξ` is `δ'(s')` for the pulled-back sequence `0 → f^*M → f^*I → f^*Q → 0` and the
pulled-back section `s'`, and it vanishes iff the torsor of local lifts of `s'` to `f^*I` has a
global section. This torsor is identified with the torsor of lifts of `f` to `P`
(`AlgebraicGeometry.Scheme.EtaleTorsor.pullbackSheafTorsor`) by the equivariant map which sends
a lift `φ : U ⟶ P` to the pullback along `φ` of the tautological lift `x₀ ∈ I(P)` of `s`. The
pullback of sections is described only through the unit `I ⟶ f_* f^* I` of the adjunction
`f^* ⊣ f_*`, and its compatibility with constant sections comes from the definition of the
comparison `f^* M ≅ M` (`AlgebraicGeometry.Scheme.upperStarConstantSheafIso`) by uniqueness of
adjoints.
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

/-- The open fibres of a continuous function to a discrete space cover. -/
lemma Etale.ofArrows_fiberι_mem {U : X.Etale} (a : C(U.left, M)) :
    Sieve.ofArrows _ (Etale.fiberι a) ∈ X.smallEtaleTopology U := by
  refine (ofArrows_mem_smallEtaleTopology_iff _).2
    (Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨a x, ⟨x, rfl⟩, ?_⟩)
  exact Scheme.Opens.ι_apply _ _

/-- Two sections of an abelian sheaf on the small étale site agree if they agree on the open
fibres of a continuous function to a discrete space. -/
lemma Etale.ext_of_fiberι (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) {U : X.Etale}
    (a : C(U.left, M)) {x y : F.obj.obj (op U)}
    (h : ∀ m, F.obj.map (Etale.fiberι a m).op x = F.obj.map (Etale.fiberι a m).op y) :
    x = y := by
  have hF : Presieve.IsSheaf X.smallEtaleTopology (F.obj ⋙ forget _) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      ((sheafCompose X.smallEtaleTopology (forget _)).obj F).property
  refine (hF _ (Etale.ofArrows_fiberι_mem a)).isSeparatedFor.ext fun V g hg ↦ ?_
  obtain ⟨W, k, _, ⟨m⟩, rfl⟩ := hg
  change F.obj.map (k ≫ Etale.fiberι a m).op x = F.obj.map (k ≫ Etale.fiberι a m).op y
  rw [op_comp, F.obj.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, h]

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

lemma pullbackVadd_left_fst (m : M) :
    (t.pullbackVadd f m).left ≫ pullback.fst t.π f = pullback.fst t.π f ≫ t.vadd m := by
  simp [Hom.Etale, vaddEtale_left]

lemma pullbackVadd_left_snd (m : M) :
    (t.pullbackVadd f m).left ≫ pullback.snd t.π f = pullback.snd t.π f := by
  simp [Hom.Etale]

lemma pullbackVadd_add (m n : M) :
    t.pullbackVadd f (m + n) = t.pullbackVadd f m ≫ t.pullbackVadd f n := by
  rw [pullbackVadd, vaddEtale_add, Functor.map_comp]

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
  rw [pullbackSmulHom, pullbackSmulHom, pullbackSmulHom, Etale.ι_glueHom_left_of_le _ _ hab,
    Etale.ι_glueHom_left_of_le _ _ ha, MorphismProperty.Comma.comp_left, ← Category.assoc,
    Etale.ι_glueHom_left_of_le _ _ hb, add_comm, pullbackVadd_add]
  simp only [MorphismProperty.Comma.comp_left, Category.assoc]

/-- **The torsor of lifts.** For an `M`-torsor `P` over `Y` and a morphism `f : Y' ⟶ Y`, the
sheaf on the small étale site of `Y'` of the `Y`-morphisms `U ⟶ P` lifting `U ⟶ Y' ⟶ Y`, that
is, the functor of points of the base change `P ×_Y Y'`, as a torsor under the sheaf
`U ↦ C(U, M)`. Its global sections are the lifts of `f` to `P`
(`AlgebraicGeometry.Scheme.EtaleTorsor.nonempty_pullbackSheafTorsor_iff`). -/
noncomputable def pullbackSheafTorsor :
    Sheaf.Torsor (Etale.continuousMapSheaf Y' M) where
  sheaf := Y'.smallEtaleTopology.uliftYoneda.{u + 1}.obj (t.pullbackEtale f)
  vadd U a φ := ⟨t.pullbackSmulHom f a φ.down⟩
  zero_vadd U φ := ULift.ext _ _ (by
    change Etale.glueHom (ContinuousMap.const _ 0) _ = _
    rw [Etale.glueHom_const, pullbackVadd, vaddEtale_zero, Functor.map_id, Category.comp_id])
  add_vadd U a b φ := ULift.ext _ _ (t.pullbackSmulHom_add f a b φ.down)
  map_vadd h a φ := ULift.ext _ _ (by
    change h.unop ≫ Etale.glueHom a _ = Etale.glueHom _ _
    rw [Etale.comp_glueHom]
    simp only [Category.assoc]
    rfl)
  bijective_vadd U φ := by
    refine (Equiv.ulift.symm.bijective).comp ?_
    refine ⟨fun a b hab ↦ ContinuousMap.ext fun x ↦ ?_, fun ψ ↦ ?_⟩
    · let W := U.unop.left.fiberOpens (a.prodMk b) (a x, b x)
      have ha : W ≤ U.unop.left.fiberOpens a (a x) := fun y hy ↦ (Prod.ext_iff.1 hy).1
      have hb : W ≤ U.unop.left.fiberOpens b (b x) := fun y hy ↦ (Prod.ext_iff.1 hy).2
      have h := congr_arg (fun χ : U.unop ⟶ t.pullbackEtale f ↦
        W.ι ≫ χ.left ≫ pullback.fst t.π f) hab
      simp only [pullbackSmulHom] at h
      rw [← Category.assoc, ← Category.assoc, Etale.ι_glueHom_left_of_le _ _ ha,
        Etale.ι_glueHom_left_of_le _ _ hb] at h
      simp only [MorphismProperty.Comma.comp_left, Category.assoc,
        pullbackVadd_left_fst] at h
      rw [← Category.assoc, ← Category.assoc W.ι] at h
      exact t.eq_of_comp_vadd_eq _ h ⟨x, rfl⟩
    · obtain ⟨a, ha⟩ := t.exists_glueOfContinuousMap_eq (φ.down.left ≫ pullback.fst t.π f)
        (ψ.down.left ≫ pullback.fst t.π f) (by
          rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc,
            ← Category.assoc]
          congr 1
          exact (MorphismProperty.Over.w ψ.down).trans (MorphismProperty.Over.w φ.down).symm)
      refine ⟨a, etaleHom_ext (pullback.hom_ext ?_ ?_)⟩
      · change (Etale.glueHom a _).left ≫ _ = _
        rw [Etale.glueHom_left, Scheme.glueOfContinuousMap_comp, ← ha]
        congr 1
        funext m
        simp only [MorphismProperty.Comma.comp_left, Category.assoc, pullbackVadd_left_fst]
      · change (Etale.glueHom a _).left ≫ _ = _
        rw [Etale.glueHom_left, Scheme.glueOfContinuousMap_comp]
        refine Scheme.glueOfContinuousMap_eq fun m ↦ ?_
        simp only [MorphismProperty.Comma.comp_left, Category.assoc, pullbackVadd_left_snd]
        congr 1
        exact (MorphismProperty.Over.w φ.down).trans (MorphismProperty.Over.w ψ.down).symm
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
    refine ⟨(e.inv ≫ φ).left ≫ pullback.fst t.π f, ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have := MorphismProperty.Over.w (e.inv ≫ φ)
    simp only [Hom.Etale, MorphismProperty.Over.pullback_obj_hom] at this
    rw [this]
    exact Category.id_comp f
  · rintro ⟨s, hs⟩
    exact ⟨⟨e.hom ≫ MorphismProperty.Over.homMk (pullback.lift s (𝟙 Y') (by simp [hs]))
      (by simp [Hom.Etale])⟩⟩

end PullbackTorsor

end EtaleTorsor

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.EtaleTorsor

variable (M : Type (u + 1)) [AddCommGroup M] [Finite M]

/-- Blueprint `sk-prop-input-torsors` (naturality): Torsors and étale H^1

Let `M` be a finite abelian group and `ξ ∈ H¹(Y_ét, M)` a class of the constant sheaf `M` on a
scheme `Y`. Then there is an `M`-torsor `t` over `Y` representing `ξ` naturally: for every
morphism `f : Y' ⟶ Y`, the pullback of `ξ` along `f` vanishes exactly when `f` lifts to the
total space of `t`, that is, exactly when the pulled-back torsor `t ×_Y Y'` is trivial. -/
@[stacks 02NE]
theorem exists_forall_cohomologyMap_eq_zero_iff {Y : Scheme.{u}}
    (ξ : Sheaf.H ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of M)) 1) :
    ∃ t : EtaleTorsor M Y, ∀ ⦃Y' : Scheme.{u}⦄ (f : Y' ⟶ Y),
      Etale.cohomologyMap f _ 1 ξ = 0 ↔ ∃ s : Y' ⟶ t.P, s ≫ t.π = f :=
  sorry

end AlgebraicGeometry.Scheme.EtaleTorsor
