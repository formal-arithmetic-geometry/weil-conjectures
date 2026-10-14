/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale.Universal
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver

/-!
# Constant sheaves of sets on the small étale site and trivial covers

For a discrete set `S`, the constant sheaf of sets with value `S` on the small étale site of a
scheme `X` is the sheaf `V ↦ C(V, S)` of locally constant functions
(`AlgebraicGeometry.Scheme.Etale.constantSheafIsoContinuousMapSheafType`). When `S` is in
bijection with a type `S'` in the universe of `X`, this sheaf is represented by the trivial
cover `∐_{S'} X ⟶ X`: a morphism `V ⟶ ∐_{S'} X` over `X` is the same as a locally constant
function `V → S'` (`AlgebraicGeometry.Scheme.sigmaHomEquiv`).
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

section ContinuousMap

variable (X : Scheme.{u}) (A : Type (u + 1)) [TopologicalSpace A]

/-- The sheaf of sets `U ↦ C(U, A)` of continuous functions with values in a topological space
`A`, on the small étale site of `X`. It is the restriction of the fpqc sheaf
`AlgebraicGeometry.continuousMapPresheaf`. -/
noncomputable def Etale.continuousMapSheafType : Sheaf X.smallEtaleTopology (Type (u + 1)) :=
  ((toProEt X ⋙ ProEt.forget X ⋙ Over.forget X).sheafPushforwardContinuous _ _
    proetaleTopology).obj
    ⟨continuousMapPresheaf.{u + 1, u} A,
      .of_le proetaleTopology_le_fpqcTopology (isSheaf_fpqcTopology_continuousMapPresheaf A)⟩

lemma Etale.continuousMapSheafType_obj_obj (U : X.Etale) :
    (Etale.continuousMapSheafType X A).obj.obj (op U) = C(U.left, A) :=
  rfl

lemma Etale.continuousMapSheafType_obj_map_apply {U V : X.Etale} (f : U ⟶ V)
    (s : C(V.left, A)) :
    (Etale.continuousMapSheafType X A).obj.map f.op s = s.comp f.left.base.hom :=
  rfl

variable [DiscreteTopology A]

/-- The constant functions, as a map from the constant presheaf with value `A` to the sheaf of
continuous functions `U ↦ C(U, A)`. -/
noncomputable def Etale.constToContinuousMapType :
    (Functor.const X.Etaleᵒᵖ).obj A ⟶ (Etale.continuousMapSheafType X A).obj where
  app _ := ↾fun a ↦ ContinuousMap.const _ a
  naturality _ _ _ := rfl

/-- A continuous function to a discrete space is locally constant: it is constant on the open
fibres, which cover. -/
instance : Presheaf.IsLocallySurjective X.smallEtaleTopology
    (Etale.constToContinuousMapType X A) where
  imageSieve_mem {U} s₀ := by
    let s : C(U.left, A) := s₀
    let V (m : A) : X.Etale := Etale.mk ((U.left.fiberOpens s m).ι ≫ U.hom)
    let ι (m : A) : V m ⟶ U := MorphismProperty.Over.homMk (U.left.fiberOpens s m).ι rfl
    refine X.smallEtaleTopology.superset_covering ?_
      ((ofArrows_mem_smallEtaleTopology_iff ι).2 ?_)
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨m⟩
      refine ⟨m, ContinuousMap.ext fun x ↦ ?_⟩
      change m = s x.1
      exact x.2.symm
    · refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨s x, ⟨x, rfl⟩, ?_⟩
      exact Scheme.Opens.ι_apply _ _

/-- Two constant sections agreeing on `U` agree locally: either they are equal, or `U` is empty
and is covered by the empty family. -/
instance : Presheaf.IsLocallyInjective X.smallEtaleTopology
    (Etale.constToContinuousMapType X A) where
  equalizerSieve_mem {U} a b h := by
    by_cases hab : a = b
    · subst hab
      exact X.smallEtaleTopology.superset_covering (fun _ _ _ ↦ rfl)
        (X.smallEtaleTopology.top_mem _)
    · have : IsEmpty U.unop.left :=
        ⟨fun x ↦ hab (by have := congr_arg (fun f : C(U.unop.left, A) ↦ f x) h; exact this)⟩
      refine X.smallEtaleTopology.superset_covering ?_
        ((ofArrows_mem_smallEtaleTopology_iff (Z := PEmpty.elim) (W := U.unop)
          (fun i : PEmpty.{1} ↦ i.elim)).2 (Set.eq_univ_of_forall fun x ↦ isEmptyElim x))
      rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨i⟩
      exact i.elim

/-- The map from the constant sheaf of sets with value `A` to the sheaf of continuous functions
`U ↦ C(U, A)` sending the constant section `a` to the constant function `a`. -/
noncomputable def Etale.constantSheafToContinuousMapSheafType :
    (constantSheaf X.smallEtaleTopology (Type (u + 1))).obj A ⟶
      Etale.continuousMapSheafType X A :=
  ((sheafificationAdjunction X.smallEtaleTopology (Type (u + 1))).homEquiv _ _).symm
    (Etale.constToContinuousMapType X A)

omit [DiscreteTopology A] in
lemma Etale.toSheafify_constantSheafToContinuousMapSheafType [DiscreteTopology A] :
    toSheafify X.smallEtaleTopology _ ≫ (Etale.constantSheafToContinuousMapSheafType X A).hom =
      Etale.constToContinuousMapType X A := by
  have h := ((sheafificationAdjunction X.smallEtaleTopology (Type (u + 1))).homEquiv
    ((Functor.const X.Etaleᵒᵖ).obj A)
      (Etale.continuousMapSheafType X A)).apply_symm_apply (Etale.constToContinuousMapType X A)
  rw [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app] at h
  exact h

instance : IsIso (Etale.constantSheafToContinuousMapSheafType X A) := by
  have h := Etale.toSheafify_constantSheafToContinuousMapSheafType X A
  refine (Sheaf.isLocallyBijective_iff_isIso
    (Etale.constantSheafToContinuousMapSheafType X A)).1 ⟨?_, ?_⟩
  · change Presheaf.IsLocallyInjective _ _
    rw [← Presheaf.comp_isLocallyInjective_iff _ (toSheafify X.smallEtaleTopology _), h]
    infer_instance
  · change Presheaf.IsLocallySurjective _ _
    rw [← Presheaf.comp_isLocallySurjective_iff _ (toSheafify X.smallEtaleTopology _), h]
    infer_instance

/-- **The constant sheaf of sets is the sheaf of locally constant functions.** For a discrete
set `A`, the constant sheaf with value `A` on the small étale site of `X` is isomorphic to the
sheaf `U ↦ C(U, A)`, by the map sending the constant section `a` to the constant function `a`. -/
noncomputable def Etale.constantSheafIsoContinuousMapSheafType :
    (constantSheaf X.smallEtaleTopology (Type (u + 1))).obj A ≅
      Etale.continuousMapSheafType X A :=
  asIso (Etale.constantSheafToContinuousMapSheafType X A)

end ContinuousMap
section Sigma

variable (S' : Type u) (X : Scheme.{u}) [TopologicalSpace S'] [DiscreteTopology S']

/-- The index of the summand of `∐_{S'} X` containing a point, as a continuous function. -/
noncomputable def sigmaIdx : C(↑(∐ fun _ : S' ↦ X), S') :=
  ⟨fun z ↦ ((sigmaMk fun _ : S' ↦ X).symm z).1,
    (continuous_sigma_iff.2 fun _ ↦ continuous_const).comp (sigmaMk _).symm.continuous⟩

omit [DiscreteTopology S'] in
@[simp]
lemma sigmaIdx_ι (σ : S') (x : X) : sigmaIdx S' X (Sigma.ι (fun _ : S' ↦ X) σ x) = σ := by
  change ((sigmaMk fun _ : S' ↦ X).symm (Sigma.ι (fun _ : S' ↦ X) σ x)).1 = σ
  rw [← sigmaMk_mk, Homeomorph.symm_apply_apply]

variable {S' X}

lemma comp_sigmaIdx_apply {W : Scheme.{u}} (a : W ⟶ ∐ fun _ : S' ↦ X) (w : W ⟶ X)
    (ha : a ≫ Sigma.desc (fun _ ↦ 𝟙 X) = w) (σ : S') :
    (W.fiberOpens ((sigmaIdx S' X).comp a.base.hom) σ).ι ≫ a =
      (W.fiberOpens ((sigmaIdx S' X).comp a.base.hom) σ).ι ≫ w ≫ Sigma.ι (fun _ : S' ↦ X) σ := by
  let O := W.fiberOpens ((sigmaIdx S' X).comp a.base.hom) σ
  have hrange : Set.range (O.ι ≫ a) ⊆ Set.range (Sigma.ι (fun _ : S' ↦ X) σ) := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨τ, y, hy⟩ := (sigmaOpenCover fun _ : S' ↦ X).exists_eq ((O.ι ≫ a) z)
    have hτ : τ = σ := by
      have h1 : sigmaIdx S' X ((O.ι ≫ a) z) = σ := z.2
      rw [← hy] at h1
      exact (sigmaIdx_ι S' X τ y).symm.trans h1
    subst hτ
    exact ⟨y, hy⟩
  have h := IsOpenImmersion.lift_fac (Sigma.ι (fun _ : S' ↦ X) σ) (O.ι ≫ a) hrange
  have hl := congrArg (· ≫ Sigma.desc (fun _ : S' ↦ 𝟙 X)) h
  simp only [Category.assoc, Sigma.ι_desc, Category.comp_id, ha] at hl
  rw [← h, hl, Category.assoc]

variable {A : Type w} [TopologicalSpace A] [DiscreteTopology A] (e : A ≃ S')

/-- **Morphisms into a trivial cover are locally constant functions.** For `w : W ⟶ X`, the
morphisms `a : W ⟶ ∐_{S'} X` over `X` correspond to the locally constant functions `W → A`,
for `A ≃ S'`: the function attached to `a` sends `z` to the index of the summand containing
`a z`. -/
noncomputable def sigmaHomEquiv {W : Scheme.{u}} (w : W ⟶ X) :
    C(W, A) ≃ {a : W ⟶ ∐ fun _ : S' ↦ X // a ≫ Sigma.desc (fun _ ↦ 𝟙 X) = w} where
  toFun f := ⟨W.glueOfContinuousMap f (fun m ↦ w ≫ Sigma.ι (fun _ : S' ↦ X) (e m)), by
    rw [Scheme.glueOfContinuousMap_comp]
    exact Scheme.glueOfContinuousMap_eq fun m ↦ by simp⟩
  invFun a := ⟨fun z ↦ e.symm (sigmaIdx S' X (a.1 z)),
    continuous_of_discreteTopology.comp ((sigmaIdx S' X).comp a.1.base.hom).continuous⟩
  left_inv f := by
    ext z
    have h := Scheme.fiberOpens_ι_glueOfContinuousMap f (fun m ↦ w ≫ Sigma.ι (fun _ : S' ↦ X) (e m)) (f z)
    have := congrArg (fun g ↦ g ⟨z, (rfl : f z = f z)⟩) h
    simp only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] at this
    change e.symm (sigmaIdx S' X (W.glueOfContinuousMap f (fun m ↦ w ≫ Sigma.ι (fun _ : S' ↦ X) (e m)) z)) = f z
    rw [this, sigmaIdx_ι, Equiv.symm_apply_apply]
  right_inv a := by
    refine Subtype.ext (Scheme.glueOfContinuousMap_eq fun m ↦ ?_)
    have h := comp_sigmaIdx_apply a.1 w a.2 (e m)
    have hO : W.fiberOpens ⟨fun z ↦ e.symm (sigmaIdx S' X (a.1 z)),
        continuous_of_discreteTopology.comp ((sigmaIdx S' X).comp a.1.base.hom).continuous⟩ m =
        W.fiberOpens ((sigmaIdx S' X).comp a.1.base.hom) (e m) := by
      ext z
      exact e.symm_apply_eq
    rw [hO]
    exact h.symm

lemma sigmaHomEquiv_apply_coe {W : Scheme.{u}} (w : W ⟶ X) (f : C(W, A)) :
    (sigmaHomEquiv e w f).1 = W.glueOfContinuousMap f (fun m ↦ w ≫ Sigma.ι (fun _ : S' ↦ X) (e m)) := rfl

lemma sigmaHomEquiv_symm_apply {W : Scheme.{u}} (w : W ⟶ X)
    (a : {a : W ⟶ ∐ fun _ : S' ↦ X // a ≫ Sigma.desc (fun _ ↦ 𝟙 X) = w}) (z : W) :
    (sigmaHomEquiv e w).symm a z = e.symm (sigmaIdx S' X (a.1 z)) := rfl

/-- `sigmaHomEquiv` is natural in `W`. -/
lemma sigmaHomEquiv_comp {W W' : Scheme.{u}} (φ : W' ⟶ W) (w : W ⟶ X) (f : C(W, A)) :
    (sigmaHomEquiv e (φ ≫ w) (f.comp φ.base.hom)).1 = φ ≫ (sigmaHomEquiv e w f).1 := by
  rw [sigmaHomEquiv_apply_coe, sigmaHomEquiv_apply_coe, Scheme.comp_glueOfContinuousMap]
  simp only [Category.assoc]

/-- `sigmaHomEquiv` is natural in `W`, in a form with the base morphisms only equal. -/
lemma sigmaHomEquiv_comp' {W W' : Scheme.{u}} (φ : W' ⟶ W) (w : W ⟶ X) {w' : W' ⟶ X}
    (hw : φ ≫ w = w') (f : C(W, A)) :
    (sigmaHomEquiv e w' (f.comp φ.base.hom)).1 = φ ≫ (sigmaHomEquiv e w f).1 := by
  subst hw
  exact sigmaHomEquiv_comp e φ w f

end Sigma
section Restrict

variable {T : Scheme.{u}} (E : T.Etaleᵒᵖ ⥤ Type (u + 1)) (U : T.Etale)

/-- The restriction of a presheaf on the small étale site of `T` to the small étale site of an
étale `T`-scheme `U`: its sections over `W ⟶ U` are the sections over `W ⟶ U ⟶ T`. It is the
presheaf underlying `(Etale.overSheafEquiv U _).functor.obj (E.over U)`. -/
abbrev Etale.restrictPresheaf : U.left.Etaleᵒᵖ ⥤ Type (u + 1) :=
  (Scheme.Etale.etaleToOver U ⋙ CategoryTheory.Over.forget U).op ⋙ E

variable (S' : Type u)

/-- The trivial cover `∐_{S'} U ⟶ U ⟶ T`, as an étale `T`-scheme. -/
noncomputable abbrev Etale.trivialCover : T.Etale :=
  have : AlgebraicGeometry.Etale (Sigma.desc fun _ : S' ↦ 𝟙 U.left) :=
    IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  Etale.mk (Sigma.desc (fun _ : S' ↦ 𝟙 U.left) ≫ U.hom)

/-- The trivial cover `∐_{S'} U ⟶ U`, as an étale `U`-scheme. -/
noncomputable abbrev Etale.trivialCover' : U.left.Etale :=
  have : AlgebraicGeometry.Etale (Sigma.desc fun _ : S' ↦ 𝟙 U.left) :=
    IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  Etale.mk (Sigma.desc (fun _ : S' ↦ 𝟙 U.left))

variable [TopologicalSpace S'] [DiscreteTopology S'] {A : Type (u + 1)} [TopologicalSpace A]
  [DiscreteTopology A] (e : A ≃ S')

variable {E U S'}

/-- A universal section on the trivial cover `∐_{S'} U` identifies the restriction of `E` to `U`
with the sheaf of locally constant `A`-valued functions, for `A ≃ S'`. -/
noncomputable def Etale.isoOfIsUniversalSection {ξ : E.obj (op (Etale.trivialCover U S'))}
    (h : IsUniversalSection E U.hom (Etale.trivialCover U S') (Sigma.desc fun _ ↦ 𝟙 U.left) ξ) :
    Etale.restrictPresheaf E U ≅ (Etale.continuousMapSheafType U.left A).obj := by
  let κ (W : U.left.Etale) (f : C(W.left, A)) : E.obj (op (Etale.mk (W.hom ≫ U.hom))) :=
    E.map (MorphismProperty.Over.homMk (sigmaHomEquiv e W.hom f).1 (by
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ U.hom) (sigmaHomEquiv e W.hom f).2)) :
        Etale.mk (W.hom ≫ U.hom) ⟶ Etale.trivialCover U S').op ξ
  have hκ (W : U.left.Etale) : Function.Bijective (κ W) := by
    let ψ : {a : W.left ⟶ ∐ fun _ : S' ↦ U.left // a ≫ Sigma.desc (fun _ ↦ 𝟙 U.left) = W.hom} →
        {a : Etale.mk (W.hom ≫ U.hom) ⟶ Etale.trivialCover U S' //
          a.left ≫ Sigma.desc (fun _ ↦ 𝟙 U.left) = W.hom} := fun a ↦
      ⟨MorphismProperty.Over.homMk a.1 (by
        exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ U.hom) a.2)), a.2⟩
    have hψ : Function.Bijective ψ :=
      ⟨fun a b hab ↦ Subtype.ext (congrArg (fun c ↦ c.1.left) hab),
        fun b ↦ ⟨⟨b.1.left, b.2⟩, rfl⟩⟩
    exact ((h (Etale.mk (W.hom ≫ U.hom)) W.hom rfl).comp hψ).comp (sigmaHomEquiv e W.hom).bijective
  refine (NatIso.ofComponents (fun W ↦ (Equiv.ofBijective (κ W.unop) (hκ W.unop)).toIso)
    (fun {W₁ W₂} φ ↦ ?_)).symm
  ext f
  change κ W₂.unop (f.comp φ.unop.left.base.hom) =
    E.map (MorphismProperty.Over.homMk φ.unop.left (by
      change φ.unop.left ≫ W₁.unop.hom ≫ U.hom = W₂.unop.hom ≫ U.hom
      rw [MorphismProperty.Over.w_assoc]) :
        Etale.mk (W₂.unop.hom ≫ U.hom) ⟶ Etale.mk (W₁.unop.hom ≫ U.hom)).op (κ W₁.unop f)
  simp only [κ]
  rw [← Functor.map_comp_apply, ← op_comp]
  refine congrArg (fun g ↦ E.map (Opposite.op g) ξ) (Etale.hom_ext ?_)
  change (sigmaHomEquiv e W₂.unop.hom (f.comp φ.unop.left.base.hom)).1 =
    φ.unop.left ≫ (sigmaHomEquiv e W₁.unop.hom f).1
  exact sigmaHomEquiv_comp' e φ.unop.left _ (MorphismProperty.Over.w φ.unop) f
/-- The restriction of `E` to `U` evaluated on a morphism of étale `U`-schemes is `E` evaluated
on the corresponding morphism of étale `T`-schemes. -/
lemma Etale.restrictPresheaf_map_eq {W₁ W₂ : U.left.Etale} (a : W₁ ⟶ W₂)
    (b : Etale.mk (W₁.hom ≫ U.hom) ⟶ Etale.mk (W₂.hom ≫ U.hom)) (hab : b.left = a.left)
    (x : E.obj (op (Etale.mk (W₂.hom ≫ U.hom)))) :
    (Etale.restrictPresheaf E U).map a.op x = E.map b.op x :=
  congrArg (fun g ↦ E.map (Opposite.op g) x) (Etale.hom_ext hab.symm)

/-- **An identification with locally constant functions gives a universal section.** If the
restriction of `E` to `U` is identified with the sheaf of locally constant `A`-valued functions,
`A ≃ S'`, then the section corresponding to the index function of `∐_{S'} U` is universal on
the trivial cover `∐_{S'} U ⟶ U`. -/
lemma Etale.isUniversalSection_of_iso
    (α : Etale.restrictPresheaf E U ≅ (Etale.continuousMapSheafType U.left A).obj) :
    IsUniversalSection E U.hom (Etale.trivialCover U S') (Sigma.desc fun _ ↦ 𝟙 U.left)
      (α.inv.app (op (Etale.trivialCover' U S'))
        ((sigmaHomEquiv e (Sigma.desc fun _ : S' ↦ 𝟙 U.left)).symm
          ⟨𝟙 _, Category.id_comp _⟩)) := by
  refine IsUniversalSection.of_mk fun W w _ ↦ ?_
  let W'' : U.left.Etale := Etale.mk w
  let idx := (sigmaHomEquiv e (Sigma.desc fun _ : S' ↦ 𝟙 U.left)).symm ⟨𝟙 _, Category.id_comp _⟩
  let ψ : {a : Etale.mk (w ≫ U.hom) ⟶ Etale.trivialCover U S' //
      a.left ≫ Sigma.desc (fun _ ↦ 𝟙 U.left) = w} →
      {a : W ⟶ ∐ fun _ : S' ↦ U.left // a ≫ Sigma.desc (fun _ ↦ 𝟙 U.left) = w} :=
    fun a ↦ ⟨a.1.left, a.2⟩
  have hψ : Function.Bijective ψ := by
    refine ⟨fun a b hab ↦ Subtype.ext (Etale.hom_ext (congrArg Subtype.val hab)), fun b ↦ ?_⟩
    refine ⟨⟨MorphismProperty.Over.homMk b.1 ?_, b.2⟩, rfl⟩
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ U.hom) b.2)
  have key : α.hom.app (op W'') ∘ (fun a : {a : Etale.mk (w ≫ U.hom) ⟶ Etale.trivialCover U S' //
      a.left ≫ Sigma.desc (fun _ ↦ 𝟙 U.left) = w} ↦ E.map a.1.op (α.inv.app (op (Etale.trivialCover' U S')) idx)) =
      (sigmaHomEquiv e w).symm ∘ ψ := by
    ext1 a
    let a'' : W'' ⟶ Etale.trivialCover' U S' := MorphismProperty.Over.homMk a.1.left a.2
    have h1 : E.map a.1.op (α.inv.app (op (Etale.trivialCover' U S')) idx) =
        (Etale.restrictPresheaf E U).map a''.op
          (α.inv.app (op (Etale.trivialCover' U S')) idx) :=
      (Etale.restrictPresheaf_map_eq a'' a.1 rfl _).symm
    have h2 : α.hom.app (op (Etale.trivialCover' U S'))
        (α.inv.app (op (Etale.trivialCover' U S')) idx) = idx := by
      rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, α.inv_hom_id]
      rfl
    rw [Function.comp_apply, h1, NatTrans.naturality_apply, h2]
    exact ContinuousMap.ext fun z ↦ rfl
  have hα : Function.Bijective (α.hom.app (op W'')) :=
    (isIso_iff_bijective _).1 inferInstance
  exact (Function.Bijective.of_comp_iff' hα _).1
    (key ▸ (sigmaHomEquiv e w).symm.bijective.comp hψ)

end Restrict

end AlgebraicGeometry.Scheme
