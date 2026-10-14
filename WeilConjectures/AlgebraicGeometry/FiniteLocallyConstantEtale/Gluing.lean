/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale.Universal
public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing

/-!
# Zariski gluing of representing finite étale schemes

Let `E` be a sheaf of sets on the small étale site of a scheme `T` and `u : U ⟶ T` étale. If
every point of `U` has an open neighbourhood `W` such that the restriction of `E` to étale
`W`-schemes is represented by a finite étale `W`-scheme
(`AlgebraicGeometry.Scheme.IsUniversalSection`), then the restriction of `E` to étale `U`-schemes
is represented by a finite étale `U`-scheme
(`AlgebraicGeometry.Scheme.exists_isUniversalSection_of_forall_exists_opens`).

The representing schemes over the members of the cover of `U` by all such opens are unique up
to unique isomorphism, so they form a relative gluing datum over this locally directed cover
(`AlgebraicGeometry.Scheme.Cover.RelativeGluingData`, Stacks 01LH); the glued scheme `P` is
finite étale over `U`, the universal sections glue to a section of `E` over `P` by the sheaf
property, and this section is universal because universality can be checked on an open cover.

This is the Zariski-local step in the proof that finite locally constant sheaves are
represented by finite étale schemes (blueprint
`lemma-weil-pbc-finite-locally-constant-etale-equivalence`).
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite MorphismProperty

namespace AlgebraicGeometry.Scheme

section OpenRestriction

variable {T : Scheme.{u}} {E : T.Etaleᵒᵖ ⥤ Type w}

/-- The restriction of an étale `T`-scheme `Z` to an open subscheme `O` of `Z`. -/
noncomputable abbrev Etale.restrict (Z : T.Etale) (O : Z.left.Opens) : T.Etale :=
  Etale.mk (O.ι ≫ Z.hom)

/-- The inclusion of the restriction of an étale `T`-scheme to an open subscheme. -/
noncomputable abbrev Etale.restrictι (Z : T.Etale) (O : Z.left.Opens) :
    Etale.restrict Z O ⟶ Z :=
  Over.homMk O.ι rfl

/-- A sheaf on the small étale site satisfies the sheaf condition for a jointly surjective
family of morphisms. -/
lemma Etale.isSheafFor_ofArrows (hE : Presheaf.IsSheaf T.smallEtaleTopology E) {Z : T.Etale}
    {ι : Type*} {Y : ι → T.Etale} (f : ∀ i, Y i ⟶ Z)
    (hf : ⋃ i, Set.range (f i).left = Set.univ) :
    Presieve.IsSheafFor E (Presieve.ofArrows Y f) :=
  (Presieve.isSheafFor_iff_generate _).2
    ((isSheaf_iff_isSheaf_of_type _ _).1 hE _ ((ofArrows_mem_smallEtaleTopology_iff f).2 hf))

lemma Etale.iUnion_range_restrictι {Z : T.Etale} {ι : Type*} (O : ι → Z.left.Opens)
    (hO : ⨆ i, O i = ⊤) : ⋃ i, Set.range (Etale.restrictι Z (O i)).left = Set.univ := by
  refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ?_
  have hx : x ∈ ⨆ i, O i := hO ▸ trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact ⟨i, ⟨x, hi⟩, rfl⟩

/-- Sections of a sheaf on the small étale site of `T` over an étale `T`-scheme `Z` which agree
on the members of an open cover of `Z` agree. -/
lemma Etale.ext_of_iSup_eq_top (hE : Presheaf.IsSheaf T.smallEtaleTopology E) {Z : T.Etale}
    {ι : Type*} (O : ι → Z.left.Opens) (hO : ⨆ i, O i = ⊤) {x y : E.obj (op Z)}
    (h : ∀ i, E.map (Etale.restrictι Z (O i)).op x = E.map (Etale.restrictι Z (O i)).op y) :
    x = y :=
  (Etale.isSheafFor_ofArrows hE _ (Etale.iUnion_range_restrictι O hO)).isSeparatedFor.ext
    (by rintro _ _ ⟨i⟩; exact h i)

end OpenRestriction

section Good

variable {T : Scheme.{u}} (E : T.Etaleᵒᵖ ⥤ Type w) {U : Scheme.{u}} (u : U ⟶ T)
  [AlgebraicGeometry.Etale u]

/-- An open `W` of `U` is *good* for `E` if the restriction of `E` to étale `W`-schemes is
represented by a finite étale `W`-scheme, i.e. has a universal section relative to `W ⟶ T`. -/
def IsRepresentableOver (W : U.Opens) : Prop :=
  ∃ (V : Scheme.{u}) (v : V ⟶ W) (_ : AlgebraicGeometry.Etale v) (_ : IsFinite v)
    (ξ : E.obj (op (Etale.mk (v ≫ W.ι ≫ u)))),
    IsUniversalSection E (W.ι ≫ u) (Etale.mk (v ≫ W.ι ≫ u)) v ξ

variable {E u}

/-- Representability over an open passes to smaller opens, by base change. -/
lemma IsRepresentableOver.mono {W W' : U.Opens} (h : IsRepresentableOver E u W)
    (hle : W' ≤ W) : IsRepresentableOver E u W' := by
  obtain ⟨V, v, _, _, ξ, hξ⟩ := h
  have ho : U.homOfLE hle ≫ W.ι ≫ u = W'.ι ≫ u := by rw [Scheme.homOfLE_ι_assoc]
  exact ⟨pullback v (U.homOfLE hle), pullback.snd _ _, inferInstance, inferInstance, _,
    hξ.baseChange (u' := W'.ι ≫ u) rfl ho⟩

end Good

/-- An isomorphism of étale `T`-schemes gives an isomorphism of the underlying schemes. -/
@[simps]
def Etale.isoLeft {T : Scheme.{u}} {A B : T.Etale} (e : A ≅ B) : A.left ≅ B.left where
  hom := e.hom.left
  inv := e.inv.left
  hom_inv_id := by rw [← Etale.comp_left_eq, e.hom_inv_id, Etale.id_left_eq]
  inv_hom_id := by rw [← Etale.comp_left_eq, e.inv_hom_id, Etale.id_left_eq]

namespace GlueRepr

variable {T : Scheme.{u}} {E : T.Etaleᵒᵖ ⥤ Type w} {U : Scheme.{u}} {u : U ⟶ T}
  [AlgebraicGeometry.Etale u]

variable (E u) in
/-- The opens of `U` over which `E` is represented by a finite étale scheme. -/
abbrev Idx : Type u := {W : U.Opens // IsRepresentableOver E u W}

/-- The representing finite étale scheme over a good open. -/
noncomputable def V (i : Idx E u) : Scheme.{u} := i.2.choose

/-- The structure morphism of the representing scheme over a good open. -/
noncomputable def v (i : Idx E u) : V i ⟶ i.1 := i.2.choose_spec.choose

instance (i : Idx E u) : AlgebraicGeometry.Etale (v i) := i.2.choose_spec.choose_spec.choose

instance (i : Idx E u) : IsFinite (v i) := i.2.choose_spec.choose_spec.choose_spec.choose

/-- The representing scheme over a good open, as an étale `T`-scheme. -/
noncomputable abbrev Y (i : Idx E u) : T.Etale := Etale.mk (v i ≫ i.1.ι ≫ u)

/-- The universal section over a good open. -/
noncomputable def ξ (i : Idx E u) : E.obj (op (Y i)) :=
  i.2.choose_spec.choose_spec.choose_spec.choose_spec.choose

lemma isUniversal (i : Idx E u) : IsUniversalSection E (i.1.ι ≫ u) (Y i) (v i) (ξ i) :=
  i.2.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

lemma exists_transE {i j : Idx E u} (h : i.1 ≤ j.1) :
    ∃ a : Y i ⟶ Y j, a.left ≫ v j = v i ≫ U.homOfLE h ∧ E.map a.op (ξ j) = ξ i :=
  (isUniversal j).exists_hom (W := Y i) (v i ≫ U.homOfLE h)
    (by rw [Category.assoc, Scheme.homOfLE_ι_assoc]; rfl) (ξ i)

/-- The transition morphism between the representing schemes over good opens `i ≤ j`. -/
noncomputable def transE {i j : Idx E u} (h : i.1 ≤ j.1) : Y i ⟶ Y j := (exists_transE h).choose

lemma transE_left_v {i j : Idx E u} (h : i.1 ≤ j.1) :
    (transE h).left ≫ v j = v i ≫ U.homOfLE h :=
  (exists_transE h).choose_spec.1

lemma map_transE {i j : Idx E u} (h : i.1 ≤ j.1) : E.map (transE h).op (ξ j) = ξ i :=
  (exists_transE h).choose_spec.2

lemma transE_unique {i j : Idx E u} (h : i.1 ≤ j.1) (a : Y i ⟶ Y j)
    (ha : a.left ≫ v j = v i ≫ U.homOfLE h) (haξ : E.map a.op (ξ j) = ξ i) :
    a = transE h :=
  (isUniversal j).hom_ext (ha.trans (transE_left_v h).symm)
    (by rw [ha, Category.assoc, Scheme.homOfLE_ι_assoc]; rfl) (haξ.trans (map_transE h).symm)

lemma transE_refl (i : Idx E u) : transE (le_refl i.1) = 𝟙 (Y i) :=
  (transE_unique _ _ (by rw [Etale.id_left_eq, Category.id_comp, Scheme.homOfLE_rfl,
    Category.comp_id]) (by rw [op_id, Functor.map_id_apply])).symm

lemma transE_trans {i j k : Idx E u} (h₁ : i.1 ≤ j.1) (h₂ : j.1 ≤ k.1) :
    transE h₁ ≫ transE h₂ = transE (h₁.trans h₂) :=
  transE_unique _ _ (by rw [Etale.comp_left_eq, Category.assoc, transE_left_v,
      reassoc_of% (transE_left_v h₁), Scheme.homOfLE_homOfLE])
    (by rw [op_comp, Functor.map_comp_apply, map_transE, map_transE])

variable (H : ∀ x : U, ∃ W : U.Opens, x ∈ W ∧ IsRepresentableOver E u W)

include H in
lemma isBasis : TopologicalSpace.Opens.IsBasis (Set.range fun i : Idx E u ↦ i.1) := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro O x hx
  obtain ⟨W, hxW, hW⟩ := H x
  exact ⟨W ⊓ O, ⟨⟨W ⊓ O, hW.mono inf_le_left⟩, rfl⟩, ⟨hxW, hx⟩, inf_le_right⟩

/-- The open cover of `U` by the opens over which `E` is represented. -/
noncomputable def cover : U.OpenCover where
  I₀ := Idx E u
  X i := i.1
  f i := i.1.ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨W, hxW, hW⟩ := H x
    exact ⟨⟨W, hW⟩, ⟨x, hxW⟩, rfl⟩

instance : Preorder (cover H).I₀ := inferInstanceAs (Preorder (Idx E u))

noncomputable instance : (cover H).LocallyDirected :=
  .ofIsBasisOpensRange (fun {i j} ↦ by
      change i.1 ≤ j.1 ↔ i.1.ι.opensRange ≤ j.1.ι.opensRange
      rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]) (by
    have : (fun i : (cover H).I₀ ↦ ((cover H).f i).opensRange) = fun i : Idx E u ↦ i.1 :=
      funext fun i ↦ Scheme.Opens.opensRange_ι _
    rw [this]
    exact isBasis H)

lemma cover_trans {i j : (cover H).I₀} (f : i ⟶ j) :
    (cover H).trans f = U.homOfLE (leOfHom f) := by
  rw [← cancel_mono (j.1.ι)]
  exact ((cover H).trans_map f).trans (Scheme.homOfLE_ι _ _).symm

/-- The representing schemes over the good opens, as a functor on the cover. -/
noncomputable def functor : (cover H).I₀ ⥤ Scheme.{u} where
  obj i := V i
  map f := (transE (leOfHom f)).left
  map_id i := by
    change (transE (le_refl i.1)).left = _
    rw [transE_refl]
    rfl
  map_comp f g := by
    rw [← Etale.comp_left_eq, transE_trans]

/-- The structure morphisms of the representing schemes, as a natural transformation. -/
noncomputable def natTrans : functor H ⟶ (cover H).functorOfLocallyDirected where
  app i := v i
  naturality {i j} f := by
    change (transE (leOfHom f)).left ≫ v j = v i ≫ (cover H).trans f
    rw [transE_left_v, cover_trans]

lemma equifibered : (natTrans H).Equifibered := by
  intro i j f
  change IsPullback (transE (leOfHom f)).left (v i) (v j) ((cover H).trans f)
  rw [cover_trans]
  have hle : i.1 ≤ j.1 := leOfHom f
  have ho : U.homOfLE hle ≫ j.1.ι ≫ u = i.1.ι ≫ u := by rw [Scheme.homOfLE_ι_assoc]
  have hB := (isUniversal j).baseChange (u' := i.1.ι ≫ u) rfl ho
  obtain ⟨e, he, heξ⟩ := (isUniversal i).exists_iso rfl hB rfl
  have ht : transE hle = e.hom ≫ IsUniversalSection.baseChangeHom rfl ho := by
    refine (transE_unique _ _ ?_ ?_).symm
    · change (e.hom.left ≫ pullback.fst _ _) ≫ v j = _
      rw [Category.assoc, pullback.condition, ← Category.assoc, he]
    · rw [op_comp, Functor.map_comp_apply, heξ]
  refine IsPullback.of_iso_pullback ⟨?_⟩ (Etale.isoLeft e) ?_ he
  · rw [transE_left_v]
  · rw [ht]
    rfl

/-- The relative gluing datum given by the representing schemes. -/
noncomputable def gluingData : (cover H).RelativeGluingData where
  functor := functor H
  natTrans := natTrans H
  equifibered := equifibered H
/-- The glued finite étale `U`-scheme. -/
noncomputable abbrev P : Scheme.{u} := (gluingData H).glued

/-- The structure morphism of the glued scheme. -/
noncomputable abbrev π : P H ⟶ U := (gluingData H).toBase

/-- The inclusion of the representing scheme over a good open into the glued scheme. -/
noncomputable abbrev ι (i : (cover H).I₀) : V i ⟶ P H := colimit.ι (gluingData H).functor i

lemma isPullback_ι (i : (cover H).I₀) : IsPullback (v i) (ι H i) i.1.ι (π H) :=
  (gluingData H).isPullback_natTrans_ι_toBase i

@[reassoc]
lemma ι_π (i : (cover H).I₀) : ι H i ≫ π H = v i ≫ i.1.ι :=
  (gluingData H).ι_toBase i

@[reassoc]
lemma transE_ι {i j : (cover H).I₀} (h : i.1 ≤ j.1) :
    (transE h).left ≫ ι H j = ι H i :=
  colimit.w (gluingData H).functor (homOfLE h : i ⟶ j)

lemma exists_ι_eq (x : P H) : ∃ (i : (cover H).I₀) (y : V i), ι H i y = x :=
  (gluingData H).cover.exists_eq x

lemma pullbackHom_eq (i : (cover H).I₀) :
    (cover H).pullbackHom (π H) i = (isPullback_ι H i).flip.isoPullback.inv ≫ v i :=
  (IsPullback.isoPullback_inv_snd _).symm

instance : AlgebraicGeometry.Etale (π H) :=
  IsZariskiLocalAtTarget.of_openCover (cover H) fun i ↦ by
    rw [pullbackHom_eq]
    exact (MorphismProperty.cancel_left_of_respectsIso @AlgebraicGeometry.Etale _ _).2
      inferInstance

instance : IsFinite (π H) :=
  IsZariskiLocalAtTarget.of_openCover (cover H) fun i ↦ by
    rw [pullbackHom_eq]
    exact (MorphismProperty.cancel_left_of_respectsIso @IsFinite _ _).2 inferInstance

/-- The glued scheme as an étale `T`-scheme. -/
noncomputable abbrev PE : T.Etale := Etale.mk (π H ≫ u)

/-- The inclusion `V_i ⟶ P` as a morphism of étale `T`-schemes. -/
noncomputable abbrev ιE (i : (cover H).I₀) : Y i ⟶ PE H :=
  Over.homMk (ι H i) (by
    change ι H i ≫ π H ≫ u = v i ≫ i.1.ι ≫ u
    rw [ι_π_assoc])

section Factor

variable {Z : T.Etale} (g : Z.left ⟶ P H) (y : Z.left ⟶ U) (hy : g ≫ π H = y)
  (hZ : y ≫ u = Z.hom) (k : (cover H).I₀)

/-- The open of `Z` over which `g : Z ⟶ P` lands in the representing scheme over `k`. -/
noncomputable abbrev O : Z.left.Opens := y ⁻¹ᵁ k.1

include hy in
lemma exists_factor : ∃ h : (O H y k).toScheme ⟶ V k,
    h ≫ ι H k = (O H y k).ι ≫ g ∧ h ≫ v k = y ∣_ k.1 :=
  ⟨(isPullback_ι H k).lift (y ∣_ k.1) ((O H y k).ι ≫ g)
      (by rw [morphismRestrict_ι, Category.assoc, hy]),
    (isPullback_ι H k).lift_snd _ _ _, (isPullback_ι H k).lift_fst _ _ _⟩

/-- The factorisation of `g` through `V_k` over `O`, as a morphism of étale `T`-schemes. -/
noncomputable def factor : Etale.restrict Z (O H y k) ⟶ Y k :=
  Over.homMk (exists_factor H g y hy k).choose (by
    change _ ≫ v k ≫ k.1.ι ≫ u = (O H y k).ι ≫ Z.hom
    rw [reassoc_of% (exists_factor H g y hy k).choose_spec.2, morphismRestrict_ι_assoc, hZ])

lemma factor_left_ι : (factor H g y hy hZ k).left ≫ ι H k = (O H y k).ι ≫ g :=
  (exists_factor H g y hy k).choose_spec.1

lemma factor_left_v : (factor H g y hy hZ k).left ≫ v k = y ∣_ k.1 :=
  (exists_factor H g y hy k).choose_spec.2

/-- **Restricting a lift through `V_i` to the part lying over `k ≤ i`.** -/
lemma map_restrictι_comp {i : (cover H).I₀} (hki : k.1 ≤ i.1) (gi : Z ⟶ Y i)
    (hgi : gi.left ≫ ι H i = g) :
    E.map (Etale.restrictι Z (O H y k) ≫ gi).op (ξ i) = E.map (factor H g y hy hZ k).op (ξ k) := by
  have : Etale.restrictι Z (O H y k) ≫ gi = factor H g y hy hZ k ≫ transE hki := by
    refine Over.Hom.ext ((isPullback_ι H i).hom_ext ?_ ?_)
    · rw [← cancel_mono i.1.ι]
      change (O H y k).ι ≫ gi.left ≫ v i ≫ i.1.ι = (factor H g y hy hZ k).left ≫
        (transE hki).left ≫ v i ≫ i.1.ι
      rw [reassoc_of% (transE_left_v hki), Scheme.homOfLE_ι, reassoc_of% factor_left_v,
        morphismRestrict_ι, ← ι_π, reassoc_of% hgi, hy]
    · change (O H y k).ι ≫ gi.left ≫ ι H i = (factor H g y hy hZ k).left ≫
        (transE hki).left ≫ ι H i
      rw [transE_ι, factor_left_ι, hgi]
  rw [this, op_comp, Functor.map_comp_apply, map_transE]

end Factor

end GlueRepr

end AlgebraicGeometry.Scheme
