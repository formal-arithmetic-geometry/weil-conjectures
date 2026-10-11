/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.RepresentableLocallyConstant
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# Effective étale descent for finite étale morphisms

Let `p : Y' ⟶ Y` be a surjective étale morphism of schemes. A finite étale `Y'`-scheme `V`
with a descent datum relative to `p` (in the transport form `CategoryTheory.Over.DescentDatum`)
descends to a finite étale `Y`-scheme, and morphisms between base changes which are compatible
with the descent data descend uniquely. Together these say that base change along `p` is an
equivalence between finite étale `Y`-schemes and finite étale `Y'`-schemes with descent datum.

## Main statements

- `CategoryTheory.Over.DescentDatum.exists_isPullback_of_etale`: effectivity of descent data on
  finite étale schemes along a surjective étale morphism.
- `CategoryTheory.Over.DescentDatum.existsUnique_hom_of_isPullback_of_etale`: compatible
  morphisms descend uniquely along a surjective étale morphism.
- `AlgebraicGeometry.Scheme.FiniteEtale.galois_descent`: the two statements together
  (blueprint `lem-galois-descent`).

## Proof

Full faithfulness holds because the base change of a surjective étale morphism is an effective
epimorphism. For effectivity, the descent datum `D` on `V` defines a sheaf `F` on the small
étale site of `Y`: its sections over an étale `U ⟶ Y` are the `Y'`-morphisms
`U ×_Y Y' ⟶ V` compatible with `D`. It is a subsheaf of the pushforward along `p` of the sheaf
represented by `V`, the compatibility being a local condition. Over an étale `Y`-scheme `Z`
equipped with a factorisation `z : Z ⟶ Y'` of its structure morphism, the sections of `F` are the
morphisms `Z ⟶ V` over `z`, using the transport of `D`. Hence `F` is represented by a finite étale
scheme over every affine open of `Y` which admits a surjective étale map from an affine scheme
factoring through `p` (`AlgebraicGeometry.Scheme.Etale.exists_representableBy_of_isAffine`).
These opens form a basis, so `F` is represented by a finite étale `Y`-scheme `X`
(`AlgebraicGeometry.Scheme.Etale.exists_representableBy_of_isBasis`), and the section of `F`
over `V` given by the identity of `V` exhibits `V` as `X ×_Y Y'`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Over.DescentDatum

variable {C : Type*} [Category* C] {X Y : C} {p : X ⟶ Y} {V : Over X} (D : DescentDatum p V)

/-- The transport of a descent datum, on underlying morphisms: a morphism `b : T ⟶ V` over
`f₁` is sent to a morphism `T ⟶ V` over `f₂`. -/
def trLeft {T : C} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (b : T ⟶ V.left)
    (hb : b ≫ V.hom = f₁) : T ⟶ V.left :=
  (D.transport f₁ f₂ h (Over.homMk b hb)).left

@[reassoc (attr := simp)]
lemma trLeft_hom {T : C} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (b : T ⟶ V.left)
    (hb : b ≫ V.hom = f₁) : D.trLeft f₁ f₂ h b hb ≫ V.hom = f₂ :=
  Over.w (D.transport f₁ f₂ h (Over.homMk b hb))

lemma trLeft_congr {T : C} {f₁ f₂ f₁' f₂' : T ⟶ X} {h : f₁ ≫ p = f₂ ≫ p}
    {b b' : T ⟶ V.left} {hb : b ≫ V.hom = f₁} (e₁ : f₁ = f₁') (e₂ : f₂ = f₂') (e : b = b') :
    D.trLeft f₁ f₂ h b hb = D.trLeft f₁' f₂' (by rw [← e₁, ← e₂]; exact h) b'
      (by rw [← e, ← e₁]; exact hb) := by
  subst e₁ e₂ e
  rfl

lemma trLeft_of_eq {T : C} {f₁ f₂ : T ⟶ X} {h : f₁ ≫ p = f₂ ≫ p} {b : T ⟶ V.left}
    {hb : b ≫ V.hom = f₁} (e : f₁ = f₂) : D.trLeft f₁ f₂ h b hb = b := by
  subst e
  simp [trLeft, D.transport_self]

lemma trLeft_comp {T T' : C} (g : T' ⟶ T) {f₁ f₂ : T ⟶ X} (h : f₁ ≫ p = f₂ ≫ p)
    {b : T ⟶ V.left} (hb : b ≫ V.hom = f₁) {f₁' f₂' : T' ⟶ X} {b' : T' ⟶ V.left}
    (e₁ : f₁' = g ≫ f₁) (e₂ : f₂' = g ≫ f₂) (e : b' = g ≫ b) :
    D.trLeft f₁' f₂' (by rw [e₁, e₂, Category.assoc, Category.assoc, h]) b'
      (by rw [e, e₁, Category.assoc, hb]) = g ≫ D.trLeft f₁ f₂ h b hb := by
  subst e₁ e₂ e
  have := D.transport_homMk_comp g f₁ f₂ h (Over.homMk b hb)
  have e : (Over.homMk g : Over.mk (g ≫ f₁) ⟶ Over.mk f₁) ≫ Over.homMk b hb =
      Over.homMk (g ≫ b) (by simp [hb]) := by
    ext
    simp
  rw [e] at this
  exact congrArg CommaMorphism.left this

lemma trLeft_trLeft {T : C} {f₁ f₂ f₃ : T ⟶ X} (h₁₂ : f₁ ≫ p = f₂ ≫ p)
    (h₂₃ : f₂ ≫ p = f₃ ≫ p) {b : T ⟶ V.left} (hb : b ≫ V.hom = f₁) :
    D.trLeft f₂ f₃ h₂₃ (D.trLeft f₁ f₂ h₁₂ b hb) (D.trLeft_hom _ _ _ _ _) =
      D.trLeft f₁ f₃ (h₁₂.trans h₂₃) b hb := by
  have e : (Over.homMk (D.trLeft f₁ f₂ h₁₂ b hb) (D.trLeft_hom _ _ _ _ _) :
      Over.mk f₂ ⟶ V) = D.transport f₁ f₂ h₁₂ (Over.homMk b hb) := by
    ext
    rfl
  change (D.transport f₂ f₃ h₂₃ (Over.homMk (D.trLeft f₁ f₂ h₁₂ b hb) _)).left = _
  rw [e, D.transport_transport]
  rfl

end CategoryTheory.Over.DescentDatum

namespace AlgebraicGeometry.Scheme

/-- Morphisms out of a scheme agreeing on a jointly surjective family of étale morphisms are
equal: the étale topology is subcanonical. -/
lemma Hom.ext_of_etale {T S : Scheme.{u}} {ι : Type*} {Z : ι → Scheme.{u}} (π : ∀ i, Z i ⟶ T)
    [∀ i, AlgebraicGeometry.Etale (π i)] (hπ : ∀ x, ∃ i, x ∈ Set.range (π i)) {a b : T ⟶ S}
    (h : ∀ i, π i ≫ a = π i ≫ b) : a = b := by
  have hS : Sieve.ofArrows Z π ∈ etaleTopology T :=
    Precoverage.generate_mem_toGrothendieck
      ((ofArrows_mem_precoverage_iff (P := @AlgebraicGeometry.Etale)).2 ⟨hπ, fun i ↦ inferInstance⟩)
  have hF := (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := etaleTopology) (yoneda.obj S))
  refine (hF _ hS).isSeparatedFor.ext ?_
  rintro W g ⟨_, f, _, ⟨i⟩, rfl⟩
  change (f ≫ π i) ≫ a = (f ≫ π i) ≫ b
  rw [Category.assoc, Category.assoc, h i]

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.EtaleDescent

variable {Y Y' : Scheme.{u}} {p : Y' ⟶ Y} {V : Over Y'} (D : Over.DescentDatum p V)

/-- A `Y'`-morphism `a : U ×_Y Y' ⟶ V` is *compatible* with the descent datum `D` if for any two
points `t₁, t₂` of `U ×_Y Y'` with the same image in `U`, the transport by `D` of `a ∘ t₁` is
`a ∘ t₂`. -/
def Compat {U : Scheme.{u}} {g : U ⟶ Y} (a : pullback g p ⟶ V.left)
    (ha : a ≫ V.hom = pullback.snd g p) : Prop :=
  ∀ ⦃T : Scheme.{u}⦄ (t₁ t₂ : T ⟶ pullback g p)
    (h : t₁ ≫ pullback.fst g p = t₂ ≫ pullback.fst g p),
    D.trLeft (t₁ ≫ pullback.snd g p) (t₂ ≫ pullback.snd g p)
      (by simp only [Category.assoc, ← pullback.condition, reassoc_of% h])
      (t₁ ≫ a) (by simp [ha]) = t₂ ≫ a

variable [AlgebraicGeometry.Etale V.hom]

/-- The presheaf `U ↦ Hom_{Y'}(U ×_Y Y', V)` on the small étale site of `Y`. -/
noncomputable abbrev ambient : Y.Etaleᵒᵖ ⥤ Type u :=
  p.Etale.op ⋙ yoneda.obj (Etale.mk V.hom)

omit [AlgebraicGeometry.Etale V.hom] in
lemma etale_map_left_fst {U₁ U₂ : Y.Etale} (g : U₂ ⟶ U₁) :
    (p.Etale.map g).left ≫ pullback.fst U₁.hom p = pullback.fst U₂.hom p ≫ g.left :=
  pullback.lift_fst _ _ _

omit [AlgebraicGeometry.Etale V.hom] in
lemma etale_map_left_snd {U₁ U₂ : Y.Etale} (g : U₂ ⟶ U₁) :
    (p.Etale.map g).left ≫ pullback.snd U₁.hom p = pullback.snd U₂.hom p :=
  pullback.lift_snd _ _ _

/-- The subpresheaf of `ambient` of morphisms compatible with the descent datum. -/
noncomputable def subfunctor : Subfunctor (ambient (p := p) (V := V)) where
  obj U := {a | Compat D a.left (MorphismProperty.Over.w a)}
  map {U₁ U₂} g a ha := by
    intro T t₁ t₂ h
    change D.trLeft _ _ _ (t₁ ≫ (p.Etale.map g.unop).left ≫ a.left) _ =
      t₂ ≫ (p.Etale.map g.unop).left ≫ a.left
    have h' : (t₁ ≫ (p.Etale.map g.unop).left) ≫ pullback.fst _ p =
        (t₂ ≫ (p.Etale.map g.unop).left) ≫ pullback.fst _ p := by
      simp only [Category.assoc, etale_map_left_fst, reassoc_of% h]
    refine (D.trLeft_congr ?_ ?_ (Category.assoc _ _ _).symm).trans
      ((ha _ _ h').trans (Category.assoc _ _ _))
    · simp [etale_map_left_snd]
    · simp [etale_map_left_snd]

lemma isSheaf_ambient : Presieve.IsSheaf Y.smallEtaleTopology (ambient (p := p) (V := V)) :=
  p.Etale.op_comp_isSheaf_of_isSheaf_type _
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := Y'.smallEtaleTopology) _)

lemma isSheaf_subfunctor : Presieve.IsSheaf Y.smallEtaleTopology (subfunctor D).toFunctor := by
  refine ((subfunctor D).isSheaf_iff isSheaf_ambient).2 fun U a ha ↦ ?_
  rw [mem_smallEtaleTopology_iff] at ha
  intro T t₁ t₂ h
  choose W g hg hx using fun x : T ↦ ha ((t₁ ≫ pullback.fst _ p) x)
  have : ∀ x, AlgebraicGeometry.Etale (g x).left := fun x ↦ by
    have : AlgebraicGeometry.Etale ((g x).left ≫ U.unop.hom) := by
      rw [MorphismProperty.Over.w]; exact (W x).prop
    exact AlgebraicGeometry.Etale.of_comp _ U.unop.hom
  let π (x : T) : pullback (t₁ ≫ pullback.fst _ p) (g x).left ⟶ T := pullback.fst _ _
  refine Hom.ext_of_etale π (fun x ↦ ?_) fun x ↦ ?_
  · obtain ⟨w, hw⟩ := hx x
    obtain ⟨z, hz, -⟩ := Pullback.exists_preimage_pullback x w hw.symm
    exact ⟨x, z, hz⟩
  · have hc : Compat D ((p.Etale.map (g x)).left ≫ a.left)
        (MorphismProperty.Over.w (p.Etale.map (g x) ≫ a)) := hg x
    have hw (t : T ⟶ pullback U.unop.hom p) (ht : t ≫ pullback.fst _ p = t₁ ≫ pullback.fst _ p) :
        pullback.snd (t₁ ≫ pullback.fst _ p) (g x).left ≫ (W x).hom =
          (π x ≫ t ≫ pullback.snd _ p) ≫ p := by
      rw [← MorphismProperty.Over.w (g x), ← pullback.condition_assoc, Category.assoc,
        Category.assoc, Category.assoc, ← pullback.condition, reassoc_of% ht]
    let s (t : T ⟶ pullback U.unop.hom p) (ht : t ≫ pullback.fst _ p = t₁ ≫ pullback.fst _ p) :
        pullback (t₁ ≫ pullback.fst _ p) (g x).left ⟶ pullback (W x).hom p :=
      pullback.lift (pullback.snd _ _) (π x ≫ t ≫ pullback.snd _ p) (hw t ht)
    have hs (t : T ⟶ pullback U.unop.hom p) (ht : t ≫ pullback.fst _ p = t₁ ≫ pullback.fst _ p) :
        s t ht ≫ (p.Etale.map (g x)).left = π x ≫ t := by
      apply pullback.hom_ext
      · simp only [Category.assoc, etale_map_left_fst, s, pullback.lift_fst_assoc, ht]
        rw [← pullback.condition]
      · simp [etale_map_left_snd, s]
    have := hc (s t₁ rfl) (s t₂ h.symm) (by simp [s])
    refine (D.trLeft_comp (π x) _ _ rfl rfl rfl).symm.trans
      ((D.trLeft_congr ?_ ?_ ?_).trans (this.trans (by rw [reassoc_of% (hs t₂ h.symm)])))
    · simp [s]
    · simp [s]
    · rw [reassoc_of% (hs t₁ rfl)]

/-- The sheaf on the small étale site of `Y` of morphisms `U ×_Y Y' ⟶ V` over `Y'` compatible
with the descent datum `D`. -/
noncomputable def sheaf : Sheaf Y.smallEtaleTopology (Type u) :=
  ⟨(subfunctor D).toFunctor, (isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_subfunctor D)⟩


/-! ### Sections over a scheme with a point of `Y'` -/

variable {D}

lemma compat {Z : Y.Etale} (a : (sheaf D).obj.obj (op Z)) :
    Compat D a.1.left (MorphismProperty.Over.w a.1) :=
  a.2

/-- The morphism `Z ⟶ V` over `z : Z ⟶ Y'` corresponding to a section of `sheaf D` over `Z`. -/
noncomputable def toPt {Z : Y.Etale} (z : Z.left ⟶ Y') (hz : z ≫ p = Z.hom)
    (a : (sheaf D).obj.obj (op Z)) : Z.left ⟶ V.left :=
  pullback.lift (𝟙 _) z (by simp [hz]) ≫ a.1.left

@[reassoc (attr := simp)]
lemma toPt_hom {Z : Y.Etale} (z : Z.left ⟶ Y') (hz : z ≫ p = Z.hom)
    (a : (sheaf D).obj.obj (op Z)) : toPt z hz a ≫ V.hom = z := by
  have h : a.1.left ≫ V.hom = pullback.snd Z.hom p := MorphismProperty.Over.w a.1
  rw [toPt, Category.assoc, h]
  exact pullback.lift_snd _ _ _

variable (D) in
/-- The section of `sheaf D` over `Z` corresponding to a morphism `b : Z ⟶ V` over
`z : Z ⟶ Y'`: it sends a point `(x, y')` of `Z ×_Y Y'` to the transport of `b x` to `y'`. -/
noncomputable def ofPtLeft {Z : Y.Etale} (z : Z.left ⟶ Y') (hz : z ≫ p = Z.hom)
    (b : Z.left ⟶ V.left) (hb : b ≫ V.hom = z) : pullback Z.hom p ⟶ V.left :=
  D.trLeft (pullback.fst Z.hom p ≫ z) (pullback.snd Z.hom p)
    (by rw [Category.assoc, hz, pullback.condition]) (pullback.fst _ _ ≫ b)
    (by rw [Category.assoc, hb])

lemma compat_ofPtLeft {Z : Y.Etale} (z : Z.left ⟶ Y') (hz : z ≫ p = Z.hom)
    (b : Z.left ⟶ V.left) (hb : b ≫ V.hom = z) :
    Compat D (ofPtLeft D z hz b hb) (D.trLeft_hom _ _ _ _ _) := by
  intro T t₁ t₂ h
  have e₁ : t₁ ≫ ofPtLeft D z hz b hb = D.trLeft (t₁ ≫ pullback.fst _ p ≫ z)
      (t₁ ≫ pullback.snd _ p) (by simp [hz, pullback.condition]) (t₁ ≫ pullback.fst _ p ≫ b)
      (by simp [hb]) :=
    (D.trLeft_comp t₁ _ _ rfl rfl rfl).symm
  refine (D.trLeft_congr rfl rfl e₁).trans ((D.trLeft_trLeft _ _ _).trans ?_)
  exact (D.trLeft_congr (by rw [reassoc_of% h]) rfl (by rw [reassoc_of% h])).trans
    (D.trLeft_comp t₂ _ _ rfl rfl rfl)

/-- The section of `sheaf D` over `Z` corresponding to a morphism `b : Z ⟶ V` over
`z : Z ⟶ Y'`. -/
noncomputable def ofPt {Z : Y.Etale} (z : Z.left ⟶ Y') (hz : z ≫ p = Z.hom)
    (b : Z.left ⟶ V.left) (hb : b ≫ V.hom = z) : (sheaf D).obj.obj (op Z) :=
  ⟨Etale.homMk (ofPtLeft D z hz b hb) (D.trLeft_hom _ _ _ _ _), compat_ofPtLeft z hz b hb⟩

lemma ofPt_congr {Z : Y.Etale} (z : Z.left ⟶ Y') (hz : z ≫ p = Z.hom)
    {b b' : Z.left ⟶ V.left} (hb : b ≫ V.hom = z) (hb' : b' ≫ V.hom = z) (e : b = b') :
    ofPt (D := D) z hz b hb = ofPt z hz b' hb' := by
  subst e
  rfl

@[simp]
lemma toPt_ofPt {Z : Y.Etale} (z : Z.left ⟶ Y') (hz : z ≫ p = Z.hom)
    (b : Z.left ⟶ V.left) (hb : b ≫ V.hom = z) : toPt z hz (ofPt (D := D) z hz b hb) = b := by
  change pullback.lift (𝟙 _) z _ ≫ ofPtLeft D z hz b hb = b
  refine (D.trLeft_comp _ _ _ rfl rfl rfl).symm.trans
    ((D.trLeft_congr (f₁' := z) (f₂' := z) (b' := b) ?_ ?_ ?_).trans (D.trLeft_of_eq rfl))
  · simp <;> exact Category.id_comp _
  · simp
  · simp <;> exact Category.id_comp _

@[simp]
lemma ofPt_toPt {Z : Y.Etale} (z : Z.left ⟶ Y') (hz : z ≫ p = Z.hom)
    (a : (sheaf D).obj.obj (op Z)) : ofPt z hz (toPt z hz a) (toPt_hom z hz a) = a := by
  apply Subtype.ext
  apply Etale.hom_ext
  change ofPtLeft D z hz (toPt z hz a) (toPt_hom z hz a) = a.1.left
  have := compat a (pullback.fst Z.hom p ≫ pullback.lift (𝟙 _) z (by simp [hz])) (𝟙 _)
    (by simp)
  refine (D.trLeft_congr ?_ ?_ ?_).trans (this.trans (Category.id_comp _))
  · simp
  · simp
  · simp [toPt]

lemma toPt_injective {Z : Y.Etale} (z : Z.left ⟶ Y') (hz : z ≫ p = Z.hom)
    {a a' : (sheaf D).obj.obj (op Z)} (h : toPt z hz a = toPt z hz a') : a = a' :=
  calc a = ofPt z hz (toPt z hz a) (toPt_hom z hz a) := (ofPt_toPt z hz a).symm
    _ = ofPt z hz (toPt z hz a') (toPt_hom z hz a') := ofPt_congr z hz _ _ h
    _ = a' := ofPt_toPt z hz a'

/-- `toPt` is natural in the étale `Y`-scheme. -/
lemma toPt_map {Z₁ Z₂ : Y.Etale} (g : Z₁ ⟶ Z₂) (z₂ : Z₂.left ⟶ Y') (hz₂ : z₂ ≫ p = Z₂.hom)
    (z₁ : Z₁.left ⟶ Y') (hz₁ : z₁ ≫ p = Z₁.hom) (e : z₁ = g.left ≫ z₂)
    (a : (sheaf D).obj.obj (op Z₂)) :
    toPt z₁ hz₁ ((sheaf D).obj.map g.op a) = g.left ≫ toPt z₂ hz₂ a := by
  change pullback.lift (𝟙 _) z₁ _ ≫ (p.Etale.map g).left ≫ a.1.left =
    g.left ≫ pullback.lift (𝟙 _) z₂ _ ≫ a.1.left
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp [etale_map_left_fst] <;> exact Category.id_comp _
  · simp [etale_map_left_snd, e]

/-- Changing the point of `Y'` transports the morphism `toPt` by the descent datum. -/
lemma toPt_eq_trLeft {Z : Y.Etale} (z z' : Z.left ⟶ Y') (hz : z ≫ p = Z.hom)
    (hz' : z' ≫ p = Z.hom) (a : (sheaf D).obj.obj (op Z)) :
    toPt z' hz' a = D.trLeft z z' (hz.trans hz'.symm) (toPt z hz a) (toPt_hom z hz a) := by
  have := compat a (pullback.lift (𝟙 _) z (by simp [hz])) (pullback.lift (𝟙 _) z' (by simp [hz']))
    (by simp)
  exact this.symm.trans (D.trLeft_congr (by simp) (by simp) rfl)


/-! ### Representability over a scheme with a point of `Y'` -/

section Representation

variable {W : Y.Etale} (w : W.left ⟶ Y') (hw : w ≫ p = W.hom)

omit [AlgebraicGeometry.Etale V.hom] in
lemma etale_snd_comp [AlgebraicGeometry.Etale V.hom] :
    AlgebraicGeometry.Etale (pullback.snd V.hom w ≫ W.hom) := by
  have : AlgebraicGeometry.Etale W.hom := W.prop
  infer_instance

/-- `V ×_{Y'} W` as an étale `Y`-scheme over `W`. -/
noncomputable def overW : Over W :=
  haveI := etale_snd_comp (V := V) w
  Over.mk (Etale.homMk (pullback.snd V.hom w) rfl :
    Etale.mk (pullback.snd V.hom w ≫ W.hom) ⟶ W)

lemma overW_hom_left : (overW (V := V) w).hom.left = pullback.snd V.hom w :=
  rfl

instance [IsFinite V.hom] : IsFinite (overW (V := V) w).hom.left :=
  inferInstanceAs (IsFinite (pullback.snd V.hom w))

lemma left_left_snd {Z : Over W} (φ : Z ⟶ overW (V := V) w) :
    φ.left.left ≫ pullback.snd V.hom w = Z.hom.left :=
  congrArg (fun f ↦ f.left) (Over.w φ)

include hw in
lemma hzW (Z : Over W) : (Z.hom.left ≫ w) ≫ p = Z.left.hom := by
  rw [Category.assoc, hw]
  exact MorphismProperty.Over.w Z.hom

variable (D) in
/-- Morphisms `Z ⟶ V ×_{Y'} W` over `W` are the sections of `sheaf D` over `Z`. -/
noncomputable def homEquivW (Z : Over W) :
    (Z ⟶ overW (V := V) w) ≃ (sheaf D).obj.obj (op Z.left) where
  toFun φ := ofPt (Z.hom.left ≫ w) (hzW w hw Z) (φ.left.left ≫ pullback.fst V.hom w)
    (by rw [Category.assoc, pullback.condition, reassoc_of% (left_left_snd w φ)])
  invFun s := Over.homMk (Etale.homMk (pullback.lift (toPt _ (hzW w hw Z) s) Z.hom.left
      (toPt_hom _ _ s)) (by
        change pullback.lift _ _ _ ≫ pullback.snd V.hom w ≫ W.hom = Z.left.hom
        rw [pullback.lift_snd_assoc]
        exact MorphismProperty.Over.w Z.hom)) (by
      apply Etale.hom_ext
      exact pullback.lift_snd _ _ _)
  left_inv φ := by
    apply Over.OverMorphism.ext
    apply Etale.hom_ext
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans (toPt_ofPt _ _ _ _)
    · exact (pullback.lift_snd _ _ _).trans (left_left_snd w φ).symm
  right_inv s := by
    refine (ofPt_congr _ _ _ (toPt_hom _ _ s) ?_).trans (ofPt_toPt _ _ s)
    exact pullback.lift_fst _ _ _

variable (D) in
/-- The restriction of `sheaf D` to étale `Y`-schemes over `W` is represented by `V ×_{Y'} W`. -/
noncomputable def representableByW :
    ((Over.forget W).op ⋙ (sheaf D).obj).RepresentableBy (overW (V := V) w) where
  homEquiv {Z} := homEquivW D w hw Z
  homEquiv_comp {Z' Z} f φ := by
    apply toPt_injective (Z'.hom.left ≫ w) (hzW w hw Z')
    change toPt _ _ (ofPt _ _ _ _) = toPt _ _ ((sheaf D).obj.map f.left.op (ofPt _ _ _ _))
    rw [toPt_ofPt, toPt_map f.left (Z.hom.left ≫ w) (hzW w hw Z), toPt_ofPt]
    · simp
    · rw [← Category.assoc]
      exact congrArg (· ≫ w) (congrArg (fun g ↦ g.left) (Over.w f)).symm

end Representation

/-! ### Effectivity -/

omit [AlgebraicGeometry.Etale V.hom] in
lemma trLeft_left {T : Scheme.{u}} (f₁ f₂ : T ⟶ Y') (h : f₁ ≫ p = f₂ ≫ p)
    (a : Over.mk f₁ ⟶ V) : D.trLeft f₁ f₂ h a.left (Over.w a) = (D.transport f₁ f₂ h a).left := by
  have : (Over.homMk a.left (Over.w a) : Over.mk f₁ ⟶ V) = a := by
    ext
    rfl
  unfold Over.DescentDatum.trLeft
  rw [this]

variable (D) in
/-- **Effective étale descent for finite étale schemes**: a finite étale `Y'`-scheme `V` with a
descent datum relative to a surjective étale morphism `p : Y' ⟶ Y` is the base change of a finite
étale `Y`-scheme `X`, through a morphism `q : V ⟶ X` which is invariant under the transport. -/
theorem exists_isPullback [AlgebraicGeometry.Etale p] [Surjective p] [IsFinite V.hom] :
    ∃ (X : Y.Etale) (q : V.left ⟶ X.left), IsFinite X.hom ∧ IsPullback q V.hom X.hom p ∧
      ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ Y') (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
        (D.transport f₁ f₂ h a).left ≫ q = a.left ≫ q := by
  let 𝔅 : Set Y.Opens := {U | IsAffineOpen U ∧ ∃ (W : Scheme.{u}) (_ : IsAffine W) (q : W ⟶ Y')
    (_ : AlgebraicGeometry.Etale q) (pU : W ⟶ U.toScheme), pU ≫ U.ι = q ≫ p ∧ Surjective pU}
  have h𝔅 : TopologicalSpace.Opens.IsBasis 𝔅 := by
    rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro O y hy
    obtain ⟨U, hU, hyU, hUO, W, hW, q, hq, pU, hpq, hp⟩ :=
      exists_isAffineOpen_surjective_etale p hy (p.surjective y)
    exact ⟨U, ⟨hU, W, hW, q, hq, pU, hpq, hp⟩, hyU, hUO⟩
  obtain ⟨X, hX, ⟨r⟩⟩ := Etale.exists_representableBy_of_isBasis (sheaf D) 𝔅 h𝔅 fun U ↦ by
    obtain ⟨hU, W, hW, q, hq, pU, hpq, hp⟩ := U.2
    have : IsAffine (openObj U.1).left := hU
    let WE : Y.Etale := Etale.mk (q ≫ p)
    have : IsAffine WE.left := hW
    let pE : WE ⟶ openObj U.1 := Etale.homMk pU hpq
    have : Surjective pE.left := hp
    exact Etale.exists_representableBy_of_isAffine (sheaf D) pE (overW (V := V) (W := WE) q)
      (representableByW D q rfl)
  have : AlgebraicGeometry.Etale X.hom := X.prop
  -- the section of `sheaf D` over `V` given by the identity of `V`
  let VE : Y.Etale := Etale.mk (V.hom ≫ p)
  let e : (sheaf D).obj.obj (op VE) := ofPt (Z := VE) V.hom rfl (𝟙 _) (Category.id_comp _)
  let qE : VE ⟶ X := r.homEquiv.symm e
  have hqE : r.homEquiv qE = e := r.homEquiv.apply_symm_apply e
  have hcomm : qE.left ≫ X.hom = V.hom ≫ p := MorphismProperty.Over.w qE
  -- the inverse of `V ⟶ X ×_Y Y'`
  let ZE : Y.Etale := Etale.mk (pullback.fst X.hom p ≫ X.hom)
  let fstE : ZE ⟶ X := Etale.homMk (pullback.fst X.hom p) rfl
  have hzZ : pullback.snd X.hom p ≫ p = ZE.hom := pullback.condition.symm
  let ψ := toPt (Z := ZE) (pullback.snd X.hom p) hzZ (r.homEquiv fstE)
  let φ := pullback.lift qE.left V.hom hcomm
  let φE : VE ⟶ ZE := Etale.homMk φ (by
    change φ ≫ pullback.fst X.hom p ≫ X.hom = V.hom ≫ p
    rw [pullback.lift_fst_assoc]
    exact hcomm)
  let ψE : ZE ⟶ VE := Etale.homMk ψ (by
    change ψ ≫ V.hom ≫ p = pullback.fst X.hom p ≫ X.hom
    rw [toPt_hom_assoc]
    exact hzZ)
  have h1 : φ ≫ ψ = 𝟙 _ := by
    have hφ : φE ≫ fstE = qE := Etale.hom_ext (pullback.lift_fst _ _ _)
    calc φ ≫ ψ = toPt V.hom rfl ((sheaf D).obj.map φE.op (r.homEquiv fstE)) :=
          (toPt_map φE _ hzZ V.hom rfl (pullback.lift_snd _ _ _).symm _).symm
      _ = toPt V.hom rfl e := by rw [← r.homEquiv_comp, hφ, hqE]
      _ = 𝟙 _ := toPt_ofPt _ _ _ _
  have h2 : ψ ≫ qE.left = pullback.fst X.hom p := by
    have : ψE ≫ qE = fstE := by
      apply r.homEquiv.injective
      rw [r.homEquiv_comp, hqE]
      apply toPt_injective (pullback.snd X.hom p) hzZ
      rw [toPt_map ψE V.hom rfl _ hzZ (toPt_hom _ _ _).symm]
      exact (Category.comp_id _).trans rfl
    exact congrArg (fun f ↦ f.left) this
  have h3 : ψ ≫ φ = 𝟙 _ := pullback.hom_ext (by simp [φ, h2]) (by simp [φ, ψ])
  let i : V.left ≅ pullback X.hom p := ⟨φ, ψ, h1, h3⟩
  refine ⟨X, qE.left, hX, IsPullback.of_iso_pullback ⟨hcomm⟩ i (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _), ?_⟩
  -- invariance of `q` under the transport
  let PE : Y.Etale := Etale.mk (pullback.fst (V.hom ≫ p) p ≫ V.hom ≫ p)
  have hzP : pullback.snd (V.hom ≫ p) p ≫ p = PE.hom := pullback.condition.symm
  have he : e.1.left ≫ V.hom = pullback.snd (V.hom ≫ p) p := MorphismProperty.Over.w e.1
  let fE : PE ⟶ VE := Etale.homMk (pullback.fst _ _) rfl
  let aE : PE ⟶ VE := Etale.homMk e.1.left (by
    change e.1.left ≫ V.hom ≫ p = pullback.fst (V.hom ≫ p) p ≫ V.hom ≫ p
    rw [reassoc_of% he]
    exact hzP)
  have hfa : (sheaf D).obj.map fE.op e = (sheaf D).obj.map aE.op e := by
    apply toPt_injective (pullback.snd (V.hom ≫ p) p) hzP
    rw [toPt_map aE V.hom rfl _ hzP he.symm, toPt_ofPt,
      toPt_eq_trLeft (pullback.fst (V.hom ≫ p) p ≫ V.hom) _ (by rw [Category.assoc]; rfl) hzP]
    refine (D.trLeft_congr rfl rfl ?_).trans (Category.comp_id _).symm
    rw [toPt_map fE V.hom rfl _ _ rfl, toPt_ofPt]
  have hfa' : pullback.fst (V.hom ≫ p) p ≫ qE.left = e.1.left ≫ qE.left := by
    have : fE ≫ qE = aE ≫ qE := by
      apply r.homEquiv.injective
      rw [r.homEquiv_comp, r.homEquiv_comp, hfa]
    exact congrArg (fun f ↦ f.left) this
  intro T f₁ f₂ h a
  let t : T ⟶ pullback (V.hom ≫ p) p := pullback.lift a.left f₂ (by
    rw [← Category.assoc, Over.w a]
    exact h)
  have ht : t ≫ e.1.left = (D.transport f₁ f₂ h a).left := by
    refine (D.trLeft_comp t _ _ rfl rfl rfl).symm.trans ?_
    refine (D.trLeft_congr ?_ ?_ ?_).trans (trLeft_left D f₁ f₂ h a)
    · simp [t]
    · simp [t]
    · simp [t]
  rw [← ht, Category.assoc, ← hfa', pullback.lift_fst_assoc]

end AlgebraicGeometry.Scheme.EtaleDescent
