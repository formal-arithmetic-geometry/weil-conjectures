/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.AlgebraicGeometry.Sites.AgreementLocus
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkUnit

/-!
# Sections of a pullback along a morphism with connected fibres

Let `p : X ⟶ S` be a morphism of schemes, `G` an étale sheaf on `S`, `V` an étale `S`-scheme,
`W` an étale `X`-scheme and `φ : W ⟶ V ×_S X` a morphism of étale `X`-schemes, so that
`W ⟶ X ⟶ S` factors through `q : W ⟶ V`. The unit of `p^* ⊣ p_*` gives a map
`G(V) ⟶ (p^* G)(W)` (`AlgebraicGeometry.Etale.upperStarSectionsMap`). If `q` is flat,
quasi-compact and has geometrically connected fibres, this map is bijective [Stacks 0A3H].

## Proof

We argue with germs at geometric points and agreement loci of sections
(`AlgebraicGeometry.Etale.agreementLocus`), avoiding fpqc descent.

* The germ of the image of `t ∈ G(V)` at a geometric point `x` of `W` is the germ of `t` at
  `q ∘ x` (`AlgebraicGeometry.Etale.toPresheafFiber_upperStarSectionsMap`); hence the images
  of `t₁, t₂` agree at `x` iff `t₁, t₂` agree at `q x`. As `q` is surjective, the map is
  injective.
* Every section `σ` of `p^* G` over `W` is, near any point, the image of a section of `G` over
  an étale `V' ⟶ V`, after base change to `W ×_V V'`.
* For two sections `a, b` of `p^* G` over `W`, the set of points of a fibre `q⁻¹(y)` where
  they agree is open and closed in the fibre: near a point it is read off from the agreement
  of two sections of `G` at a single point of the discrete fibre over `y` of an étale
  `V' ⟶ V`. As the fibres are connected, `a` and `b` agree on all or on none of a fibre.
* So the agreement locus `U` of `σ` with the image of a local section `c` is saturated for
  `q`; since a flat quasi-compact surjection is a quotient map, `q(U)` is open, and on
  `q(U)` the section `c` pulls back to `σ`. These local sections glue by injectivity.

## Main definitions

- `AlgebraicGeometry.Etale.upperStarSectionsMap`: the map `G(V) ⟶ (p^* G)(W)`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_upperStarSectionsMap`: it is bijective when `q` is flat,
  quasi-compact with geometrically connected fibres [Stacks 0A3H].
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

section Def

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
variable {X S : Scheme.{u}}

variable (p : X ⟶ S) in
/-- For a sheaf `G` on `S_ét`, an étale `S`-scheme `V`, an étale `X`-scheme `W` and a morphism
`φ : W ⟶ V ×_S X` of étale `X`-schemes, the map `G(V) ⟶ (p^* G)(W)`: the unit of
`p^* ⊣ p_*` at `V`, landing in `(p_* p^* G)(V) = (p^* G)(V ×_S X)`, followed by the restriction
along `φ`.

When `W ⟶ V` is flat, quasi-compact and has geometrically connected fibres, this map is
bijective, see `AlgebraicGeometry.Etale.isIso_upperStarSectionsMap`. -/
noncomputable def Etale.upperStarSectionsMap (G : Sheaf S.smallEtaleTopology A) {V : S.Etale}
    {W : X.Etale} (φ : W ⟶ (MorphismProperty.Over.pullback @Etale ⊤ p).obj V) :
    G.obj.obj (op V) ⟶ ((p)^*[A].obj G).obj.obj (op W) :=
  ((Etale.upperStarLowerStarAdjunction A p).unit.app G).hom.app (op V) ≫
    ((p)^*[A].obj G).obj.map φ.op

variable {A} {p : X ⟶ S}

omit [HasSmallSiteSheafify A] in
/-- The maps `Etale.upperStarSectionsMap` are natural: for `f : V' ⟶ V`, `ψ : W' ⟶ W` and
`φ' : W' ⟶ V' ×_S X` compatible with `φ`, restricting along `f` and then mapping by `φ'` is
mapping by `φ` and then restricting along `ψ`. -/
@[reassoc]
lemma Etale.upperStarSectionsMap_naturality (G : Sheaf S.smallEtaleTopology A)
    {V V' : S.Etale} {W W' : X.Etale}
    (φ : W ⟶ (MorphismProperty.Over.pullback @Etale ⊤ p).obj V)
    (φ' : W' ⟶ (MorphismProperty.Over.pullback @Etale ⊤ p).obj V') (f : V' ⟶ V) (ψ : W' ⟶ W)
    (h : φ' ≫ (MorphismProperty.Over.pullback @Etale ⊤ p).map f = ψ ≫ φ) :
    G.obj.map f.op ≫ Etale.upperStarSectionsMap A p G φ' =
      Etale.upperStarSectionsMap A p G φ ≫ ((p)^*[A].obj G).obj.map ψ.op := by
  have hn := ((Etale.upperStarLowerStarAdjunction A p).unit.app G).hom.naturality f.op
  simp only [Functor.id_obj, Functor.comp_obj] at hn
  simp only [Etale.upperStarSectionsMap]
  rw [← Category.assoc, hn, Category.assoc, Category.assoc, Etale.lowerStar_obj_val_map,
    ← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, h]

end Def
/-- Every point of a scheme is the image of a geometric point, with values in a separably
closed field of the same universe. -/
lemma Scheme.exists_geometricPoint (Z : Scheme.{u}) (z : Z) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsSepClosed Ω) (x : Spec (.of Ω) ⟶ Z), x default = z :=
  ⟨AlgebraicClosure (Z.residueField z), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z)
      (AlgebraicClosure (Z.residueField z)))) ≫ Z.fromSpecResidueField z, by
    rw [Scheme.Hom.comp_apply]
    exact Z.fromSpecResidueField_apply z _⟩

section Agreement

variable {Y : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ]
  {F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}

lemma Etale.agreementLocus_comm {T : Y.Etale} (a b : F.obj.obj (op T)) :
    Etale.agreementLocus F a b = Etale.agreementLocus F b a := by
  ext z
  exact ⟨fun ⟨U, f, hz, h⟩ ↦ ⟨U, f, hz, h.symm⟩, fun ⟨U, f, hz, h⟩ ↦ ⟨U, f, hz, h.symm⟩⟩

lemma Etale.mem_agreementLocus_trans {T : Y.Etale} {a b c : F.obj.obj (op T)} {z : T.left}
    (hab : z ∈ Etale.agreementLocus F a b) (hbc : z ∈ Etale.agreementLocus F b c) :
    z ∈ Etale.agreementLocus F a c := by
  obtain ⟨U, f, ⟨u, hu⟩, h₁⟩ := hab
  obtain ⟨U', f', ⟨u', hu'⟩, h₂⟩ := hbc
  obtain ⟨Z, p₁, p₂, z', hp, hz₁, -⟩ := exists_eq_of_apply_eq f f' u u' (hu.trans hu'.symm)
  refine ⟨Z, p₁ ≫ f, ⟨z', by rw [← hu, ← hz₁]; rfl⟩, ?_⟩
  have e₁ := congrArg (F.obj.map p₁.op) h₁
  have e₂ := congrArg (F.obj.map p₂.op) h₂
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp] at e₁ e₂
  rw [e₁, hp, e₂]

/-- Agreement at a point only depends on the sections near it: if `a = a'` and `b = b'` at `z`,
then `a, b` agree at `z` iff `a', b'` do. -/
lemma Etale.mem_agreementLocus_congr {T : Y.Etale} {a a' b b' : F.obj.obj (op T)} {z : T.left}
    (ha : z ∈ Etale.agreementLocus F a a') (hb : z ∈ Etale.agreementLocus F b b') :
    z ∈ Etale.agreementLocus F a b ↔ z ∈ Etale.agreementLocus F a' b' := by
  have ha' : z ∈ Etale.agreementLocus F a' a := Etale.agreementLocus_comm a a' ▸ ha
  have hb' : z ∈ Etale.agreementLocus F b' b := Etale.agreementLocus_comm b b' ▸ hb
  exact ⟨fun h ↦ Etale.mem_agreementLocus_trans (Etale.mem_agreementLocus_trans ha' h) hb,
    fun h ↦ Etale.mem_agreementLocus_trans (Etale.mem_agreementLocus_trans ha h) hb'⟩

end Agreement

section Germs

variable {Λ : Type (u + 1)} [CommRing Λ] {X S : Scheme.{u}} {p : X ⟶ S}

variable (p) in
/-- The morphism `W ⟶ V` induced by a morphism `φ : W ⟶ V ×_S X` of étale `X`-schemes. -/
noncomputable abbrev Etale.chartProj {V : S.Etale} {W : X.Etale}
    (φ : W ⟶ (MorphismProperty.Over.pullback @Etale ⊤ p).obj V) : W.left ⟶ V.left :=
  φ.left ≫ pullback.fst V.hom p

lemma Etale.chartProj_comp_hom {V : S.Etale} {W : X.Etale}
    (φ : W ⟶ (MorphismProperty.Over.pullback @Etale ⊤ p).obj V) :
    Etale.chartProj p φ ≫ V.hom = W.hom ≫ p := by
  have hφ : φ.left ≫ pullback.snd V.hom p = W.hom := MorphismProperty.Over.w φ
  rw [Category.assoc, pullback.condition, reassoc_of% hφ]

/-- **Germs of `Etale.upperStarSectionsMap`.** The germ of the image of a section `t ∈ G(V)`
at a geometric point `x` of `W` is, under `AlgebraicGeometry.Etale.upperStarCompSheafFiberIso`,
the germ of `t` at the geometric point `x ≫ q` of `V`. -/
@[reassoc]
lemma Etale.upperStarSectionsMap_toPresheafFiber
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {V : S.Etale} {W : X.Etale}
    (φ : W ⟶ (MorphismProperty.Over.pullback @Etale ⊤ p).obj V)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] {s : Spec (.of Ω) ⟶ X}
    (x : Spec (.of Ω) ⟶ W.left) (hx : x ≫ W.hom = s)
    (hv : (x ≫ Etale.chartProj p φ) ≫ V.hom = s ≫ p) :
    Etale.upperStarSectionsMap _ p G φ ≫
        (pointSmallEtale s).toPresheafFiber W (Over.homMk x hx) ((p)^*[_].obj G).obj =
      (pointSmallEtale (s ≫ p)).toPresheafFiber V (Over.homMk (x ≫ Etale.chartProj p φ) hv)
          G.obj ≫ (Etale.upperStarCompSheafFiberIso _ p s).inv.app G := by
  rw [Etale.toPresheafFiber_upperStarCompSheafFiberIso_inv_app, Etale.upperStarSectionsMap,
    Category.assoc, GrothendieckTopology.Point.toPresheafFiber_w]
  congr 2
  apply CategoryTheory.Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [pointSmallEtaleFiberEtaleIso_inv_app_left_fst]
    rfl
  · simp only [pointSmallEtaleFiberEtaleIso_inv_app_left_snd]
    have hφ : φ.left ≫ pullback.snd V.hom p = W.hom := MorphismProperty.Over.w φ
    change (x ≫ φ.left) ≫ pullback.snd V.hom p = s
    rw [Category.assoc, hφ]
    exact hx

/-- The images of two sections of `G` over `V` agree at a point `z` of `W` iff the sections
agree at its image in `V`. -/
lemma Etale.mem_agreementLocus_upperStarSectionsMap_iff
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {V : S.Etale} {W : X.Etale}
    (φ : W ⟶ (MorphismProperty.Over.pullback @Etale ⊤ p).obj V) (t₁ t₂ : G.obj.obj (op V))
    (z : W.left) :
    z ∈ Etale.agreementLocus ((p)^*[_].obj G) (Etale.upperStarSectionsMap _ p G φ t₁)
        (Etale.upperStarSectionsMap _ p G φ t₂) ↔
      Etale.chartProj p φ z ∈ Etale.agreementLocus G t₁ t₂ := by
  obtain ⟨Ω, _, _, x, rfl⟩ := Scheme.exists_geometricPoint W.left z
  have hv : (x ≫ Etale.chartProj p φ) ≫ V.hom = (x ≫ W.hom) ≫ p := by
    rw [Category.assoc, Etale.chartProj_comp_hom, Category.assoc]
  rw [Etale.mem_agreementLocus_iff_toPresheafFiber_eq _ _ x rfl,
    ← Scheme.Hom.comp_apply, Etale.mem_agreementLocus_iff_toPresheafFiber_eq _ _ _ hv]
  have key (t : G.obj.obj (op V)) := congrArg (fun f ↦ f t)
    (Etale.upperStarSectionsMap_toPresheafFiber G φ x rfl hv)
  simp only [ConcreteCategory.comp_apply] at key
  rw [key, key]
  exact ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).1.eq_iff

/-- If `q : W ⟶ V` is surjective, `Etale.upperStarSectionsMap` is injective. -/
lemma Etale.upperStarSectionsMap_injective
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {V : S.Etale} {W : X.Etale}
    (φ : W ⟶ (MorphismProperty.Over.pullback @Etale ⊤ p).obj V)
    (hq : Function.Surjective (Etale.chartProj p φ)) :
    Function.Injective (Etale.upperStarSectionsMap _ p G φ) := by
  intro t₁ t₂ h
  refine Etale.eq_of_agreementLocus_eq_univ (Set.eq_univ_iff_forall.2 fun v ↦ ?_)
  obtain ⟨z, rfl⟩ := hq v
  rw [← Etale.mem_agreementLocus_upperStarSectionsMap_iff, h, Etale.agreementLocus_self]
  trivial

end Germs
section Chart

variable {X S : Scheme.{u}} {p : X ⟶ S} {V V' : S.Etale} {W : X.Etale}
  (φ : W ⟶ (MorphismProperty.Over.pullback @Etale ⊤ p).obj V) (f : V' ⟶ V)

/-- The base change `W ×_V V'` of `W` along an étale `f : V' ⟶ V`, as an étale `X`-scheme. -/
noncomputable def Etale.chart : X.Etale :=
  haveI := Etale.etale_left f
  haveI : AlgebraicGeometry.Etale W.hom := W.prop
  Scheme.Etale.mk (pullback.fst (Etale.chartProj p φ) f.left ≫ W.hom)

/-- The projection `W ×_V V' ⟶ W`. -/
noncomputable def Etale.chartι : Etale.chart φ f ⟶ W :=
  MorphismProperty.Over.homMk (pullback.fst (Etale.chartProj p φ) f.left) rfl

lemma Etale.chart_hom :
    (Etale.chart φ f).hom = pullback.fst (Etale.chartProj p φ) f.left ≫ W.hom := rfl

lemma Etale.chartι_left :
    (Etale.chartι φ f).left = pullback.fst (Etale.chartProj p φ) f.left := rfl

/-- The morphism `W ×_V V' ⟶ V' ×_S X` of étale `X`-schemes. -/
noncomputable def Etale.chartφ :
    Etale.chart φ f ⟶ (MorphismProperty.Over.pullback @Etale ⊤ p).obj V' :=
  MorphismProperty.Over.homMk
    (pullback.lift (pullback.snd (Etale.chartProj p φ) f.left)
      (pullback.fst (Etale.chartProj p φ) f.left ≫ W.hom) (by
        have hf : f.left ≫ V.hom = V'.hom := MorphismProperty.Over.w f
        rw [← hf, ← Category.assoc, ← pullback.condition, Category.assoc,
          Etale.chartProj_comp_hom, Category.assoc]))
    (pullback.lift_snd _ _ _)

@[simp]
lemma Etale.chartProj_chartφ :
    Etale.chartProj p (Etale.chartφ φ f) = pullback.snd (Etale.chartProj p φ) f.left := by
  simp [Etale.chartProj, Etale.chartφ]

lemma Etale.chartφ_comp :
    Etale.chartφ φ f ≫ (MorphismProperty.Over.pullback @Etale ⊤ p).map f =
      Etale.chartι φ f ≫ φ := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  all_goals rw [MorphismProperty.Comma.comp_left_assoc, MorphismProperty.Comma.comp_left_assoc,
    MorphismProperty.Over.pullback_map_left]
  · simp only [Etale.chartφ, Etale.chartι, MorphismProperty.Over.homMk_hom, Over.homMk_left,
      limit.lift_π, PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_left]
    exact pullback.condition.symm
  · simp only [Etale.chartφ, Etale.chartι, MorphismProperty.Over.homMk_hom, Over.homMk_left,
      limit.lift_π, PullbackCone.mk_π_app]
    have hφ : φ.left ≫ pullback.snd V.hom p = W.hom := MorphismProperty.Over.w φ
    rw [hφ]

lemma Etale.isPullback_chart :
    IsPullback (Etale.chartι φ f).left (Etale.chartProj p (Etale.chartφ φ f))
      (Etale.chartProj p φ) f.left := by
  rw [Etale.chartProj_chartφ, Etale.chartι_left]
  exact IsPullback.of_hasPullback _ _


lemma Etale.chartProj_comp_map {W' : X.Etale}
    (α : W' ⟶ (MorphismProperty.Over.pullback @Etale ⊤ p).obj V') :
    Etale.chartProj p (α ≫ (MorphismProperty.Over.pullback @Etale ⊤ p).map f) =
      Etale.chartProj p α ≫ f.left := by
  change (α ≫ _).left ≫ _ = _
  rw [MorphismProperty.Comma.comp_left_assoc, MorphismProperty.Over.pullback_map_left,
    pullback.lift_fst, Category.assoc]

lemma Etale.chartProj_comp {W' : X.Etale} (θ : W' ⟶ W) :
    Etale.chartProj p (θ ≫ φ) = θ.left ≫ Etale.chartProj p φ := by
  change (θ ≫ φ).left ≫ _ = _
  rw [MorphismProperty.Comma.comp_left_assoc]

/-- The morphism `W ×_V V'' ⟶ W ×_V V'` induced by `g : V'' ⟶ V'` over `V`. -/
noncomputable def Etale.chartMap {V'' : S.Etale} (g : V'' ⟶ V') (h : V'' ⟶ V)
    (hgf : g ≫ f = h) : Etale.chart φ h ⟶ Etale.chart φ f :=
  MorphismProperty.Over.homMk
    (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ g.left) (by
      rw [pullback.condition, Category.assoc, ← hgf]
      rfl))
    (by simp [Etale.chart_hom])

@[reassoc (attr := simp)]
lemma Etale.chartMap_chartι {V'' : S.Etale} (g : V'' ⟶ V') (h : V'' ⟶ V)
    (hgf : g ≫ f = h) :
    Etale.chartMap φ f g h hgf ≫ Etale.chartι φ f = Etale.chartι φ h := by
  apply MorphismProperty.Over.Hom.ext
  rw [MorphismProperty.Comma.comp_left]
  simp [Etale.chartMap, Etale.chartι]

lemma Etale.chartφ_chartMap {V'' : S.Etale} (g : V'' ⟶ V') (h : V'' ⟶ V)
    (hgf : g ≫ f = h) :
    Etale.chartφ φ h ≫ (MorphismProperty.Over.pullback @Etale ⊤ p).map g =
      Etale.chartMap φ f g h hgf ≫ Etale.chartφ φ f := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  all_goals rw [MorphismProperty.Comma.comp_left_assoc, MorphismProperty.Comma.comp_left_assoc,
    MorphismProperty.Over.pullback_map_left]
  · simp [Etale.chartφ, Etale.chartMap]
  · simp [Etale.chartφ, Etale.chartMap]

end Chart

section Local

variable {Λ : Type (u + 1)} [CommRing Λ] {X S : Scheme.{u}} {p : X ⟶ S}

/-- **Local sections of `p^* G` come from `G`.** Every section `σ` of `p^* G` over `W` agrees
near any point `z` of `W`, after base change along some étale `f : V' ⟶ V`, with the image of
a section of `G` over `V'`. -/
lemma Etale.exists_mem_agreementLocus_chart
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {V : S.Etale} {W : X.Etale}
    (φ : W ⟶ (MorphismProperty.Over.pullback @Etale ⊤ p).obj V)
    (σ : ((p)^*[_].obj G).obj.obj (op W)) (z : W.left) :
    ∃ (V' : S.Etale) (f : V' ⟶ V) (c : G.obj.obj (op V')) (z' : (Etale.chart φ f).left),
      (Etale.chartι φ f).left z' = z ∧
      z' ∈ Etale.agreementLocus ((p)^*[_].obj G) (((p)^*[_].obj G).obj.map (Etale.chartι φ f).op σ)
        (Etale.upperStarSectionsMap _ p G (Etale.chartφ φ f) c) := by
  obtain ⟨Ω, _, _, x, rfl⟩ := Scheme.exists_geometricPoint W.left z
  obtain ⟨s, hs⟩ : ∃ s, x ≫ W.hom = s := ⟨_, rfl⟩
  have hv : (x ≫ Etale.chartProj p φ) ≫ V.hom = s ≫ p := by
    rw [Category.assoc, Etale.chartProj_comp_hom, ← Category.assoc, hs]
  let e := (Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) p s).app G
  let germσ := (pointSmallEtale s).toPresheafFiber W (Over.homMk x hs)
    ((p)^*[_].obj G).obj σ
  obtain ⟨V₀, v₀, c₀, hc₀⟩ :=
    (pointSmallEtale (s ≫ p)).toPresheafFiber_jointly_surjective (P := G.obj) (e.hom germσ)
  -- a common refinement of the pointed étale neighbourhoods `(V₀, v₀)` and `(V, x ≫ q)`
  have : IsCofiltered (pointSmallEtale (s ≫ p)).fiber.Elements :=
    inferInstanceAs (IsCofiltered
      (Scheme.Etale.forget S ⋙ coyoneda.obj (op (Over.mk (s ≫ p)))).Elements)
  let a₀ : (pointSmallEtale (s ≫ p)).fiber.Elements := ⟨V₀, v₀⟩
  let a₁ : (pointSmallEtale (s ≫ p)).fiber.Elements :=
    ⟨V, Over.homMk (x ≫ Etale.chartProj p φ) hv⟩
  let m := IsCofiltered.min a₀ a₁
  let g : m.1 ⟶ V₀ := (IsCofiltered.minToLeft a₀ a₁).1
  let f : m.1 ⟶ V := (IsCofiltered.minToRight a₀ a₁).1
  have hg : (pointSmallEtale (s ≫ p)).fiber.map g m.2 = v₀ := (IsCofiltered.minToLeft a₀ a₁).2
  have hf : m.2.left ≫ f.left = x ≫ Etale.chartProj p φ :=
    congrArg CategoryTheory.CommaMorphism.left (IsCofiltered.minToRight a₀ a₁).2
  let x' : Spec (.of Ω) ⟶ (Etale.chart φ f).left := pullback.lift x m.2.left hf.symm
  have hx' : x' ≫ (Etale.chart φ f).hom = s := by
    rw [Etale.chart_hom, pullback.lift_fst_assoc, hs]
  refine ⟨m.1, f, G.obj.map g.op c₀, x' default, ?_, ?_⟩
  · rw [Etale.chartι_left, ← Scheme.Hom.comp_apply, pullback.lift_fst]
  rw [Etale.mem_agreementLocus_iff_toPresheafFiber_eq _ _ x' hx']
  have hv' : (x' ≫ Etale.chartProj p (Etale.chartφ φ f)) ≫ m.1.hom = s ≫ p := by
    rw [Etale.chartProj_chartφ, pullback.lift_snd]
    exact CategoryTheory.Over.w m.2
  have h₁ := congrArg (fun h ↦ h (G.obj.map g.op c₀))
    (Etale.upperStarSectionsMap_toPresheafFiber G (Etale.chartφ φ f) x' hx' hv')
  simp only [ConcreteCategory.comp_apply] at h₁
  rw [h₁, ← ConcreteCategory.comp_apply, GrothendieckTopology.Point.toPresheafFiber_w]
  have h₂ : (pointSmallEtale s).fiber.map (Etale.chartι φ f) (Over.homMk x' hx') =
      Over.homMk x hs := by
    apply CategoryTheory.Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _
  have h₃ : (pointSmallEtale (s ≫ p)).fiber.map g
      (Over.homMk (x' ≫ Etale.chartProj p (Etale.chartφ φ f)) hv') = v₀ := by
    rw [← hg]
    congr 1
    apply CategoryTheory.Over.OverMorphism.ext
    change x' ≫ Etale.chartProj p (Etale.chartφ φ f) = m.2.left
    rw [Etale.chartProj_chartφ, pullback.lift_snd]
  have h₄ : (pointSmallEtale (s ≫ p)).toPresheafFiber m.1
      (Over.homMk (x' ≫ Etale.chartProj p (Etale.chartφ φ f)) hv') G.obj (G.obj.map g.op c₀) =
        e.hom germσ := by
    rw [← ConcreteCategory.comp_apply, GrothendieckTopology.Point.toPresheafFiber_w, h₃, hc₀]
  rw [h₂, h₄]
  change germσ = (e.hom ≫ e.inv) germσ
  rw [e.hom_inv_id]
  rfl
lemma Etale.chartProj_chartφ_comp {V V' : S.Etale} {W : X.Etale}
    (φ : W ⟶ (MorphismProperty.Over.pullback @Etale ⊤ p).obj V) (f : V' ⟶ V)
    (z : (Etale.chart φ f).left) :
    f.left (Etale.chartProj p (Etale.chartφ φ f) z) =
      Etale.chartProj p φ ((Etale.chartι φ f).left z) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, (Etale.isPullback_chart φ f).w]

/-- **Local constancy of agreement along the fibres.** For sections `a, b` of `p^* G` over `W`
and a point `z` of `W`, there is an open neighbourhood `O` of `z` such that a point of `O` in
the fibre of `q` through `z` lies in the agreement locus of `a` and `b` iff `z` does. -/
lemma Etale.exists_isOpen_mem_agreementLocus_iff
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {V : S.Etale} {W : X.Etale}
    (φ : W ⟶ (MorphismProperty.Over.pullback @Etale ⊤ p).obj V)
    (a b : ((p)^*[_].obj G).obj.obj (op W)) (z : W.left) :
    ∃ O : Set W.left, IsOpen O ∧ z ∈ O ∧ ∀ z' ∈ O,
      Etale.chartProj p φ z' = Etale.chartProj p φ z →
        (z' ∈ Etale.agreementLocus ((p)^*[_].obj G) a b ↔
          z ∈ Etale.agreementLocus ((p)^*[_].obj G) a b) := by
  let H := ((p)^*[ModuleCat.{u + 1} Λ].obj G)
  obtain ⟨V₁, f₁, c, z₁, hz₁, hc⟩ := Etale.exists_mem_agreementLocus_chart G φ a z
  let ψ₁ := Etale.chartι φ f₁
  let φ₁ := Etale.chartφ φ f₁
  obtain ⟨V₂, f₂, d, z₂, hz₂, hd⟩ :=
    Etale.exists_mem_agreementLocus_chart G φ₁ (H.obj.map ψ₁.op b) z₁
  let ψ₂ := Etale.chartι φ₁ f₂
  let φ₂ := Etale.chartφ φ₁ f₂
  let Ψ := ψ₂ ≫ ψ₁
  let c₂ := G.obj.map f₂.op c
  let q₂ := Etale.chartProj p φ₂
  have hΨ (σ : H.obj.obj (op W)) : H.obj.map Ψ.op σ = H.obj.map ψ₂.op (H.obj.map ψ₁.op σ) := by
    simp only [Ψ, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  have hc₂ : Etale.upperStarSectionsMap _ p G φ₂ c₂ =
      H.obj.map ψ₂.op (Etale.upperStarSectionsMap _ p G φ₁ c) := by
    have := congrArg (fun h ↦ h c)
      (Etale.upperStarSectionsMap_naturality G φ₁ φ₂ f₂ ψ₂ (Etale.chartφ_comp φ₁ f₂))
    simpa only [ConcreteCategory.comp_apply] using this
  have hq (o : (Etale.chart φ₁ f₂).left) :
      f₁.left (f₂.left (q₂ o)) = Etale.chartProj p φ (Ψ.left o) := by
    rw [Etale.chartProj_chartφ_comp, Etale.chartProj_chartφ_comp]
    rfl
  -- the key equivalence on `N₁ ∩ N₂`
  let N₁ := Etale.agreementLocus H (H.obj.map Ψ.op a) (Etale.upperStarSectionsMap _ p G φ₂ c₂)
  let N₂ := Etale.agreementLocus H (H.obj.map Ψ.op b) (Etale.upperStarSectionsMap _ p G φ₂ d)
  have key (o) (h₁ : o ∈ N₁) (h₂ : o ∈ N₂) :
      Ψ.left o ∈ Etale.agreementLocus H a b ↔ q₂ o ∈ Etale.agreementLocus G c₂ d := by
    rw [← Etale.mem_agreementLocus_map_iff, Etale.mem_agreementLocus_congr h₁ h₂,
      Etale.mem_agreementLocus_upperStarSectionsMap_iff]
  have hz₂₁ : z₂ ∈ N₁ := by
    change z₂ ∈ Etale.agreementLocus H _ _
    rw [hΨ, hc₂, Etale.mem_agreementLocus_map_iff, hz₂]
    exact hc
  have hz₂₂ : z₂ ∈ N₂ := by
    change z₂ ∈ Etale.agreementLocus H _ _
    rw [hΨ]
    exact hd
  have hΨz : Ψ.left z₂ = z := by
    change ψ₁.left (ψ₂.left z₂) = z
    rw [hz₂, hz₁]
  -- the fibre of `V₂ ⟶ V` through `q₂ z₂` is discrete
  let F := f₂ ≫ f₁
  have := Etale.etale_left F
  have hdisc := F.left.isDiscrete_preimage_singleton (Etale.chartProj p φ z)
  have hmem : q₂ z₂ ∈ F.left ⁻¹' {Etale.chartProj p φ z} := by
    change f₁.left (f₂.left (q₂ z₂)) = _
    rw [hq, hΨz]
  have := isDiscrete_iff_discreteTopology.1 hdisc
  obtain ⟨D, hD, hDeq⟩ := isOpen_induced_iff.1
    (isOpen_discrete ({⟨_, hmem⟩} : Set (F.left ⁻¹' {Etale.chartProj p φ z})))
  have := Etale.etale_left Ψ
  refine ⟨Ψ.left '' (N₁ ∩ N₂ ∩ q₂ ⁻¹' D),
    Ψ.left.isOpenMap _ (((Etale.isOpen_agreementLocus _ _).inter
      (Etale.isOpen_agreementLocus _ _)).inter (hD.preimage q₂.continuous)),
    ⟨z₂, ⟨⟨hz₂₁, hz₂₂⟩, ?_⟩, hΨz⟩, ?_⟩
  · have : (⟨q₂ z₂, hmem⟩ : F.left ⁻¹' {Etale.chartProj p φ z}) ∈
        (Subtype.val ⁻¹' D : Set _) := by rw [hDeq]; rfl
    exact this
  rintro _ ⟨o, ⟨⟨ho₁, ho₂⟩, hoD⟩, rfl⟩ hoq
  have homem : q₂ o ∈ F.left ⁻¹' {Etale.chartProj p φ z} := by
    change f₁.left (f₂.left (q₂ o)) = _
    rw [hq, hoq]
  have hoeq : q₂ o = q₂ z₂ := by
    have : (⟨q₂ o, homem⟩ : F.left ⁻¹' {Etale.chartProj p φ z}) ∈
        (Subtype.val ⁻¹' D : Set _) := hoD
    rw [hDeq] at this
    exact congrArg Subtype.val (Set.mem_singleton_iff.1 this)
  rw [key o ho₁ ho₂, hoeq, ← key z₂ hz₂₁ hz₂₂, hΨz]

/-- **Agreement is constant on connected fibres.** If the fibres of `q : W ⟶ V` are
preconnected, two sections of `p^* G` over `W` agreeing at a point of a fibre agree at every
point of this fibre. -/
lemma Etale.mem_agreementLocus_of_chartProj_eq
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {V : S.Etale} {W : X.Etale}
    (φ : W ⟶ (MorphismProperty.Over.pullback @Etale ⊤ p).obj V)
    (hq : ∀ y, _root_.IsPreconnected (Etale.chartProj p φ ⁻¹' {y}))
    (a b : ((p)^*[_].obj G).obj.obj (op W)) {z z' : W.left}
    (hzz' : Etale.chartProj p φ z' = Etale.chartProj p φ z)
    (hz : z ∈ Etale.agreementLocus ((p)^*[_].obj G) a b) :
    z' ∈ Etale.agreementLocus ((p)^*[_].obj G) a b := by
  let Fb := Etale.chartProj p φ ⁻¹' {Etale.chartProj p φ z}
  have : PreconnectedSpace Fb := isPreconnected_iff_preconnectedSpace.1 (hq _)
  let A : Set Fb := {x | x.1 ∈ Etale.agreementLocus ((p)^*[_].obj G) a b}
  have hA : IsClopen A := by
    refine ⟨⟨?_⟩, (Etale.isOpen_agreementLocus _ _).preimage continuous_subtype_val⟩
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨O, hO, hxO, hO'⟩ := Etale.exists_isOpen_mem_agreementLocus_iff G φ a b x.1
    refine ⟨Subtype.val ⁻¹' O, fun y hy hyA ↦ hx ?_, hO.preimage continuous_subtype_val, hxO⟩
    have h := hO' y.1 hy (y.2.trans x.2.symm)
    exact h.1 hyA
  rcases isClopen_iff.1 hA with h | h
  · exact absurd (h ▸ (show (⟨z, rfl⟩ : Fb) ∈ A from hz)) (Set.notMem_empty _)
  · exact (h.symm ▸ Set.mem_univ (⟨z', hzz'⟩ : Fb) : (⟨z', hzz'⟩ : Fb) ∈ A)
/-- **Local surjectivity.** If `q : W ⟶ V` is flat, quasi-compact with geometrically connected
fibres, every section `σ` of `p^* G` over `W` is, near every point `v` of `V`, after base change
along an étale `f : V' ⟶ V` whose image contains `v`, the image of a section of `G` over
`V'`. -/
lemma Etale.exists_chartι_map_eq_upperStarSectionsMap
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {V : S.Etale} {W : X.Etale}
    (φ : W ⟶ (MorphismProperty.Over.pullback @Etale ⊤ p).obj V)
    [Flat (Etale.chartProj p φ)] [QuasiCompact (Etale.chartProj p φ)]
    [GeometricallyConnected (Etale.chartProj p φ)]
    (σ : ((p)^*[_].obj G).obj.obj (op W)) (v : V.left) :
    ∃ (V' : S.Etale) (f : V' ⟶ V) (c : G.obj.obj (op V')), v ∈ Set.range f.left ∧
      ((p)^*[_].obj G).obj.map (Etale.chartι φ f).op σ =
        Etale.upperStarSectionsMap _ p G (Etale.chartφ φ f) c := by
  let H := ((p)^*[ModuleCat.{u + 1} Λ].obj G)
  obtain ⟨x, rfl⟩ := (Etale.chartProj p φ).surjective v
  obtain ⟨V₁, f₁, c, x₁, hx₁, hc⟩ := Etale.exists_mem_agreementLocus_chart G φ σ x
  let ψ₁ := Etale.chartι φ f₁
  let φ₁ := Etale.chartφ φ f₁
  let q₁ := Etale.chartProj p φ₁
  have hq₁ : q₁ = pullback.snd (Etale.chartProj p φ) f₁.left := Etale.chartProj_chartφ φ f₁
  have : Flat q₁ := by rw [hq₁]; infer_instance
  have : QuasiCompact q₁ := by rw [hq₁]; infer_instance
  have : GeometricallyConnected q₁ := by rw [hq₁]; infer_instance
  let U := Etale.agreementLocus H (H.obj.map ψ₁.op σ) (Etale.upperStarSectionsMap _ p G φ₁ c)
  have hsat {u u'} (h : q₁ u' = q₁ u) (hu : u ∈ U) : u' ∈ U :=
    Etale.mem_agreementLocus_of_chartProj_eq G φ₁
      (fun y ↦ (q₁.isConnected_preimage_singleton y).isPreconnected) _ _ h hu
  have hpre : q₁ ⁻¹' (q₁ '' U) = U := by
    refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
    rintro u' ⟨u, hu, hq⟩
    exact hsat hq.symm hu
  have hopen : IsOpen (q₁ '' U) := by
    rw [← (Flat.isQuotientMap_of_surjective q₁).isOpen_preimage, hpre]
    exact Etale.isOpen_agreementLocus _ _
  let O : V₁.left.Opens := ⟨q₁ '' U, hopen⟩
  let ι := Etale.ofOpensι V₁ O
  refine ⟨Etale.ofOpens V₁ O, ι ≫ f₁, G.obj.map ι.op c, ⟨⟨q₁ x₁, x₁, hc, rfl⟩, ?_⟩, ?_⟩
  · change f₁.left (q₁ x₁) = _
    rw [Etale.chartProj_chartφ_comp, hx₁]
  let θ := Etale.chartMap φ f₁ ι (ι ≫ f₁) rfl
  have h₁ : H.obj.map (Etale.chartι φ (ι ≫ f₁)).op σ = H.obj.map θ.op (H.obj.map ψ₁.op σ) := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Etale.chartMap_chartι]
  have h₂ : Etale.upperStarSectionsMap _ p G (Etale.chartφ φ (ι ≫ f₁)) (G.obj.map ι.op c) =
      H.obj.map θ.op (Etale.upperStarSectionsMap _ p G φ₁ c) := by
    have := congrArg (fun h ↦ h c) (Etale.upperStarSectionsMap_naturality G φ₁
      (Etale.chartφ φ (ι ≫ f₁)) ι θ (Etale.chartφ_chartMap φ f₁ ι (ι ≫ f₁) rfl))
    simpa only [ConcreteCategory.comp_apply] using this
  rw [h₁, h₂]
  refine Etale.eq_of_agreementLocus_eq_univ (Set.eq_univ_iff_forall.2 fun o ↦ ?_)
  rw [Etale.mem_agreementLocus_map_iff]
  have hθ : q₁ (θ.left o) = ι.left (Etale.chartProj p (Etale.chartφ φ (ι ≫ f₁)) o) := by
    have := congrArg (Etale.chartProj p) (Etale.chartφ_chartMap φ f₁ ι (ι ≫ f₁) rfl)
    rw [Etale.chartProj_comp_map, Etale.chartProj_comp] at this
    exact (congrArg (fun h ↦ h o) this).symm.trans (Scheme.Hom.comp_apply _ _ _) |>.symm.trans
      (Scheme.Hom.comp_apply _ _ _) |>.symm
  obtain ⟨u, hu, hqu⟩ : ι.left (Etale.chartProj p (Etale.chartφ φ (ι ≫ f₁)) o) ∈ q₁ '' U :=
    (Etale.chartProj p (Etale.chartφ φ (ι ≫ f₁)) o).2
  exact hsat (hθ.trans hqu.symm) hu

variable (Λ p) in
/-- **[Stacks 0A3H].** Let `φ : W ⟶ V ×_S X` be a morphism of étale `X`-schemes such that the
induced morphism `q : W ⟶ V` is flat, quasi-compact and has geometrically connected fibres.
Then for every sheaf `G` of `Λ`-modules on `S_ét` the map `G(V) ⟶ (p^* G)(W)` of
`AlgebraicGeometry.Etale.upperStarSectionsMap` is bijective.

Writing `j : W ⟶ X` and `r : V ⟶ S` for the structure morphisms, `j ≫ p = q ≫ r` and `r` is
étale, so `(p^* G)(W) = Γ(W, q^* (G|_V))`, and this is the statement that for a flat
quasi-compact `q` with geometrically connected fibres the global sections of an inverse image
agree with the global sections downstairs. This is Step 2 of the blueprint proof of
`sk-prop-deg0`.

Injectivity holds as `q` is surjective
(`AlgebraicGeometry.Etale.upperStarSectionsMap_injective`). For surjectivity, a section `σ` is
locally the image of sections `c_i` of `G` over an étale covering `V_i ⟶ V`
(`AlgebraicGeometry.Etale.exists_chartι_map_eq_upperStarSectionsMap`, which uses the
connectedness of the fibres), and the `c_i` glue by injectivity over `V_i ×_V V_j`. -/
@[stacks 0A3H]
theorem Etale.isIso_upperStarSectionsMap (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {V : S.Etale} {W : X.Etale} (φ : W ⟶ (MorphismProperty.Over.pullback @Etale ⊤ p).obj V)
    [Flat (φ.left ≫ pullback.fst V.hom p)]
    [QuasiCompact (φ.left ≫ pullback.fst V.hom p)]
    [GeometricallyConnected (φ.left ≫ pullback.fst V.hom p)] :
    IsIso (Etale.upperStarSectionsMap _ p G φ) := by
  let H := ((p)^*[ModuleCat.{u + 1} Λ].obj G)
  have hinj {V' : S.Etale} (h : V' ⟶ V) :
      Function.Injective (Etale.upperStarSectionsMap _ p G (Etale.chartφ φ h)) := by
    refine Etale.upperStarSectionsMap_injective G _ ?_
    rw [Etale.chartProj_chartφ]
    exact Scheme.Hom.surjective _
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨?_, fun σ ↦ ?_⟩
  · exact Etale.upperStarSectionsMap_injective G φ (Scheme.Hom.surjective _)
  choose V' f c hv hσ using Etale.exists_chartι_map_eq_upperStarSectionsMap G φ σ
  obtain ⟨s, hs⟩ := Etale.exists_eq_map_of_compatible f
    (Set.eq_univ_iff_forall.2 fun v ↦ Set.mem_iUnion.2 ⟨v, hv v⟩) c
    (fun i j Z g₁ g₂ hg ↦ by
      apply hinj (g₁ ≫ f i)
      have e₁ := congrArg (fun h ↦ h (c i)) (Etale.upperStarSectionsMap_naturality G
        (Etale.chartφ φ (f i)) (Etale.chartφ φ (g₁ ≫ f i)) g₁ _
        (Etale.chartφ_chartMap φ (f i) g₁ (g₁ ≫ f i) rfl))
      have e₂ := congrArg (fun h ↦ h (c j)) (Etale.upperStarSectionsMap_naturality G
        (Etale.chartφ φ (f j)) (Etale.chartφ φ (g₁ ≫ f i)) g₂ _
        (Etale.chartφ_chartMap φ (f j) g₂ (g₁ ≫ f i) hg.symm))
      simp only [ConcreteCategory.comp_apply] at e₁ e₂
      rw [e₁, e₂, ← hσ i, ← hσ j, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        ← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, Etale.chartMap_chartι,
        Etale.chartMap_chartι])
  refine ⟨s, Etale.eq_of_forall_map_eq (fun v ↦ Etale.chartι φ (f v))
    (Set.eq_univ_iff_forall.2 fun x ↦ Set.mem_iUnion.2 ⟨Etale.chartProj p φ x, ?_⟩) fun v ↦ ?_⟩
  · obtain ⟨v', hv'⟩ := hv (Etale.chartProj p φ x)
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x v' hv'.symm
    exact ⟨z, hz⟩
  · have := congrArg (fun h ↦ h s) (Etale.upperStarSectionsMap_naturality G φ
      (Etale.chartφ φ (f v)) (f v) (Etale.chartι φ (f v)) (Etale.chartφ_comp φ (f v)))
    simp only [ConcreteCategory.comp_apply] at this
    rw [← this, hs, hσ]

end Local

end AlgebraicGeometry
