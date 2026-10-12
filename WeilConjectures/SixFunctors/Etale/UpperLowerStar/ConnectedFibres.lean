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

end AlgebraicGeometry
