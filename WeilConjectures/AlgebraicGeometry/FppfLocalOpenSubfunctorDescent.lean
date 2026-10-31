/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent

/-!
# Fppf-local descent of open subfunctors

Source: Stacks Project, Spaces, Tag 02WU, local representatives and representing property;
Descent, Tag 03N0; Topologies, Tag 022C
(blueprint: lem-trf-fppf-local-open-subfunctor-descent).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem image_local {C : Type*} [Category C] {J : GrothendieckTopology C}
    (F G : Sheaf J (Type u)) (α : G.obj ⟶ F.obj)
    (hα : ∀ E : C, Function.Injective (α.app (op E)))
    {E : C} (x : F.obj.obj (op E)) (R : Sieve E) (hR : R ∈ J E)
    (hx : ∀ (D : C) (f : D ⟶ E), R f →
      ∃ g, α.app (op D) g = F.obj.map f.op x) :
    ∃ g, α.app (op E) g = x := by
  classical
  choose g hg using hx
  let family : Presieve.FamilyOfElements G.obj R.arrows := g
  have compatible : family.Compatible := by
    intro D₁ D₂ D f₁ f₂ i₁ i₂ hi₁ hi₂ heq
    apply hα D
    rw [α.naturality_apply, α.naturality_apply, hg, hg]
    simp only [← Functor.map_comp_apply, ← op_comp, heq]
  have hG := (isSheaf_iff_isSheaf_of_type J G.obj).mp G.property
  have hF := (isSheaf_iff_isSheaf_of_type J F.obj).mp F.property
  obtain ⟨y, hy, _⟩ := hG R hR family compatible
  refine ⟨y, ?_⟩
  apply (hF R hR).isSeparatedFor.ext
  intro D f hf
  rw [← α.naturality_apply, hy f hf]
  exact hg D f hf

private theorem open_factor {S : Scheme.{u}} {T E : Over S} (V : T.left.Opens)
    (f : E ⟶ T) :
    Set.range f.left.base ⊆ V ↔
      ∃ v : E ⟶ Over.mk (V.ι ≫ T.hom), v ≫ Over.homMk V.ι = f := by
  constructor
  · intro h
    have hr : Set.range f.left.base ⊆ Set.range V.ι.base := by
      intro x hx
      obtain ⟨y, rfl⟩ := hx
      exact ⟨⟨f.left y, h ⟨y, rfl⟩⟩, rfl⟩
    refine ⟨Over.homMk (IsOpenImmersion.lift V.ι f.left hr) ?_, ?_⟩
    · change _ ≫ (V.ι ≫ T.hom) = E.hom
      rw [← Category.assoc, IsOpenImmersion.lift_fac, Over.w]
    · ext
      exact IsOpenImmersion.lift_fac _ _ _
  · rintro ⟨v, rfl⟩
    change Set.range (v.left ≫ V.ι).base ⊆ V
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    exact (v.left y).property

private theorem chart_criterion {S : Scheme.{u}} (U : Over S)
    (F G : Sheaf (Scheme.fppfTopology.over S) (Type u)) (α : G.obj ⟶ F.obj)
    (q : yoneda.obj U ⟶ F.obj) (W : U.left.Opens)
    (eW : yoneda.obj (Over.mk (W.ι ≫ U.hom)) ≅ pullback q α)
    (heW : eW.hom ≫ pullback.fst q α = yoneda.map (Over.homMk W.ι))
    (E : Over S) (b : E ⟶ U) :
    (∃ g, α.app (op E) g = q.app (op E) b) ↔ Set.range b.left.base ⊆ W := by
  rw [open_factor]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨p, hp, _⟩ := Types.exists_of_isPullback
      ((IsPullback.of_hasPullback q α).app (op E)) b g hg.symm
    refine ⟨eW.inv.app (op E) p, ?_⟩
    have hw := congrArg (fun k ↦ k.app (op E) (eW.inv.app (op E) p)) heW
    change (pullback.fst q α).app (op E)
      (eW.hom.app (op E) (eW.inv.app (op E) p)) =
      eW.inv.app (op E) p ≫ Over.homMk W.ι at hw
    have hinv := congrArg (fun k ↦ k.app (op E) p) eW.inv_hom_id
    change eW.hom.app (op E) (eW.inv.app (op E) p) = p at hinv
    rw [hinv] at hw
    exact hw.symm.trans hp
  · rintro ⟨v, hv⟩
    refine ⟨(pullback.snd q α).app (op E) (eW.hom.app (op E) v), ?_⟩
    have hp := congrArg (fun k ↦ k.app (op E) (eW.hom.app (op E) v))
      (pullback.condition (f := q) (g := α))
    have hw := congrArg (fun k ↦ k.app (op E) v) heW
    change q.app (op E) ((pullback.fst q α).app (op E) (eW.hom.app (op E) v)) =
      α.app (op E) ((pullback.snd q α).app (op E) (eW.hom.app (op E) v)) at hp
    change (pullback.fst q α).app (op E) (eW.hom.app (op E) v) =
      v ≫ Over.homMk W.ι at hw
    rw [hw, hv] at hp
    exact hp.symm

private theorem range_preimage {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (V : Z.Opens) : Set.range (f ≫ g).base ⊆ V ↔ Set.range f.base ⊆ g ⁻¹ᵁ V := by
  simp only [Set.range_subset_iff]
  rfl

private theorem opens_ext_tests {S : Scheme.{u}} (T : Over S) (V V' : T.left.Opens)
    (h : ∀ (E : Over S) (f : E ⟶ T),
      Set.range f.left.base ⊆ V ↔ Set.range f.left.base ⊆ V') : V = V' := by
  apply le_antisymm
  · intro x hx
    have he := (h (Over.mk (V.ι ≫ T.hom)) (Over.homMk V.ι)).mp
      (by rintro y ⟨z, rfl⟩; exact z.property)
    exact he ⟨⟨x, hx⟩, rfl⟩
  · intro x hx
    have he := (h (Over.mk (V'.ι ≫ T.hom)) (Over.homMk V'.ι)).mpr
      (by rintro y ⟨z, rfl⟩; exact z.property)
    exact he ⟨⟨x, hx⟩, rfl⟩

private theorem chart_preimage {S : Scheme.{u}} (U : Over S)
    (F G : Sheaf (Scheme.fppfTopology.over S) (Type u)) (α : G.obj ⟶ F.obj)
    (q : yoneda.obj U ⟶ F.obj) (W : U.left.Opens)
    (eW : yoneda.obj (Over.mk (W.ι ≫ U.hom)) ≅ pullback q α)
    (heW : eW.hom ≫ pullback.fst q α = yoneda.map (Over.homMk W.ι))
    (B : Over S) (b c : B ⟶ U) (h : yoneda.map b ≫ q = yoneda.map c ≫ q) :
    b.left ⁻¹ᵁ W = c.left ⁻¹ᵁ W := by
  apply opens_ext_tests B
  intro E f
  rw [← range_preimage, ← range_preimage]
  change Set.range (f ≫ b).left.base ⊆ W ↔ Set.range (f ≫ c).left.base ⊆ W
  rw [← chart_criterion U F G α q W eW heW E (f ≫ b),
    ← chart_criterion U F G α q W eW heW E (f ≫ c)]
  have he := congrArg (fun k ↦ k.app (op E) f) h
  change q.app (op E) (f ≫ b) = q.app (op E) (f ≫ c) at he
  rw [he]

private theorem cover_mem {S : Scheme.{u}} {T : Over S} {I : Type*}
    (Ti : I → Over S) (φ : ∀ i, Ti i ⟶ T)
    (hφ : Presieve.ofArrows (fun i ↦ (Ti i).left) (fun i ↦ (φ i).left) ∈
      Scheme.fppfPrecoverage T.left) :
    Sieve.ofArrows Ti φ ∈ (Scheme.fppfTopology.over S) T := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact Precoverage.generate_mem_toGrothendieck hφ

private theorem opens_unique_cover {T : Scheme.{u}} {I : Type*} (Ti : I → Scheme.{u})
    (φ : ∀ i, Ti i ⟶ T) (hφ : Presieve.ofArrows Ti φ ∈ Scheme.fppfPrecoverage T)
    (V V' : T.Opens) (h : ∀ i, φ i ⁻¹ᵁ V = φ i ⁻¹ᵁ V') : V = V' := by
  apply SetLike.ext
  intro x
  obtain ⟨D, f, hf, y, hy⟩ := Scheme.JointlySurjective.exists_eq
    (K := Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) (Presieve.ofArrows Ti φ) hφ x
  obtain ⟨i⟩ := hf
  rw [← hy]
  change y ∈ φ i ⁻¹ᵁ V ↔ y ∈ φ i ⁻¹ᵁ V'
  rw [h i]

private theorem representation_of_criterion {S : Scheme.{u}}
    (F G : Sheaf (Scheme.fppfTopology.over S) (Type u)) (α : G.obj ⟶ F.obj)
    (hα : ∀ E : Over S, Function.Injective (α.app (op E)))
    (T : Over S) (a : yoneda.obj T ⟶ F.obj) (V : T.left.Opens)
    (hV : ∀ (E : Over S) (f : E ⟶ T),
      (∃ g, α.app (op E) g = a.app (op E) f) ↔ Set.range f.left.base ⊆ V) :
    ∃ e : yoneda.obj (Over.mk (V.ι ≫ T.hom)) ≅ pullback a α,
      e.hom ≫ pullback.fst a α = yoneda.map (Over.homMk V.ι) := by
  let B : Over S := Over.mk (V.ι ≫ T.hom)
  let j : B ⟶ T := Over.homMk V.ι
  obtain ⟨g, hg⟩ := (hV B j).mpr (by rintro y ⟨z, rfl⟩; exact z.property)
  let r : yoneda.obj B ⟶ G.obj := yonedaEquiv.symm g
  have comm : yoneda.map j ≫ a = r ≫ α := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map,
      yonedaEquiv_comp, show r = yonedaEquiv.symm g from rfl, Equiv.apply_symm_apply]
    exact hg.symm
  have hp : IsPullback (yoneda.map j) r a α := by
    apply IsPullback.of_forall_isPullback_app
    intro E
    rw [Types.isPullback_iff]
    refine ⟨congr_app comm E, ?_, ?_⟩
    · intro v w hvw
      apply (cancel_mono j).mp
      exact hvw.1
    · intro f g' he
      obtain ⟨v, hv⟩ := (open_factor V f).mp ((hV E.unop f).mp ⟨g', he.symm⟩)
      refine ⟨v, hv, ?_⟩
      apply hα E.unop
      have hw := congrArg (fun k ↦ k.app E v) comm
      change a.app E (v ≫ j) = α.app E (r.app E v) at hw
      rw [hv] at hw
      exact hw.symm.trans he
  exact ⟨hp.isoPullback, hp.isoPullback_hom_fst⟩

private theorem overlap_compatible {S : Scheme.{u}} (U T : Over S)
    (F G : Sheaf (Scheme.fppfTopology.over S) (Type u)) (α : G.obj ⟶ F.obj)
    (q : yoneda.obj U ⟶ F.obj) (W : U.left.Opens)
    (eW : yoneda.obj (Over.mk (W.ι ≫ U.hom)) ≅ pullback q α)
    (heW : eW.hom ≫ pullback.fst q α = yoneda.map (Over.homMk W.ι))
    (a : yoneda.obj T ⟶ F.obj) {I : Type*} (Ti : I → Over S)
    (φ : ∀ i, Ti i ⟶ T) (ai : ∀ i, Ti i ⟶ U)
    (hai : ∀ i, yoneda.map (ai i) ≫ q = yoneda.map (φ i) ≫ a) :
    ∀ i j, pullback.fst (φ i).left (φ j).left ⁻¹ᵁ ((ai i).left ⁻¹ᵁ W) =
      pullback.snd (φ i).left (φ j).left ⁻¹ᵁ ((ai j).left ⁻¹ᵁ W) := by
  intro i j
  let B : Over S := Over.mk (pullback.fst (φ i).left (φ j).left ≫ (Ti i).hom)
  let pi : B ⟶ Ti i := Over.homMk (pullback.fst (φ i).left (φ j).left)
  let pj : B ⟶ Ti j := Over.homMk (pullback.snd (φ i).left (φ j).left) (by
    dsimp [B]
    rw [← Over.w (φ i), ← Over.w (φ j), ← Category.assoc, ← Category.assoc,
      pullback.condition])
  have hc : pi ≫ φ i = pj ≫ φ j := by
    ext
    exact pullback.condition
  have he : yoneda.map (pi ≫ ai i) ≫ q = yoneda.map (pj ≫ ai j) ≫ q := by
    rw [yoneda.map_comp, Category.assoc, hai, ← Category.assoc, ← yoneda.map_comp, hc,
      yoneda.map_comp, Category.assoc, ← hai, ← Category.assoc, ← yoneda.map_comp]
  have hh := chart_preimage U F G α q W eW heW B (pi ≫ ai i) (pj ≫ ai j) he
  change ((pullback.fst (φ i).left (φ j).left ≫ (ai i).left) ⁻¹ᵁ W) =
    ((pullback.snd (φ i).left (φ j).left ≫ (ai j).left) ⁻¹ᵁ W) at hh
  simpa only [Scheme.Hom.comp_preimage] using hh

private theorem criterion_of_descent {S : Scheme.{u}} (U T : Over S)
    (F G : Sheaf (Scheme.fppfTopology.over S) (Type u)) (α : G.obj ⟶ F.obj)
    (hα : ∀ E : Over S, Function.Injective (α.app (op E)))
    (q : yoneda.obj U ⟶ F.obj) (W : U.left.Opens)
    (eW : yoneda.obj (Over.mk (W.ι ≫ U.hom)) ≅ pullback q α)
    (heW : eW.hom ≫ pullback.fst q α = yoneda.map (Over.homMk W.ι))
    (a : yoneda.obj T ⟶ F.obj) {I : Type*} (Ti : I → Over S)
    (φ : ∀ i, Ti i ⟶ T)
    (hφ : Presieve.ofArrows (fun i ↦ (Ti i).left) (fun i ↦ (φ i).left) ∈
      Scheme.fppfPrecoverage T.left)
    (ai : ∀ i, Ti i ⟶ U)
    (hai : ∀ i, yoneda.map (ai i) ≫ q = yoneda.map (φ i) ≫ a)
    (V : T.left.Opens) (hV : ∀ i, (φ i).left ⁻¹ᵁ V = (ai i).left ⁻¹ᵁ W) :
    ∀ (E : Over S) (f : E ⟶ T),
      (∃ g, α.app (op E) g = a.app (op E) f) ↔ Set.range f.left.base ⊆ V := by
  intro E f
  let Ei (i : I) : Over S :=
    Over.mk (pullback.snd (φ i).left f.left ≫ E.hom)
  let p (i : I) : Ei i ⟶ E := Over.homMk (pullback.snd (φ i).left f.left)
  let r (i : I) : Ei i ⟶ Ti i := Over.homMk (pullback.fst (φ i).left f.left) (by
    dsimp [Ei]
    rw [← Over.w (φ i), ← Over.w f, ← Category.assoc, ← Category.assoc,
      pullback.condition])
  have hc (i : I) : r i ≫ φ i = p i ≫ f := by
    ext
    exact pullback.condition
  have hp : Presieve.ofArrows (fun i ↦ (Ei i).left) (fun i ↦ (p i).left) ∈
      Scheme.fppfPrecoverage E.left := by
    exact Precoverage.mem_coverings_of_isPullback _ hφ f.left _ _
      (fun i ↦ (IsPullback.of_hasPullback (φ i).left f.left).flip)
  have hlocal (i : I) :
      (∃ g, α.app (op (Ei i)) g = a.app (op (Ei i)) (p i ≫ f)) ↔
        Set.range ((p i ≫ f).left).base ⊆ V := by
    have he := congrArg (fun k ↦ k.app (op (Ei i)) (r i)) (hai i)
    change q.app (op (Ei i)) (r i ≫ ai i) =
      a.app (op (Ei i)) (r i ≫ φ i) at he
    rw [hc i] at he
    rw [← he, chart_criterion U F G α q W eW heW (Ei i) (r i ≫ ai i)]
    change Set.range ((r i).left ≫ (ai i).left).base ⊆ W ↔ _
    rw [range_preimage, ← hV i, ← range_preimage]
    change Set.range (r i ≫ φ i).left.base ⊆ V ↔ _
    rw [hc i]
  constructor
  · rintro ⟨g, hg⟩ x ⟨y, rfl⟩
    obtain ⟨D, k, hk, z, hz⟩ := Scheme.JointlySurjective.exists_eq
      (K := Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation))
      (Presieve.ofArrows (fun i ↦ (Ei i).left) (fun i ↦ (p i).left)) hp y
    obtain ⟨i⟩ := hk
    have hi := (hlocal i).mp ⟨G.obj.map (p i).op g, by
      rw [α.naturality_apply, hg]
      exact (a.naturality_apply (p i).op f).symm⟩
    rw [← hz]
    exact hi ⟨z, rfl⟩
  · intro hf
    apply image_local F G α hα (a.app (op E) f) (Sieve.ofArrows Ei p)
      (cover_mem Ei p hp)
    intro D k hk
    obtain ⟨i, l, hl⟩ := Sieve.ofArrows.exists hk
    have hsub : Set.range ((p i ≫ f).left).base ⊆ V := by
      intro x hx
      obtain ⟨y, hy⟩ := hx
      rw [← hy]
      exact hf ⟨(p i).left y, rfl⟩
    obtain ⟨g, hg⟩ := (hlocal i).mpr hsub
    refine ⟨G.obj.map l.op g, ?_⟩
    rw [α.naturality_apply, hg, ← a.naturality_apply]
    change a.app (op D) (l ≫ (p i ≫ f)) = F.obj.map k.op (a.app (op E) f)
    rw [← Category.assoc, ← hl]
    exact a.naturality_apply k.op f

private theorem exists_criterion {S : Scheme.{u}} (U : Over S)
    (F G : Sheaf (Scheme.fppfTopology.over S) (Type u)) (α : G.obj ⟶ F.obj)
    (hα : ∀ E : Over S, Function.Injective (α.app (op E)))
    (q : yoneda.obj U ⟶ F.obj)
    (hq : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) q)
    (W : U.left.Opens)
    (eW : yoneda.obj (Over.mk (W.ι ≫ U.hom)) ≅ pullback q α)
    (heW : eW.hom ≫ pullback.fst q α = yoneda.map (Over.homMk W.ι))
    (T : Over S) (a : yoneda.obj T ⟶ F.obj) :
    ∃ V : T.left.Opens, ∀ (E : Over S) (f : E ⟶ T),
      (∃ g, α.app (op E) g = a.app (op E) f) ↔ Set.range f.left.base ⊆ V := by
  classical
  have : Scheme.fppfPrecoverage.HasIsos := ⟨fun {_ _} f _ ↦ by
    exact Scheme.Hom.singleton_mem_fppfPrecoverage f⟩
  have hs := hq.imageSieve_mem (yonedaEquiv a)
  have hs' := Eq.mp (congrArg
    (fun J : GrothendieckTopology (Over S) ↦ Presheaf.imageSieve q (yonedaEquiv a) ∈ J T)
    (over_toGrothendieck_eq_toGrothendieck_comap_forget Scheme.fppfPrecoverage S)) hs
  obtain ⟨R, hR, hle⟩ :=
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hs'
  obtain ⟨I, Ti, φ, rfl⟩ := R.exists_eq_ofArrows
  have hφ : Presieve.ofArrows (fun i ↦ (Ti i).left) (fun i ↦ (φ i).left) ∈
      Scheme.fppfPrecoverage T.left := by
    simpa only [Precoverage.mem_comap_iff, Presieve.map_ofArrows,
      Over.forget_obj, Over.forget_map] using hR
  have lifts (i : I) : ∃ b : Ti i ⟶ U,
      yoneda.map b ≫ q = yoneda.map (φ i) ≫ a := by
    obtain ⟨b, hb⟩ := hle _ _ (Presieve.ofArrows.mk i)
    refine ⟨b, yonedaEquiv.injective ?_⟩
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map, ← yonedaEquiv_naturality]
    exact hb
  choose ai hai using lifts
  obtain ⟨V, hV, _⟩ := openSubscheme_existsUnique_of_fpqc (fun i ↦ (φ i).left)
    (Scheme.fppfPrecoverage_le_fpqcPrecoverage _ hφ) (fun i ↦ (ai i).left ⁻¹ᵁ W)
    (overlap_compatible U T F G α q W eW heW a Ti φ ai hai)
  exact ⟨V, criterion_of_descent U T F G α hα q W eW heW a Ti φ hφ ai hai V hV⟩

/-- An open pullback along a locally surjective scheme presentation descends to an open
representation over every test scheme, independently of the cover and naturally in the test.
Here `a : yoneda.obj T ⟶ F.obj` is the section of `F(T)` given by Yoneda.

Source: Stacks Project, Spaces, Tag 02WU (lemma-finding-opens), generalized from quotient
sheaves to the assumed pullback square; Descent, Tag 03N0; Topologies, Tag 022C
(blueprint: lem-trf-fppf-local-open-subfunctor-descent).

Proof:
1. Evaluate the assumed isomorphism on a test scheme E. It identifies maps into W over
   a map b into U with sections g of G satisfying alpha(g) = q(b). Such g is unique by
   sectionwise injectivity. The fibre-product property and open factorization
   (lem-weil-pbc-open-immersion-base-change and
   lem-weil-pbc-morphism-factors-through-open-subscheme) give the same criterion for b⁻¹W.
2. On Ti ×_T Tj the two lifts have equal images in F. Apply step 1 to the inclusions of
   their inverse-image opens to obtain both inclusions, hence equality of the opens.
3. The fppf family is fpqc: after restricting to each affine open of T, apply
   lem-pc-fppf-affine-refinement. The finite affine opens obtained are opens in the
   original covering members and give the condition of def-weil-pbc-fpqc-covering.
4. Apply lem-weil-pbc-open-subscheme-fpqc-descent to obtain the unique descended open V.
   This includes the empty covering of the empty scheme.
5. For f : Z → T factoring through V, pull back the covering. Step 1 supplies sections
   of G on its members. Injectivity makes them agree on overlaps. The sheaf condition
   of def-weil-pbc-sites-and-cohomology glues them uniquely; separation in F verifies
   that the glued section maps to the restriction of a.
6. Conversely, a section g over Z mapping to f*a locally factors f through V by step 1.
   Joint surjectivity puts the entire image of f in V. Open factorization then gives
   its unique global factorization through V.
7. These constructions are mutually inverse on every test scheme. Uniqueness of g
   and of open factorization makes them natural, yielding the stated isomorphism over h_T.
8. Any other cover gives the same open by mutual factorization using steps 5 and 6.
   The isomorphism over h_T is unique since alpha is injective. Pull back any cover
   along b : Z → T: uniqueness of open descent identifies its open with b⁻¹V.
   On every test E the two comparisons give the same G(E) section, again by injectivity.
   Local surjectivity supplies a cover for every T,a, so alpha is representable by
   open immersions, without any algebraic-space assumption on F or G.
-/
theorem fppf_local_open_subfunctor_descent {S : Scheme.{u}} (U : Over S)
    (F G : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (α : G.obj ⟶ F.obj)
    (hα : ∀ T : Over S, Function.Injective (α.app (op T)))
    (q : yoneda.obj U ⟶ F.obj)
    (hq : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) q)
    (W : U.left.Opens)
    (eW : yoneda.obj (Over.mk (W.ι ≫ U.hom)) ≅ pullback q α)
    (heW : eW.hom ≫ pullback.fst q α = yoneda.map (Over.homMk W.ι)) :
    ∃ (V : ∀ (T : Over S), (yoneda.obj T ⟶ F.obj) → T.left.Opens)
      (e : ∀ (T : Over S) (a : yoneda.obj T ⟶ F.obj),
        yoneda.obj (Over.mk ((V T a).ι ≫ T.hom)) ≅ pullback a α),
      (∀ (T : Over S) (a : yoneda.obj T ⟶ F.obj),
        (e T a).hom ≫ pullback.fst a α = yoneda.map (Over.homMk (V T a).ι)) ∧
      (∀ (T : Over S) (a : yoneda.obj T ⟶ F.obj)
        (e' : yoneda.obj (Over.mk ((V T a).ι ≫ T.hom)) ≅ pullback a α),
        e'.hom ≫ pullback.fst a α = yoneda.map (Over.homMk (V T a).ι) →
        e' = e T a) ∧
      (∀ (T : Over S) (a : yoneda.obj T ⟶ F.obj)
        (I : Type v) (Ti : I → Over S) (φ : ∀ i, Ti i ⟶ T),
        Presieve.ofArrows (fun i ↦ (Ti i).left) (fun i ↦ (φ i).left) ∈
          Scheme.fppfPrecoverage T.left →
        ∀ ai : ∀ i, Ti i ⟶ U,
          (∀ i, yoneda.map (ai i) ≫ q = yoneda.map (φ i) ≫ a) →
          (∀ i j,
            pullback.fst (φ i).left (φ j).left ⁻¹ᵁ ((ai i).left ⁻¹ᵁ W) =
              pullback.snd (φ i).left (φ j).left ⁻¹ᵁ ((ai j).left ⁻¹ᵁ W)) ∧
          (∀ i, (φ i).left ⁻¹ᵁ V T a = (ai i).left ⁻¹ᵁ W) ∧
          (∀ O : T.left.Opens,
            (∀ i, (φ i).left ⁻¹ᵁ O = (ai i).left ⁻¹ᵁ W) → O = V T a)) ∧
      (∀ (Z T : Over S) (b : Z ⟶ T) (a : yoneda.obj T ⟶ F.obj),
        V Z (yoneda.map b ≫ a) = b.left ⁻¹ᵁ V T a) ∧
      (∀ (Z T : Over S) (b : Z ⟶ T) (a : yoneda.obj T ⟶ F.obj)
        (E : Over S)
        (vZ : E ⟶ Over.mk ((V Z (yoneda.map b ≫ a)).ι ≫ Z.hom))
        (vT : E ⟶ Over.mk ((V T a).ι ≫ T.hom)),
        vZ ≫ Over.homMk (V Z (yoneda.map b ≫ a)).ι ≫ b =
          vT ≫ Over.homMk (V T a).ι →
        (pullback.snd (yoneda.map b ≫ a) α).app (op E)
            ((e Z (yoneda.map b ≫ a)).hom.app (op E) vZ) =
          (pullback.snd a α).app (op E) ((e T a).hom.app (op E) vT)) := by
  classical
  choose V hV using exists_criterion U F G α hα q hq W eW heW
  choose e he using fun T a ↦ representation_of_criterion F G α hα T a (V T a) (hV T a)
  have hmono : Mono α := (NatTrans.mono_iff_mono_app α).mpr fun E ↦
    (CategoryTheory.mono_iff_injective (α.app E)).mpr (hα E.unop)
  refine ⟨V, e, he, ?_, ?_, ?_, ?_⟩
  · intro T a e' he'
    apply Iso.ext
    apply (cancel_mono (pullback.fst a α)).mp
    rw [he', he]
  · intro T a I Ti φ hφ ai hai
    have hi (i : I) : (φ i).left ⁻¹ᵁ V T a = (ai i).left ⁻¹ᵁ W := by
      apply opens_ext_tests (Ti i)
      intro E f
      rw [← range_preimage, ← range_preimage]
      change Set.range (f ≫ φ i).left.base ⊆ V T a ↔
        Set.range (f ≫ ai i).left.base ⊆ W
      rw [← hV T a E (f ≫ φ i),
        ← chart_criterion U F G α q W eW heW E (f ≫ ai i)]
      have hh := congrArg (fun k ↦ k.app (op E) f) (hai i)
      change q.app (op E) (f ≫ ai i) = a.app (op E) (f ≫ φ i) at hh
      rw [hh]
    refine ⟨overlap_compatible U T F G α q W eW heW a Ti φ ai hai, hi, ?_⟩
    intro O hO
    exact opens_unique_cover (fun i ↦ (Ti i).left) (fun i ↦ (φ i).left) hφ O (V T a)
      (fun i ↦ (hO i).trans (hi i).symm)
  · intro Z T b a
    apply opens_ext_tests Z
    intro E f
    rw [← range_preimage]
    change Set.range f.left.base ⊆ V Z (yoneda.map b ≫ a) ↔
      Set.range (f ≫ b).left.base ⊆ V T a
    rw [← hV Z (yoneda.map b ≫ a) E f, ← hV T a E (f ≫ b)]
    rfl
  · intro Z T b a E vZ vT hcomm
    apply hα E
    have hz := congrArg (fun k ↦ k.app (op E) ((e Z (yoneda.map b ≫ a)).hom.app
      (op E) vZ)) (pullback.condition (f := yoneda.map b ≫ a) (g := α))
    have ht := congrArg (fun k ↦ k.app (op E) ((e T a).hom.app (op E) vT))
      (pullback.condition (f := a) (g := α))
    have ez := congrArg (fun k ↦ k.app (op E) vZ) (he Z (yoneda.map b ≫ a))
    have et := congrArg (fun k ↦ k.app (op E) vT) (he T a)
    change (pullback.fst (yoneda.map b ≫ a) α).app (op E)
      ((e Z (yoneda.map b ≫ a)).hom.app (op E) vZ) =
      vZ ≫ Over.homMk (V Z (yoneda.map b ≫ a)).ι at ez
    change (pullback.fst a α).app (op E) ((e T a).hom.app (op E) vT) =
      vT ≫ Over.homMk (V T a).ι at et
    change a.app (op E) ((pullback.fst (yoneda.map b ≫ a) α).app (op E)
      ((e Z (yoneda.map b ≫ a)).hom.app (op E) vZ) ≫ b) = _ at hz
    change a.app (op E) ((pullback.fst a α).app (op E)
      ((e T a).hom.app (op E) vT)) = _ at ht
    rw [ez, Category.assoc, hcomm] at hz
    rw [et] at ht
    exact hz.symm.trans ht

end AlgebraicGeometry
