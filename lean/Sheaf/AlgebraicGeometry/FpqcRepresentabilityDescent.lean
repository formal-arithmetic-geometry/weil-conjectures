/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-! # Representability after effective fpqc descent

Source: Stacks Project, Tag 02W0.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- An fpqc sheaf represented over a faithfully flat quasi-compact base change is represented
 by a compatible effective descent of the representing scheme.

Proof: the identity of the representing scheme supplies a local universal section. Transport
 invariance and the cartesian square make this section compatible on overlaps, so the sheaf
 condition glues it. Yoneda gives a map from the descended represented functor to the sheaf.
 This map is bijective over the covering base, hence locally bijective. Since both functors
 are sheaves, it is an isomorphism.

Source: Stacks Project, Tag 02W0.
(blueprint: lem-pd-fpqc-representability-descent) -/
theorem nonempty_representableBy_of_effective_fpqc_descent
    {X Y : Scheme.{u}} (p : X ⟶ Y) [Flat p] [Surjective p] [QuasiCompact p]
    (F : (Over Y)ᵒᵖ ⥤ Type (u + 1))
    (hF : Presheaf.IsSheaf (Scheme.fpqcTopology.over Y) F)
    (V : Over X) (r : ((Over.map p).op ⋙ F).RepresentableBy V)
    (J : Over Y) (q : V.left ⟶ J.left) (hq : IsPullback q V.hom J.hom p)
    (hinv : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X)
      (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
      (r.overTransport f₁ f₂ h a).left ≫ q = a.left ≫ q) :
    Nonempty (F.RepresentableBy J) := by
  classical
  let VY := (Over.map p).obj V
  let qY : VY ⟶ J := Over.homMk q hq.w
  have hqflat : Flat q := MorphismProperty.of_isPullback (P := @Flat) hq.flip inferInstance
  have hqsurj : Surjective q :=
    MorphismProperty.of_isPullback (P := @Surjective) hq.flip inferInstance
  have hqqc : QuasiCompact q :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hq.flip inferInstance
  have hcover (T U : Over Y) (g : T ⟶ U) [Flat g.left] [Surjective g.left]
      [QuasiCompact g.left] : Sieve.generate (.singleton g) ∈ Scheme.fpqcTopology.over Y U := by
    rw [Scheme.fpqcTopology, over_toGrothendieck_eq_toGrothendieck_comap_forget]
    apply Precoverage.generate_mem_toGrothendieck
    simp [Precoverage.mem_comap_iff, Presieve.map_singleton]
  let s₀ : F.obj (op VY) := r.homEquiv (𝟙 V)
  have hs₀ : ∀ {Z : Over Y} (g₁ g₂ : Z ⟶ VY),
      g₁ ≫ qY = g₂ ≫ qY → F.map g₁.op s₀ = F.map g₂.op s₀ := by
    intro Z g₁ g₂ hg
    let f₁ := g₁.left ≫ V.hom
    let f₂ := g₂.left ≫ V.hom
    have hf : f₁ ≫ p = f₂ ≫ p := by
      simpa only [f₁, f₂, VY, Over.map_obj_hom, Over.mk_hom, Category.assoc] using
        (Over.w g₁).trans (Over.w g₂).symm
    let a₁ : Over.mk f₁ ⟶ V := Over.homMk g₁.left
    let a₂ : Over.mk f₂ ⟶ V := Over.homMk g₂.left
    have ha : r.overTransport f₁ f₂ hf a₁ = a₂ := by
      apply Over.OverMorphism.ext
      apply hq.hom_ext
      · rw [hinv]
        exact congrArg CommaMorphism.left hg
      · exact (Over.w _).trans (Over.w a₂).symm
    let e₁ : Z ⟶ (Over.map p).obj (Over.mk f₁) :=
      Over.homMk (𝟙 Z.left) (by
        simpa only [Category.id_comp, f₁, VY, Over.map_obj_hom, Over.mk_hom,
          Category.assoc] using (Over.w g₁))
    let e₂ : Z ⟶ (Over.map p).obj (Over.mk f₂) :=
      Over.homMk (𝟙 Z.left) (by
        simpa only [Category.id_comp, f₂, VY, Over.map_obj_hom, Over.mk_hom,
          Category.assoc] using (Over.w g₂))
    have he : e₂ ≫ Functor.RepresentableBy.overMapHomMkId f₁ f₂ hf = e₁ := by
      ext
      simp [e₁, e₂]
    have h₁ : e₁ ≫ (Over.map p).map a₁ = g₁ := by ext; simp [e₁, a₁]
    have h₂ : e₂ ≫ (Over.map p).map a₂ = g₂ := by ext; simp [e₂, a₂]
    rw [← h₁, ← h₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
    have hri {T : Over X} (a : T ⟶ V) :
        F.map ((Over.map p).map a).op s₀ = r.homEquiv a := by
      simpa [s₀] using (r.homEquiv_comp a (𝟙 V)).symm
    rw [hri, hri]
    rw [← ha, r.homEquiv_overTransport, ← Functor.map_comp_apply, ← op_comp, he]
    rfl
  have : Flat qY.left := hqflat
  have : Surjective qY.left := hqsurj
  have : QuasiCompact qY.left := hqqc
  obtain ⟨s, hs, hsuniq⟩ := (Presieve.isSheafFor_singleton.mp
    ((Presieve.isSheafFor_iff_generate _).mpr (hF.isSheafFor _ (hcover VY J qY)))) s₀ hs₀
  let φ : uliftYoneda.{u + 1}.obj J ⟶ F := uliftYonedaEquiv.symm s
  have hφ : ∀ {T : Over X} (a : T ⟶ V),
      φ.app (op ((Over.map p).obj T)) ⟨Over.homMk (a.left ≫ q) (by
        rw [Category.assoc, hq.w, ← Category.assoc, Over.w]
        rfl)⟩ = r.homEquiv a := by
    intro T a
    change F.map (Over.homMk (a.left ≫ q) (by
      rw [Category.assoc, hq.w, ← Category.assoc, Over.w]
      rfl) : (Over.map p).obj T ⟶ J).op s = r.homEquiv a
    have he : (Over.map p).map a ≫ qY = (Over.homMk (a.left ≫ q) (by
        rw [Category.assoc, hq.w, ← Category.assoc, Over.w]
        rfl) : (Over.map p).obj T ⟶ J) := by ext; rfl
    rw [← he, op_comp, Functor.map_comp_apply, hs]
    simpa using (r.homEquiv_comp a (𝟙 V)).symm
  have hbij (T : Over X) : Function.Bijective (φ.app (op ((Over.map p).obj T))) := by
    let e : (T ⟶ V) ≃ ((Over.map p).obj T ⟶ J) :=
      { toFun a := Over.homMk (a.left ≫ q) (by
          rw [Category.assoc, hq.w, ← Category.assoc, Over.w]
          rfl)
        invFun g := Over.homMk (hq.lift g.left T.hom (Over.w g)) (hq.lift_snd _ _ _)
        left_inv a := by
          apply Over.OverMorphism.ext
          apply hq.hom_ext
          · simp
          · simp
        right_inv g := by
          apply Over.OverMorphism.ext
          exact hq.lift_fst _ _ _ }
    have he : φ.app (op ((Over.map p).obj T)) =
        TypeCat.ofHom (Equiv.ulift.trans (e.symm.trans r.homEquiv)) := by
      ext x
      obtain ⟨g⟩ := x
      have h := hφ (e.symm g)
      change φ.app _ ⟨e (e.symm g)⟩ = r.homEquiv (e.symm g) at h
      change φ.app _ ⟨g⟩ = r.homEquiv (e.symm g)
      simpa only [Equiv.apply_symm_apply] using h
    rw [he]
    exact Equiv.bijective _
  let W (T : Over Y) : Over X := Over.mk (pullback.snd T.hom p)
  let g (T : Over Y) : (Over.map p).obj (W T) ⟶ T :=
    Over.homMk (pullback.fst T.hom p) pullback.condition
  have hgflat (T : Over Y) : Flat (g T).left := inferInstanceAs (Flat (pullback.fst T.hom p))
  have hgsurj (T : Over Y) : Surjective (g T).left :=
    inferInstanceAs (Surjective (pullback.fst T.hom p))
  have hgqc (T : Over Y) : QuasiCompact (g T).left :=
    inferInstanceAs (QuasiCompact (pullback.fst T.hom p))
  have hgc (T : Over Y) : Sieve.generate (.singleton (g T)) ∈ Scheme.fpqcTopology.over Y T :=
    hcover _ _ (g T)
  have hY : Presheaf.IsSheaf (Scheme.fpqcTopology.over Y) (uliftYoneda.{u + 1}.obj J) :=
    (isSheaf_iff_isSheaf_of_type _ _).mpr
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)
  let ψ : (⟨uliftYoneda.{u + 1}.obj J, hY⟩ : Sheaf (Scheme.fpqcTopology.over Y) (Type (u + 1))) ⟶
      ⟨F, hF⟩ := ⟨φ⟩
  have : Presheaf.IsLocallyInjective (Scheme.fpqcTopology.over Y) φ := by
    constructor
    intro T a b hab
    apply (Scheme.fpqcTopology.over Y).superset_covering _ (hgc T.unop)
    apply (Sieve.generate_le_iff _ _).mpr
    intro U f hf
    cases hf
    change (uliftYoneda.obj J).map (g T.unop).op a =
      (uliftYoneda.obj J).map (g T.unop).op b
    apply (hbij (W T.unop)).injective
    rw [NatTrans.naturality_apply φ, NatTrans.naturality_apply φ, hab]
  have : Presheaf.IsLocallySurjective (Scheme.fpqcTopology.over Y) φ := by
    constructor
    intro T a
    apply (Scheme.fpqcTopology.over Y).superset_covering _ (hgc T)
    apply (Sieve.generate_le_iff _ _).mpr
    intro U f hf
    cases hf
    exact (hbij (W T)).surjective (F.map (g T).op a)
  have : Sheaf.IsLocallyInjective ψ := inferInstance
  have : Sheaf.IsLocallySurjective ψ := inferInstance
  have : IsIso ψ := (Sheaf.isLocallyBijective_iff_isIso ψ).mp ⟨inferInstance, inferInstance⟩
  let e := (sheafToPresheaf _ _).mapIso (asIso ψ)
  exact ⟨(Functor.RepresentableBy.equivUliftYonedaIso F J).symm e⟩

end AlgebraicGeometry
