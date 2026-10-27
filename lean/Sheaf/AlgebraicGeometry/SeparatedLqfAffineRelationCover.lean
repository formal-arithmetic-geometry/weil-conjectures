/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q157 and T2
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
import Mathlib.CategoryTheory.Functor.RegularEpi
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equalizer
import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineAtlasOpenCover
import Sheaf.AlgebraicGeometry.SpaceSeparatedLqfPermanence
import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Closed affine relation presentations on open pieces

Source: Stacks Project, Morphisms of Spaces, Tag 03XX, first three proof paragraphs;
Spaces, Tag 0262 (blueprint: lem-a1-separated-lqf-affine-relation-cover).

All objects are kept on the big fppf site of `S`, with their displayed maps to `h_Ti`
and, after base change, `h_B`. Sheaves over a representable `h_Ti` are equivalently
sheaves on the big fppf site of `Ti`. Colimits in the slice are created by the forgetful
functor. Thus the displayed sheafification universal properties, with the specified
atlas and structure maps, are precisely the relative fppf quotients.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

private theorem atlas_representable_space {S : Scheme.{u}} (T : Over S) :
    IsAlgebraicSpace ((Scheme.fppfTopology.over S).yoneda.obj T) := by
  constructor
  · intro V a
    let f : V ⟶ T := yoneda.preimage (a ≫ prod.fst)
    let g : V ⟶ T := yoneda.preimage (a ≫ prod.snd)
    let e := equalizer.ι f g
    have h := ((isPullback_equalizer_prod f g).flip).map yoneda
    refine ⟨equalizer f g, e, yoneda.map (e ≫ f), ?_, trivial⟩
    apply h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (asIso (prodComparison yoneda T T))
    · simp [e, Functor.map_comp]
    · simp [e]
    · apply prod.hom_ext <;> simp [prodComparison, ← Functor.map_comp]
    · apply prod.hom_ext <;> simp [prodComparison, ← Functor.map_comp, f, g]
  · refine ⟨T, 𝟙 _, ?_, ?_⟩
    · intro V a
      refine ⟨V, 𝟙 _, a, ?_, ?_⟩
      · simpa using (IsPullback.of_id_snd (f := a))
      · exact (inferInstance : Etale (𝟙 V.left))
    · intro V a
      refine ⟨V, 𝟙 _, a, ?_, ?_⟩
      · simpa using (IsPullback.of_id_snd (f := a))
      · exact (inferInstance : Surjective (𝟙 V.left))

private theorem atlas_representable_of_square {S : Scheme.{u}}
    (P : MorphismProperty (Over S)) {F G H K : (Over S)ᵒᵖ ⥤ Type u}
    {p : F ⟶ H} {g : G ⟶ H} {v : K ⟶ F} {pB : K ⟶ G}
    (hsq : IsPullback v pB p g) (hp : IsRepresentableWith P p) :
    IsRepresentableWith P pB := by
  intro V a
  obtain ⟨Z, z, l, hz, hP⟩ := hp V (a ≫ g)
  let k := hsq.lift l (yoneda.map z ≫ a) (by simpa [Category.assoc] using hz.w)
  refine ⟨Z, z, k, ?_, hP⟩
  apply IsPullback.of_right (t := hsq)
    (s := by simpa only [k, IsPullback.lift_fst] using hz)
  simp [k]

private theorem atlas_projection_property {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X : (Over S)ᵒᵖ ⥤ Type u} {U R : Over S}
    {p : yoneda.obj U ⟶ X} {s t : R ⟶ U}
    (hR : IsPullback (yoneda.map s) (yoneda.map t) p p)
    (hp : IsRepresentableWith (fun _ _ z ↦ P z.left) p) : P t.left := by
  obtain ⟨Z, z, l, hz, hP⟩ := hp U p
  let e : R ≅ Z := yoneda.preimageIso (hR.isoIsPullback _ _ hz)
  have he : e.hom ≫ z = t := by apply yoneda.map_injective; simp [e]
  rw [← he, Over.comp_left, P.cancel_left_of_respectsIso]
  exact hP

private theorem atlas_locallySurjective {S : Scheme.{u}}
    (X : AlgebraicSpace S) (U : Over S) (p : yoneda.obj U ⟶ X.obj.obj)
    (hp : IsEtale p) (hsur : IsSurjective p) :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) p := by
  constructor
  intro H x
  let a : yoneda.obj H ⟶ X.obj.obj := yonedaEquiv.symm x
  obtain ⟨V, v, l, hv, he⟩ := hp H a
  obtain ⟨W, w, k, hw, hs⟩ := hsur H a
  let e : V ≅ W := yoneda.preimageIso (hv.isoIsPullback _ _ hw)
  have ev : e.hom ≫ w = v := by
    apply yoneda.map_injective
    simp [e]
  have : Etale v.left := he
  have : Surjective w.left := hs
  have : Surjective v.left := by rw [← ev, Over.comp_left]; infer_instance
  have hcov : Sieve.generate (Presieve.singleton v) ∈
      (Scheme.fppfTopology.over S) H := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate]
    apply Scheme.fppfTopology.superset_covering ?_
      (Precoverage.generate_mem_toGrothendieck v.left.singleton_mem_fppfPrecoverage)
    apply (Sieve.generate_le_iff _ _).mpr
    intro Z z hz
    cases hz
    apply Sieve.le_generate
    exact Presieve.image_mem_functorPushforward _ _ Presieve.singleton.mk
  apply (Scheme.fppfTopology.over S).superset_covering _ hcov
  apply (Sieve.generate_le_iff _ _).mpr
  intro Z z hz
  cases hz
  refine ⟨l.app (op V) (𝟙 V), ?_⟩
  have hh := congrArg (fun m ↦ m.app (op V) (𝟙 V)) hv.w
  simpa [a, yonedaEquiv] using hh

private theorem atlas_quotient {S : Scheme.{u}}
    (X : AlgebraicSpace S) (U R : Over S) (p : yoneda.obj U ⟶ X.obj.obj)
    (s t : R ⟶ U) (hR : IsPullback (yoneda.map s) (yoneda.map t) p p)
    (hp : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) p) :
    ∃ η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ X.obj.obj,
      coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η = p ∧
      ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
        Function.Bijective (fun a : X.obj.obj ⟶ G.obj ↦ η ≫ a) := by
  let J := Scheme.fppfTopology.over S
  let Z := Subfunctor.range p
  let v := Subfunctor.toRange p
  let j := Z.ι
  have hvj : v ≫ j = p := rfl
  have hkv : IsKernelPair v (yoneda.map s) (yoneda.map t) :=
    IsKernelPair.cancel_right_of_mono (hvj ▸ hR)
  have : Epi v := (Subfunctor.epi_iff_range_eq_top v).mpr (Subfunctor.range_toRange p)
  have hc := hkv.toCoequalizer (regularEpiOfEpi v)
  have htop : Z.sheafify J = ⊤ :=
    (Presheaf.isLocallySurjective_iff_range_sheafify_eq_top' J p).mp hp
  let η := coequalizer.desc p hR.w
  refine ⟨η, coequalizer.π_desc _ _, fun G ↦ ⟨?_, ?_⟩⟩
  · intro a b hab
    have habp : p ≫ a = p ≫ b := by
      simpa [η] using congrArg
        (fun k ↦ coequalizer.π (yoneda.map s) (yoneda.map t) ≫ k) hab
    let pa : J.yoneda.obj U ⟶ X.obj := ⟨p⟩
    have : Sheaf.IsLocallySurjective pa := hp
    have hh : (pa ≫ (⟨a⟩ : X.obj ⟶ G)) = pa ≫ ⟨b⟩ := by
      exact Sheaf.hom_ext habp
    exact congrArg (fun k : X.obj ⟶ G ↦ k.hom) ((cancel_epi pa).mp hh)
  · intro a
    let d : Z.toFunctor ⟶ G.obj := hc.desc (Cofork.ofπ
      (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ a)
      (by simpa only [← Category.assoc] using (coequalizer.condition_assoc
        (yoneda.map s) (yoneda.map t) a)))
    let i : Z.toFunctor ⟶ (Z.sheafify J).toFunctor :=
      Subfunctor.homOfLe (Z.le_sheafify J)
    have : IsIso (Z.sheafify J).ι := (Subfunctor.eq_top_iff_isIso _).mp htop
    let e : (Z.sheafify J).toFunctor ≅ X.obj.obj := asIso (Z.sheafify J).ι
    let b := e.inv ≫ Z.sheafifyLift d
      ((isSheaf_iff_isSheaf_of_type J G.obj).mp G.property)
    refine ⟨b, ?_⟩
    apply coequalizer.hom_ext
    have hid : i ≫ e.hom = j := by simp [i, e, j]
    have hi : j ≫ e.inv = i := by rw [← hid]; simp
    change (coequalizer.π _ _ ≫ η) ≫ b = _
    rw [coequalizer.π_desc]
    change (v ≫ j) ≫ e.inv ≫ _ = _
    rw [Category.assoc v j, ← Category.assoc j e.inv, hi,
      Subfunctor.to_sheafifyLift]
    exact Cofork.IsColimit.π_desc hc

/-- An atlas has an effective scheme kernel relation; its sheaf quotient and its
kernel relation commute with arbitrary scheme base change.
Source: Stacks Project, Spaces, Tag 0262, clauses (1)--(3), and Tag 02X2
(blueprint: lem-a1-separated-lqf-affine-relation-cover).

Proof: represent the pullback of the atlas along itself. Each projection is a
surjective etale scheme map by the scheme-test definition. On any scheme test,
the pullback universal property identifies relation sections with pairs of atlas
sections with equal image. Equality gives an equivalence relation and uniqueness
gives injectivity. The atlas is locally surjective on the fppf site: its pullback
to a section is a surjective etale scheme cover and supplies a local lift. Sheaf
descent therefore makes its target the coequalizer of this kernel pair among
sheaves. Descend the atlas map to the presheaf coequalizer; maps from this
coequalizer into a sheaf are exactly maps from the target into that sheaf.
For a scheme B over T form UB=U times_T B, RB=R times_T B, and XB=X times_T B.
The projection formulas define the two maps RB to UB. Their universal properties
identify RB with the kernel pair of UB to XB: a section is a pair of U-lifts with
equal X-image and a common B-coordinate. Base change preserves representable
surjective etaleness, so the same descent argument gives the final quotient. -/
private theorem exists_atlas_relation_baseChange {S : Scheme.{u}}
    (T : Over S) (X : AlgebraicSpace S) (q : X.obj.obj ⟶ yoneda.obj T)
    (U : Over S) (uT : U ⟶ T) (p : yoneda.obj U ⟶ X.obj.obj)
    (hp : IsEtale p) (hsur : IsSurjective p) (hpq : p ≫ q = yoneda.map uT) :
    ∃ (R : Over S) (s t : R ⟶ U),
    IsPullback (yoneda.map s) (yoneda.map t) p p ∧
    Etale s.left ∧ Surjective s.left ∧ Etale t.left ∧ Surjective t.left ∧
    (∀ H : Over S,
      Function.Injective (fun r : H ⟶ R ↦ (r ≫ s, r ≫ t)) ∧
      Equivalence (fun a b : H ⟶ U ↦ ∃ r : H ⟶ R, r ≫ s = a ∧ r ≫ t = b) ∧
      ∀ a b : H ⟶ U,
        (∃ r : H ⟶ R, r ≫ s = a ∧ r ≫ t = b) ↔
          p.app (op H) a = p.app (op H) b) ∧
    (∃ η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ X.obj.obj,
      coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η = p ∧
      ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
        Function.Bijective (fun a : X.obj.obj ⟶ G.obj ↦ η ≫ a)) ∧
    ∀ (B : Over S) (b : B ⟶ T),
      ∃ (UB RB : Over S) (v : UB ⟶ U) (uB : UB ⟶ B)
        (w : RB ⟶ R) (rB : RB ⟶ B) (sB tB : RB ⟶ UB)
        (XB : AlgebraicSpace S) (g : XB.obj.obj ⟶ X.obj.obj)
        (d : XB.obj.obj ⟶ yoneda.obj B) (pB : yoneda.obj UB ⟶ XB.obj.obj),
        IsPullback v uB uT b ∧ IsPullback w rB (s ≫ uT) b ∧
        IsPullback g d q (yoneda.map b) ∧
        pB ≫ g = yoneda.map v ≫ p ∧ pB ≫ d = yoneda.map uB ∧
        sB ≫ v = w ≫ s ∧ tB ≫ v = w ≫ t ∧
        sB ≫ uB = rB ∧ tB ≫ uB = rB ∧
        IsEtale pB ∧ IsSurjective pB ∧
        IsPullback (yoneda.map sB) (yoneda.map tB) pB pB ∧
        ∃ ηB : coequalizer (yoneda.map sB) (yoneda.map tB) ⟶ XB.obj.obj,
          coequalizer.π (yoneda.map sB) (yoneda.map tB) ≫ ηB = pB ∧
          ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
            Function.Bijective (fun a : XB.obj.obj ⟶ G.obj ↦ ηB ≫ a) := by
  classical
  obtain ⟨R, t, l, hR', ht⟩ := hp U p
  let s := yoneda.preimage l
  have hR : IsPullback (yoneda.map s) (yoneda.map t) p p := by simpa [s] using hR'
  have hs : Etale s.left := atlas_projection_property _ hR.flip hp
  have hss : Surjective s.left := atlas_projection_property _ hR.flip hsur
  have hts : Surjective t.left := atlas_projection_property _ hR hsur
  obtain ⟨η, hη, hηbij⟩ := atlas_quotient X U R p s t hR
    (atlas_locallySurjective X U p hp hsur)
  refine ⟨R, s, t, hR, hs, hss, ht, hts, ?_, ⟨η, hη, hηbij⟩, ?_⟩
  · intro H
    have heq (a b : H ⟶ U) :
        (∃ r : H ⟶ R, r ≫ s = a ∧ r ≫ t = b) ↔
          p.app (op H) a = p.app (op H) b := by
      constructor
      · rintro ⟨r, rfl, rfl⟩
        exact congrArg (fun k ↦ k.app (op H) r) hR.w
      · intro hab
        have h : yoneda.map a ≫ p = yoneda.map b ≫ p := by
          apply yonedaEquiv.injective
          change p.app (op H) (𝟙 H ≫ a) = p.app (op H) (𝟙 H ≫ b)
          simpa only [Category.id_comp] using hab
        refine ⟨yoneda.preimage (hR.lift (yoneda.map a) (yoneda.map b) h), ?_, ?_⟩
        · apply yoneda.map_injective
          simp
        · apply yoneda.map_injective
          simp
    refine ⟨?_, ⟨(fun a ↦ (heq a a).mpr rfl),
      (fun {a b} h ↦ (heq b a).mpr ((heq a b).mp h).symm),
      (fun {a b c} h k ↦ (heq a c).mpr (((heq a b).mp h).trans ((heq b c).mp k)))⟩,
      heq⟩
    intro a b hab
    apply yoneda.map_injective
    apply hR.hom_ext
    · simpa only [← Functor.map_comp] using congrArg yoneda.map (congrArg Prod.fst hab)
    · simpa only [← Functor.map_comp] using congrArg yoneda.map (congrArg Prod.snd hab)
  · intro B b
    let f : X.obj ⟶ (Scheme.fppfTopology.over S).yoneda.obj T := ⟨q⟩
    let XBS := Limits.pullback f ((Scheme.fppfTopology.over S).yoneda.map b)
    have hXBS : IsAlgebraicSpace XBS :=
      (fibreProduct_isAlgebraicSpace X
        ⟨(Scheme.fppfTopology.over S).yoneda.obj B, atlas_representable_space B⟩
        ⟨(Scheme.fppfTopology.over S).yoneda.obj T, atlas_representable_space T⟩
        ⟨f⟩ ⟨(Scheme.fppfTopology.over S).yoneda.map b⟩).1
    let XB : AlgebraicSpace S := ⟨XBS, hXBS⟩
    let g : XB.obj.obj ⟶ X.obj.obj := (pullback.fst f
      ((Scheme.fppfTopology.over S).yoneda.map b)).hom
    let d : XB.obj.obj ⟶ yoneda.obj B := (pullback.snd f
      ((Scheme.fppfTopology.over S).yoneda.map b)).hom
    have hXB : IsPullback g d q (yoneda.map b) :=
      (IsPullback.of_hasPullback f ((Scheme.fppfTopology.over S).yoneda.map b)).map
        (sheafToPresheaf _ _)
    let UB := Limits.pullback uT b
    let v : UB ⟶ U := pullback.fst uT b
    let uB : UB ⟶ B := pullback.snd uT b
    have hUB : IsPullback v uB uT b := IsPullback.of_hasPullback uT b
    have hUBy := hUB.map yoneda
    let pB := hXB.lift (yoneda.map v ≫ p) (yoneda.map uB) (by
      simp only [Category.assoc, hpq, ← Functor.map_comp]
      exact congrArg yoneda.map hUB.w)
    have pBg : pB ≫ g = yoneda.map v ≫ p := hXB.lift_fst _ _ _
    have pBd : pB ≫ d = yoneda.map uB := hXB.lift_snd _ _ _
    have hpat : IsPullback (yoneda.map v) pB p g := by
      refine IsPullback.of_isLimit' ⟨pBg.symm⟩ ?_
      refine PullbackCone.IsLimit.mk _
        (fun z ↦ hUBy.lift z.fst (z.snd ≫ d) ?_)
        (fun z ↦ by simp) (fun z ↦ ?_) (fun z m hm hn ↦ ?_)
      · rw [← hpq, ← Category.assoc, z.condition, Category.assoc, hXB.w]
        simp only [Category.assoc]
      · apply hXB.hom_ext
        · rw [Category.assoc, pBg, ← Category.assoc, IsPullback.lift_fst]
          exact z.condition
        · rw [Category.assoc, pBd, IsPullback.lift_snd]
      · apply hUBy.hom_ext
        · simpa using hm
        · rw [IsPullback.lift_snd, ← pBd, ← Category.assoc, hn]
    have hpB : IsEtale pB := atlas_representable_of_square _ hpat hp
    have hsurB : IsSurjective pB := atlas_representable_of_square _ hpat hsur
    have hst : s ≫ uT = t ≫ uT := by
      apply yoneda.map_injective
      simpa only [Functor.map_comp, ← hpq, ← Category.assoc] using
        congrArg (fun k ↦ k ≫ q) hR.w
    let RB := Limits.pullback (s ≫ uT) b
    let w : RB ⟶ R := pullback.fst (s ≫ uT) b
    let rB : RB ⟶ B := pullback.snd (s ≫ uT) b
    have hRB : IsPullback w rB (s ≫ uT) b := IsPullback.of_hasPullback _ _
    have hRBy := hRB.map yoneda
    let sB : RB ⟶ UB := hUB.lift (w ≫ s) rB (by simpa [Category.assoc] using hRB.w)
    let tB : RB ⟶ UB := hUB.lift (w ≫ t) rB (by
      simpa [Category.assoc, ← hst] using hRB.w)
    have hsBv : sB ≫ v = w ≫ s := hUB.lift_fst _ _ _
    have htBv : tB ≫ v = w ≫ t := hUB.lift_fst _ _ _
    have hsBu : sB ≫ uB = rB := hUB.lift_snd _ _ _
    have htBu : tB ≫ uB = rB := hUB.lift_snd _ _ _
    have ys : yoneda.map sB ≫ yoneda.map v = yoneda.map w ≫ yoneda.map s := by
      rw [← Functor.map_comp, hsBv, Functor.map_comp]
    have yt : yoneda.map tB ≫ yoneda.map v = yoneda.map w ≫ yoneda.map t := by
      rw [← Functor.map_comp, htBv, Functor.map_comp]
    have ysu : yoneda.map sB ≫ yoneda.map uB = yoneda.map rB := by
      rw [← Functor.map_comp, hsBu]
    have ytu : yoneda.map tB ≫ yoneda.map uB = yoneda.map rB := by
      rw [← Functor.map_comp, htBu]
    have hker : IsPullback (yoneda.map sB) (yoneda.map tB) pB pB := by
      have hcomm : yoneda.map sB ≫ pB = yoneda.map tB ≫ pB := by
        apply hXB.hom_ext
        · calc
            (yoneda.map sB ≫ pB) ≫ g = (yoneda.map sB ≫ yoneda.map v) ≫ p := by
              rw [Category.assoc, pBg, Category.assoc]
            _ = (yoneda.map tB ≫ yoneda.map v) ≫ p := by
              rw [ys, yt, Category.assoc, Category.assoc, hR.w]
            _ = (yoneda.map tB ≫ pB) ≫ g := by
              symm
              rw [Category.assoc, pBg, Category.assoc]
        · simp only [Category.assoc, pBd, ← Functor.map_comp]
          rw [hsBu, htBu]
      refine IsPullback.of_isLimit' ⟨hcomm⟩ ?_
      refine PullbackCone.IsLimit.mk _ (fun z ↦ ?_) (fun z ↦ ?_)
        (fun z ↦ ?_) (fun z m hm hn ↦ ?_)
      · let r := hR.lift (z.fst ≫ yoneda.map v) (z.snd ≫ yoneda.map v) (by
          rw [Category.assoc, Category.assoc, ← pBg, ← Category.assoc,
            ← Category.assoc, z.condition])
        exact hRBy.lift r (z.fst ≫ yoneda.map uB) (by
          rw [Functor.map_comp, ← Category.assoc, IsPullback.lift_fst,
            Category.assoc, hUBy.w]
          simp only [Category.assoc])
      · apply hUBy.hom_ext
        · rw [Category.assoc, ys, ← Category.assoc, IsPullback.lift_fst,
            IsPullback.lift_fst]
        · rw [Category.assoc, ysu, IsPullback.lift_snd]
      · apply hUBy.hom_ext
        · rw [Category.assoc, yt, ← Category.assoc, IsPullback.lift_fst,
            IsPullback.lift_snd]
        · rw [Category.assoc, ytu, IsPullback.lift_snd]
          simpa only [Category.assoc, pBd] using congrArg (fun k ↦ k ≫ d) z.condition
      · apply hRBy.hom_ext
        · rw [IsPullback.lift_fst]
          apply hR.hom_ext
          · rw [IsPullback.lift_fst, Category.assoc, ← ys, ← Category.assoc, hm]
          · rw [IsPullback.lift_snd, Category.assoc, ← yt, ← Category.assoc, hn]
        · rw [IsPullback.lift_snd, ← ysu, ← Category.assoc, hm]
    obtain ⟨ηB, hηB, hηBbij⟩ := atlas_quotient XB UB RB pB sB tB hker
      (atlas_locallySurjective XB UB pB hpB hsurB)
    exact ⟨UB, RB, v, uB, w, rB, sB, tB, XB, g, d, pB,
      hUB, hRB, hXB, pBg, pBd, hsBv, htBv, hsBu, htBu, hpB, hsurB, hker,
      ηB, hηB, hηBbij⟩



private theorem open_comp {S : Scheme.{u}} {F G H : (Over S)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} {g : G ⟶ H}
    (hf : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) f)
    (hg : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) g) :
    IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) (f ≫ g) := by
  intro T a
  obtain ⟨U, p, q, hq, hp⟩ := hg T a
  obtain ⟨V, r, k, hk, hr⟩ := hf U q
  have : IsOpenImmersion p.left := hp
  have : IsOpenImmersion r.left := hr
  refine ⟨V, r ≫ p, k, ?_, (inferInstance : IsOpenImmersion (r.left ≫ p.left))⟩
  simpa only [Functor.map_comp] using hk.paste_vert hq

private theorem open_mono {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G}
    (hf : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) f) : Mono f := by
  rw [NatTrans.mono_iff_mono_app]
  intro T
  rw [mono_iff_injective]
  intro x y hxy
  let a : yoneda.obj T.unop ⟶ F := yonedaEquiv.symm x
  let b : yoneda.obj T.unop ⟶ F := yonedaEquiv.symm y
  have hab : a ≫ f = b ≫ f := by
    apply yonedaEquiv.injective
    simpa only [yonedaEquiv_comp, a, b, Equiv.apply_symm_apply] using hxy
  obtain ⟨U, p, q, hq, hp⟩ := hf T.unop (a ≫ f)
  have : IsOpenImmersion p.left := hp
  have : Mono p := (Over.forget S).mono_of_mono_map
    (inferInstance : Mono p.left)
  let l := hq.lift a (𝟙 _) (by simp)
  let m := hq.lift b (𝟙 _) (by simpa using hab.symm)
  have hlm : l = m := by
    apply (cancel_mono (yoneda.map p)).mp
    simp [l, m]
  have : a = b := by
    rw [← hq.lift_fst a (𝟙 _) (by simp), ← hq.lift_fst b (𝟙 _) (by simpa using hab.symm)]
    exact congrArg (fun k ↦ k ≫ q) hlm
  simpa only [a, b, Equiv.apply_symm_apply] using congrArg yonedaEquiv this

private theorem open_range {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G}
    (hf : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) f) :
    IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) (Subfunctor.range f).ι := by
  have := open_mono hf
  let e := asIso (Subfunctor.toRange f)
  intro T a
  obtain ⟨U, p, q, hq, hp⟩ := hf T a
  refine ⟨U, p, q ≫ e.hom, ?_, hp⟩
  exact hq.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp [e]) (by simp)

private theorem scheme_test_open {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G}
    (hf : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) f)
    (H : Over S) (a : yoneda.obj H ⟶ G) :
    ∃ (V : H.left.Opens)
      (k : yoneda.obj (Over.mk (V.ι ≫ H.hom)) ⟶ F),
      IsPullback k (yoneda.map (Over.homMk V.ι)) f a := by
  obtain ⟨U, p, q, hq, hp⟩ := hf H a
  have : IsOpenImmersion p.left := hp
  let V := p.left.opensRange
  let e : U.left ≅ V.toScheme := IsOpenImmersion.isoOfRangeEq p.left V.ι
    (by exact Subtype.range_val.symm)
  have he : e.hom ≫ V.ι = p.left := IsOpenImmersion.isoOfRangeEq_hom_fac ..
  let eo : U ≅ Over.mk (V.ι ≫ H.hom) := Over.isoMk e (by
    change e.hom ≫ (V.ι ≫ H.hom) = U.hom
    rw [← Category.assoc, he, Over.w p])
  have hep : eo.inv ≫ p = Over.homMk V.ι := by
    ext
    change e.inv ≫ p.left = V.ι
    rw [← he, Iso.inv_hom_id_assoc]
  refine ⟨V, yoneda.map eo.inv ≫ q, ?_⟩
  exact hq.of_iso' (yoneda.mapIso eo.symm) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by
      change yoneda.map eo.inv ≫ yoneda.map p = yoneda.map (Over.homMk V.ι) ≫ 𝟙 _
      rw [← Functor.map_comp, hep, Category.comp_id])
    (by simp) (by simp)

private theorem yoneda_open {S : Scheme.{u}} {U T : Over S} (b : U ⟶ T)
    (hb : IsOpenImmersion b.left) :
    IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) (yoneda.map b) := by
  intro V a
  let c := yoneda.preimage a
  let Z := Limits.pullback b c
  have hz : IsPullback (pullback.fst b c) (pullback.snd b c) b c :=
    IsPullback.of_hasPullback _ _
  have hz' := hz.map (Over.forget S)
  refine ⟨Z, pullback.snd b c, yoneda.map (pullback.fst b c), ?_, ?_⟩
  · simpa [c] using hz.map yoneda
  · exact MorphismProperty.of_isPullback hz' hb

private theorem open_cover_of_joint {S : Scheme.{u}} {I : Type u}
    {F : (Over S)ᵒᵖ ⥤ Type u} {G : I → (Over S)ᵒᵖ ⥤ Type u}
    (c : ∀ i, G i ⟶ F)
    (hc : ∀ i, IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) (c i))
    (hjoint : IsJointlySurjective c) (H : Over S) (a : yoneda.obj H ⟶ F) :
    ∃ (V : I → H.left.Opens)
      (k : ∀ i, yoneda.obj (Over.mk ((V i).ι ≫ H.hom)) ⟶ G i),
      (⨆ i, V i) = ⊤ ∧ ∀ i,
        IsPullback (k i) (yoneda.map (Over.homMk (V i).ι)) (c i) a := by
  classical
  choose V k hk using fun i ↦ scheme_test_open (hc i) H a
  refine ⟨V, k, ?_, hk⟩
  apply top_unique
  intro x hx
  let K : Type u := H.left.residueField x
  let r : Over.mk (H.left.fromSpecResidueField x ≫ H.hom) ⟶ H :=
    Over.homMk (H.left.fromSpecResidueField x)
  obtain ⟨i, L, hL, e, y, hy⟩ := hjoint K
    (H.left.fromSpecResidueField x ≫ H.hom) (yonedaEquiv (yoneda.map r ≫ a))
  let := hL
  let v : Over.mk (Spec.map (CommRingCat.ofHom e) ≫
      (H.left.fromSpecResidueField x ≫ H.hom)) ⟶
      Over.mk (H.left.fromSpecResidueField x ≫ H.hom) :=
    Over.homMk (Spec.map (CommRingCat.ofHom e)) rfl
  have heq : yonedaEquiv.symm y ≫ c i = yoneda.map (v ≫ r) ≫ a := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply, hy,
      yonedaEquiv_naturality, Functor.map_comp, Category.assoc]
  let l := (hk i).lift (yonedaEquiv.symm y) (yoneda.map (v ≫ r)) heq
  let lo := yoneda.preimage l
  have hl : lo ≫ Over.homMk (V i).ι = v ≫ r := by
    apply yoneda.map_injective
    simp [lo, l]
  have hpoint := congrArg (fun z ↦ z.left (IsLocalRing.closedPoint L)) hl
  have hmem : x ∈ V i := by
    have hvalue : (V i).ι (lo.left (IsLocalRing.closedPoint L)) = x := by
      simpa [v, r, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using hpoint
    exact hvalue ▸ (lo.left (IsLocalRing.closedPoint L)).property
  exact (TopologicalSpace.Opens.mem_iSup).mpr ⟨i, hmem⟩

/-- A separated chartwise locally quasi-finite space has affine atlas pieces over
an affine open covering of its target, with coverage on every scheme test.
Source: Stacks Project, Morphisms of Spaces, Tag 03XX, first two proof paragraphs;
Properties of Spaces, Tags 03FY and 03BZ
(blueprint: lem-a1-separated-lqf-affine-relation-cover).

Proof: cover the target by affine opens and pull the space back to each open.
Apply the affine atlas open cover theorem to each pullback. Compose its open
inclusions with the pullback open inclusion, and identify each resulting monomorphism
with its image subfunctor. Scheme tests of these inclusions are open subschemes.
For any test scheme, its inverse images of the affine target opens cover it; within
each, the point-covering property of the atlas pieces covers every residue-field
point, hence these open subschemes cover. Open restriction and base change preserve
the chartwise locally quasi-finite and closed-diagonal properties by
`space_separated_lqf_permanence`. Yoneda supplies each atlas structure map. -/
private theorem exists_separated_lqf_affine_atlas_cover {S : Scheme.{u}}
    (T : Over S) (E : AlgebraicSpace S) (f : E.obj.obj ⟶ yoneda.obj T)
    (hqf : ∀ (V : Over S) (a : yoneda.obj V ⟶ E.obj.obj), IsEtale a →
      Scheme.Hom.IsLocallyQuasiFinite (yoneda.preimage (a ≫ f)).left)
    (hsep : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (pullback.diagonal f)) :
    ∃ (I : Type u) (A : I → OpenSubspace E) (X : I → AlgebraicSpace S)
      (e : ∀ i : I, (X i).obj.obj ≅ (A i).val.toFunctor) (W : I → T.left.Opens),
      (∀ (H : Over S) (a : yoneda.obj H ⟶ E.obj.obj),
        ∃ (V : I → H.left.Opens)
          (k : ∀ i : I, yoneda.obj (Over.mk ((V i).ι ≫ H.hom)) ⟶ (X i).obj.obj),
          (⨆ i : I, V i) = ⊤ ∧ ∀ i : I,
            IsPullback (k i) (yoneda.map (Over.homMk (V i).ι))
              ((e i).hom ≫ (A i).val.ι) a) ∧
      ∀ i : I, IsAffine (W i).toScheme ∧
        ∃ (q : (X i).obj.obj ⟶ yoneda.obj (Over.mk ((W i).ι ≫ T.hom)))
          (U : Over S) (uT : U ⟶ Over.mk ((W i).ι ≫ T.hom))
          (p : yoneda.obj U ⟶ (X i).obj.obj),
          q ≫ yoneda.map (Over.homMk (W i).ι) = (e i).hom ≫ (A i).val.ι ≫ f ∧
          (∀ (V : Over S) (a : yoneda.obj V ⟶ (X i).obj.obj), IsEtale a →
            Scheme.Hom.IsLocallyQuasiFinite (yoneda.preimage (a ≫ q)).left) ∧
          IsRepresentableWith (fun _ _ v ↦ IsClosedImmersion v.left)
            (pullback.diagonal q) ∧
          IsAffine U.left ∧ IsEtale p ∧ IsSurjective p ∧ p ≫ q = yoneda.map uT := by
  classical
  let J := Scheme.fppfTopology.over S
  let fs : E.obj ⟶ J.yoneda.obj T := ⟨f⟩
  let B (W : T.left.affineOpens) : Over S := Over.mk (W.val.ι ≫ T.hom)
  let b (W : T.left.affineOpens) : B W ⟶ T := Over.homMk W.val.ι
  let ZS (W : T.left.affineOpens) := Limits.pullback fs (J.yoneda.map (b W))
  have hperm (W : T.left.affineOpens) :=
    space_separated_lqf_permanence T (B W) (b W) E fs hqf hsep
  let Z (W : T.left.affineOpens) : AlgebraicSpace S := ⟨ZS W, (hperm W).1⟩
  let z (W : T.left.affineOpens) : (Z W).obj.obj ⟶ E.obj.obj :=
    (pullback.fst fs (J.yoneda.map (b W))).hom
  let d (W : T.left.affineOpens) : (Z W).obj.obj ⟶ yoneda.obj (B W) :=
    (pullback.snd fs (J.yoneda.map (b W))).hom
  have hpb (W : T.left.affineOpens) : IsPullback (z W) (d W) f (yoneda.map (b W)) :=
    (IsPullback.of_hasPullback fs (J.yoneda.map (b W))).map (sheafToPresheaf _ _)
  have hzopen (W : T.left.affineOpens) :
      IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) (z W) :=
    atlas_representable_of_square _ (hpb W).flip
      (yoneda_open (b W) (inferInstance : IsOpenImmersion W.val.ι))
  choose N X j U p hj hp using fun W ↦ exists_affine_atlas_open_cover (Z W)
  let I : Type u := Σ W : T.left.affineOpens, N W
  let c (i : I) : (X i.1 i.2).obj.obj ⟶ E.obj.obj := (j i.1 i.2).hom.hom ≫ z i.1
  have hc (i : I) : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) (c i) :=
    open_comp (hp i.1 i.2).1 (hzopen i.1)
  have hmono (i : I) : Mono (c i) := open_mono (hc i)
  let A (i : I) : OpenSubspace E := ⟨Subfunctor.range (c i), open_range (hc i)⟩
  let e (i : I) : (X i.1 i.2).obj.obj ≅ (A i).val.toFunctor :=
    asIso (Subfunctor.toRange (c i))
  have hec (i : I) : (e i).hom ≫ (A i).val.ι = c i := rfl
  have hcover : IsJointlySurjective c := by
    intro K hK s x
    let a : yoneda.obj (Over.mk s) ⟶ E.obj.obj := yonedaEquiv.symm x
    let r : Over.mk s ⟶ T := yoneda.preimage (a ≫ f)
    obtain ⟨W, hW, hxW, _⟩ := exists_isAffineOpen_mem_and_subset
      (X := T.left) (x := r.left (IsLocalRing.closedPoint K)) (U := ⊤) (by trivial)
    let Wi : T.left.affineOpens := ⟨W, hW⟩
    let l : Spec (CommRingCat.of K) ⟶ W.toScheme :=
      IsOpenImmersion.lift W.ι r.left (by
        rintro _ ⟨v, rfl⟩
        refine ⟨⟨r.left v, ?_⟩, rfl⟩
        simpa only [Subsingleton.elim v (IsLocalRing.closedPoint K)] using hxW)
    have hl : l ≫ W.ι = r.left := IsOpenImmersion.lift_fac ..
    let lo : Over.mk s ⟶ B Wi := Over.homMk l (by
      change l ≫ (W.ι ≫ T.hom) = s
      rw [← Category.assoc, hl, Over.w r]
      rfl)
    have hlo : lo ≫ b Wi = r := by ext; exact hl
    let za := (hpb Wi).lift a (yoneda.map lo) (by
      rw [← Functor.map_comp, hlo]
      simp [r])
    obtain ⟨i, L, hL, ext, y, hy⟩ := hj Wi K s (yonedaEquiv za)
    let := hL
    refine ⟨⟨Wi, i⟩, L, hL, ext, y, ?_⟩
    change (z Wi).app _ ((j Wi i).hom.hom.app _ y) = _
    rw [hy, NatTrans.naturality_apply, ← yonedaEquiv_comp]
    simp [za, a]
  refine ⟨I, A, (fun i ↦ X i.1 i.2), e, (fun i ↦ i.1.val), ?_, ?_⟩
  · intro H a
    simpa only [hec] using open_cover_of_joint c hc hcover H a
  · intro i
    have hrest := (hperm i.1).2.2.2 (X i.1 i.2) (j i.1 i.2).hom (hp i.1 i.2).1
    let q := (j i.1 i.2).hom.hom ≫ d i.1
    refine ⟨i.1.property, q, U i.1 i.2,
      yoneda.preimage (p i.1 i.2 ≫ q), p i.1 i.2, ?_,
      hrest.1, hrest.2.1, (hp i.1 i.2).2.1,
      (hp i.1 i.2).2.2.1, (hp i.1 i.2).2.2.2.1, ?_⟩
    · change ((j i.1 i.2).hom.hom ≫ d i.1) ≫ yoneda.map (b i.1) =
        (e i).hom ≫ (A i).val.ι ≫ f
      rw [← Category.assoc, hec]
      exact congrArg (fun k ↦ (j i.1 i.2).hom.hom ≫ k) (hpb i.1).w.symm
    · simp


set_option backward.isDefEq.respectTransparency false in
private theorem kernel_isClosed {S : Scheme.{u}} (T : Over S) (X : AlgebraicSpace S)
    (q : X.obj.obj ⟶ yoneda.obj T)
    (hsep : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (pullback.diagonal q)) (U R : Over S) (p : yoneda.obj U ⟶ X.obj.obj)
    (uT : U ⟶ T) (hu : p ≫ q = yoneda.map uT) (s t : R ⟶ U)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) p p) :
    ∃ hst : s.left ≫ uT.left = t.left ≫ uT.left,
      IsClosedImmersion (pullback.lift s.left t.left hst) := by
  let D := Limits.pullback uT uT
  let a : yoneda.obj D ⟶ Limits.pullback q q :=
    pullback.lift (yoneda.map (pullback.fst uT uT) ≫ p)
      (yoneda.map (pullback.snd uT uT) ≫ p) (by
        simp only [Category.assoc, hu, ← Functor.map_comp, pullback.condition])
  obtain ⟨R', r, k, hk, hr⟩ := hsep D a
  let s' := r ≫ pullback.fst uT uT
  let t' := r ≫ pullback.snd uT uT
  have hks : yoneda.map s' ≫ p = k := by
    have he := hk.w =≫ pullback.fst q q
    simpa only [a, s', Category.assoc, pullback.lift_fst, pullback.diagonal_fst,
      Category.comp_id, Functor.map_comp] using he.symm
  have hkt : yoneda.map t' ≫ p = k := by
    have he := hk.w =≫ pullback.snd q q
    simpa only [a, t', Category.assoc, pullback.lift_snd, pullback.diagonal_snd,
      Category.comp_id, Functor.map_comp] using he.symm
  have hR' : IsPullback (yoneda.map s') (yoneda.map t') p p := by
    apply IsPullback.of_forall_isPullback_app
    rintro ⟨H⟩
    apply (Types.isPullback_iff _ _ _ _).2
    refine ⟨congr_app (hks.trans hkt.symm) (op H), ?_, ?_⟩
    · intro x y hxy
      change x ≫ s' = y ≫ s' ∧ x ≫ t' = y ≫ t' at hxy
      have hrxy : x ≫ r = y ≫ r := by
        apply (IsPullback.of_hasPullback uT uT).hom_ext
        · exact hxy.1
        · exact hxy.2
      have hkxy : k.app (op H) x = k.app (op H) y := by
        rw [← hks]
        change p.app (op H) (x ≫ s') = p.app (op H) (y ≫ s')
        rw [hxy.1]
      exact Types.ext_of_isPullback (hk.app (op H)) hkxy hrxy
    · intro x y hxy
      have hbase : x ≫ uT = y ≫ uT := by
        apply yoneda.map_injective
        apply yonedaEquiv.injective
        simpa only [Functor.map_comp, ← hu, yonedaEquiv_comp, yonedaEquiv_yoneda_map,
          NatTrans.comp_app, types_comp_apply] using congrArg (q.app (op H)) hxy
      let z : H ⟶ D := pullback.lift x y hbase
      have hz : (pullback.diagonal q).app (op H) (p.app (op H) x) = a.app (op H) z := by
        have he : yonedaEquiv.symm (p.app (op H) x) ≫ pullback.diagonal q =
            yoneda.map z ≫ a := by
          apply pullback.hom_ext
          · apply yonedaEquiv.injective
            simp only [a, z, Category.assoc, pullback.diagonal_fst, pullback.lift_fst,
              Category.comp_id, ← Functor.map_comp_assoc]
            simp only [yonedaEquiv_comp, yonedaEquiv_yoneda_map, Equiv.apply_symm_apply]
          · apply yonedaEquiv.injective
            simp only [a, z, Category.assoc, pullback.diagonal_snd, pullback.lift_snd,
              Category.comp_id, ← Functor.map_comp_assoc]
            simpa only [pullback.lift_snd, yonedaEquiv_comp, yonedaEquiv_yoneda_map,
              Equiv.apply_symm_apply] using hxy
        simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_yoneda_map]
          using congrArg yonedaEquiv he
      obtain ⟨v, _, hrv⟩ := Types.exists_of_isPullback (hk.app (op H)) (p.app (op H) x) z hz
      change v ≫ r = z at hrv
      refine ⟨v, ?_, ?_⟩
      · change v ≫ r ≫ pullback.fst uT uT = x
        rw [← Category.assoc, hrv]
        exact pullback.lift_fst _ _ _
      · change v ≫ r ≫ pullback.snd uT uT = y
        rw [← Category.assoc, hrv]
        exact pullback.lift_snd _ _ _
  let e : R ≅ R' := yoneda.preimageIso (hR.isoIsPullback _ _ hR')
  have hes : e.hom ≫ s' = s := by apply yoneda.map_injective; simp [e]
  have het : e.hom ≫ t' = t := by apply yoneda.map_injective; simp [e]
  have hst : s ≫ uT = t ≫ uT := by
    apply yoneda.map_injective
    simpa only [Functor.map_comp, ← hu, ← Category.assoc] using hR.w =≫ q
  refine ⟨congrArg (fun f ↦ f.left) hst, ?_⟩
  have : IsClosedImmersion r.left := hr
  have hD : IsPullback (pullback.fst uT uT).left (pullback.snd uT uT).left
      uT.left uT.left := (IsPullback.of_hasPullback uT uT).map (Over.forget S)
  have heq : pullback.lift s.left t.left (congrArg (fun f ↦ f.left) hst) =
      e.hom.left ≫ r.left ≫ hD.isoPullback.hom := by
    apply pullback.hom_ext
    · simpa only [s', Over.comp_left, Category.assoc, IsPullback.isoPullback_hom_fst,
      pullback.lift_fst]
        using congrArg (fun f ↦ f.left) hes.symm
    · simpa only [t', Over.comp_left, Category.assoc, IsPullback.isoPullback_hom_snd,
      pullback.lift_snd]
        using congrArg (fun f ↦ f.left) het.symm
  rw [heq]
  infer_instance

/-- A separated chartwise locally quasi-finite space admits open affine relation
presentations over affine opens of its target. `e` identifies the actual open subfunctor
with the algebraic space `X i`. The covering clause represents every inverse image by
open subschemes covering the whole test scheme. The coequalizers are the sectionwise
quotient presheaves; bijectivity of precomposition by `η` is their sheafification
universal property. The equations with `p` specify the canonical comparison and its
atlas compatibility. All maps are over `S`; the displayed maps to `Ti` and `B` retain
the relative structures.

Source: Stacks Project, Morphisms of Spaces, Tag 03XX, first three proof paragraphs;
Spaces, Tag 0262, clauses (1)-(3)
(blueprint: lem-a1-separated-lqf-affine-relation-cover).

Proof:
1. Choose affine opens of T using lem-weil-pbc-affine-opens-basis. Their inverse images
   are open spaces by lem-trf-space-fibre-products-etale-covers and
   lem-weil-pbc-open-preimage-fibre-product. Apply lem-a1-space-affine-atlas-open-cover
   to each inverse image, obtaining the pieces and affine surjective etale atlases.
   Apply lem-a1-space-separated-lqf-permanence to their open restrictions: every chart
   is locally quasi-finite and each relative diagonal is closed on scheme tests.
2. For an arbitrary scheme H mapping to E, its inverse images of the affine base opens
   cover H. On each one, lem-a1-space-etale-open-image and the point-covering clause
   of lem-a1-space-affine-atlas-open-cover imply that the inverse images of the chosen
   pieces cover every residue-field point. They are open subschemes by
   def-a1-space-open-subspace. Their union is therefore all of H, also when H is empty.
3. Apply lem-a1-etale-atlas-presentation to each atlas. It supplies its scheme kernel
   pair, surjective etale projections, the relation of equality of atlas images on
   every test, and the canonical fppf sheaf quotient compatible with the atlas.
   Regard the maps as maps over the affine base open; their structure maps agree
   because the relation is the kernel pair. This is def-trf-algebraic-space's same
   construction on the relative big site.
4. By def-pc-fibre-product the relation map into U times_Ti U is the scheme test of
   the relative diagonal along the atlas pair. It is closed by step 1. The product
   is affine by lem-weil-pbc-fibre-product-affine-spectra, hence R is affine by the
   affine-target description in def-weil-closed-immersion. No reducedness or
   Noetherian hypothesis is used.
5. For every B mapping to Ti, base change the atlas using
   lem-trf-space-fibre-products-etale-covers. The fibre-product universal property
   identifies its kernel pair with R times_Ti B, respecting both projections:
   sections on both sides are pairs of U-lifts having the same X-image and the
   prescribed B-map. Apply lem-a1-etale-atlas-presentation to this atlas over B.
   The resulting sheafification map is canonical, as it is induced by the specified
   atlas and the quotient universal property, and preserves the B-structure.
-/
theorem exists_separated_lqf_affine_relation_cover {S : Scheme.{u}}
    (T : Over S) (E : AlgebraicSpace S) (f : E.obj.obj ⟶ yoneda.obj T)
    (hqf : ∀ (V : Over S) (a : yoneda.obj V ⟶ E.obj.obj), IsEtale a →
      Scheme.Hom.IsLocallyQuasiFinite (yoneda.preimage (a ≫ f)).left)
    (hsep : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (pullback.diagonal f)) :
    ∃ (I : Type u) (A : I → OpenSubspace E) (X : I → AlgebraicSpace S)
      (e : ∀ i : I, (X i).obj.obj ≅ (A i).val.toFunctor) (W : I → T.left.Opens),
      (∀ (H : Over S) (a : yoneda.obj H ⟶ E.obj.obj),
        ∃ (V : I → H.left.Opens)
          (k : ∀ i : I, yoneda.obj (Over.mk ((V i).ι ≫ H.hom)) ⟶ (X i).obj.obj),
          (⨆ i : I, V i) = ⊤ ∧ ∀ i : I,
            IsPullback (k i) (yoneda.map (Over.homMk (V i).ι))
              ((e i).hom ≫ (A i).val.ι) a) ∧
      ∀ i : I, IsAffine (W i).toScheme ∧
        ∃ (q : (X i).obj.obj ⟶ yoneda.obj (Over.mk ((W i).ι ≫ T.hom)))
          (U R : Over S) (uT : U ⟶ Over.mk ((W i).ι ≫ T.hom)) (s t : R ⟶ U)
          (p : yoneda.obj U ⟶ (X i).obj.obj),
          q ≫ yoneda.map (Over.homMk (W i).ι) = (e i).hom ≫ (A i).val.ι ≫ f ∧
          (∀ (V : Over S) (a : yoneda.obj V ⟶ (X i).obj.obj), IsEtale a →
            Scheme.Hom.IsLocallyQuasiFinite (yoneda.preimage (a ≫ q)).left) ∧
          IsRepresentableWith (fun _ _ v ↦ IsClosedImmersion v.left)
            (pullback.diagonal q) ∧
          IsAffine U.left ∧ IsAffine R.left ∧ IsEtale p ∧ IsSurjective p ∧
          p ≫ q = yoneda.map uT ∧ Scheme.Hom.IsLocallyQuasiFinite uT.left ∧
          IsPullback (yoneda.map s) (yoneda.map t) p p ∧
          Etale s.left ∧ Surjective s.left ∧ Etale t.left ∧ Surjective t.left ∧
          (∃ hst : s.left ≫ uT.left = t.left ≫ uT.left,
            IsClosedImmersion (pullback.lift s.left t.left hst)) ∧
          (∀ H : Over S,
            Function.Injective (fun r : H ⟶ R ↦ (r ≫ s, r ≫ t)) ∧
            Equivalence (fun a b : H ⟶ U ↦ ∃ r : H ⟶ R, r ≫ s = a ∧ r ≫ t = b) ∧
            ∀ a b : H ⟶ U,
              (∃ r : H ⟶ R, r ≫ s = a ∧ r ≫ t = b) ↔
                p.app (op H) a = p.app (op H) b) ∧
          (∃ η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ (X i).obj.obj,
            coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η = p ∧
            ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
              Function.Bijective (fun a : (X i).obj.obj ⟶ G.obj ↦ η ≫ a)) ∧
          ∀ (B : Over S) (b : B ⟶ Over.mk ((W i).ι ≫ T.hom)),
            ∃ (UB RB : Over S) (v : UB ⟶ U) (uB : UB ⟶ B)
              (w : RB ⟶ R) (rB : RB ⟶ B) (sB tB : RB ⟶ UB)
              (XB : AlgebraicSpace S) (g : XB.obj.obj ⟶ (X i).obj.obj)
              (d : XB.obj.obj ⟶ yoneda.obj B) (pB : yoneda.obj UB ⟶ XB.obj.obj),
              IsPullback v uB uT b ∧ IsPullback w rB (s ≫ uT) b ∧
              IsPullback g d q (yoneda.map b) ∧
              pB ≫ g = yoneda.map v ≫ p ∧ pB ≫ d = yoneda.map uB ∧
              sB ≫ v = w ≫ s ∧ tB ≫ v = w ≫ t ∧
              sB ≫ uB = rB ∧ tB ≫ uB = rB ∧
              IsEtale pB ∧ IsSurjective pB ∧
              IsPullback (yoneda.map sB) (yoneda.map tB) pB pB ∧
              ∃ ηB : coequalizer (yoneda.map sB) (yoneda.map tB) ⟶ XB.obj.obj,
                coequalizer.π (yoneda.map sB) (yoneda.map tB) ≫ ηB = pB ∧
                ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
                  Function.Bijective (fun a : XB.obj.obj ⟶ G.obj ↦ ηB ≫ a) 
    := by
  classical
  obtain ⟨I, A, X, e, W, hcover, hlocal⟩ :=
    exists_separated_lqf_affine_atlas_cover T E f hqf hsep
  refine ⟨I, A, X, e, W, hcover, fun i ↦ ?_⟩
  obtain ⟨hW, q, U, uT, p, hq, hqf', hsep', hU, hp, hsur, hpq⟩ := hlocal i
  obtain ⟨R, s, t, hR, hs, hss, ht, hts, hsections, hquot, hbase⟩ :=
    exists_atlas_relation_baseChange _ (X i) q U uT p hp hsur hpq
  obtain ⟨hst, hclosed⟩ := kernel_isClosed _ (X i) q hsep' U R p uT hpq s t hR
  have : IsAffine (W i).toScheme := hW
  have : IsAffine (Over.mk ((W i).ι ≫ T.hom)).left := hW
  have : IsAffine U.left := hU
  have : IsClosedImmersion (pullback.lift s.left t.left hst) := hclosed
  have hAffine : IsAffine R.left := isAffine_of_isAffineHom
    (pullback.lift s.left t.left hst)
  exact ⟨hW, q, U, R, uT, s, t, p, hq, hqf', hsep', hU, hAffine,
    hp, hsur, hpq, (by simpa only [hpq, yoneda.preimage_map] using hqf' U p hp),
    hR, hs, hss, ht, hts, ⟨hst, hclosed⟩,
    hsections, hquot, hbase⟩

end AlgebraicGeometry.AlgebraicSpace
