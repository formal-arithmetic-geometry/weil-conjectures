/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q123
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Sheaf.AlgebraicGeometry.EtaleAtlasPresentation
import Sheaf.AlgebraicGeometry.ProperEtaleRelationFiniteNeighbourhood
import Sheaf.AlgebraicGeometry.FiniteFlatAffineRelationQuotient
import Sheaf.AlgebraicGeometry.EtaleRelationFindingOpens
import Sheaf.AlgebraicGeometry.EtaleQuasiAffineImageScheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Schematic neighbourhoods from finite restricted affine relations

Source: Stacks Project, Spaces and Morphisms, Tag 03XX,
proposition-locally-quasi-finite-separated-over-scheme, fourth and final proof paragraphs
(blueprint: lem-a1-closed-relation-schematic-neighbourhood).

The clopen pieces are schemes equipped with open immersions with complementary images.
The full restricted relation is specified by its representing pullback square. Quotients
are sheafifications of presheaf coequalizers, specified by their hom-set universal property.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

private theorem property_of_square {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {F G : (Over S)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hf : IsRepresentableWith (fun _ _ m ↦ P m.left) f)
    {T U : Over S} {a : yoneda.obj T ⟶ G} (p : U ⟶ T)
    (q : yoneda.obj U ⟶ F) (hsq : IsPullback q (yoneda.map p) f a) : P p.left := by
  obtain ⟨V, p₀, q₀, h₀, hp₀⟩ := hf T a
  let e := yoneda.preimageIso (hsq.isoIsPullback _ _ h₀)
  have he : e.hom ≫ p₀ = p := by
    apply yoneda.map_injective
    simp [e]
  rw [← he, Over.comp_left, P.cancel_left_of_respectsIso]
  exact hp₀

private theorem representable_of_square {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u})
    {A B F G : (Over S)ᵒᵖ ⥤ Type u} {q : A ⟶ B} {p' : A ⟶ G}
    {p : B ⟶ F} {g : G ⟶ F} (h : IsPullback q p' p g)
    (hp : IsRepresentableWith (fun _ _ m ↦ P m.left) p) :
    IsRepresentableWith (fun _ _ m ↦ P m.left) p' := by
  intro T a
  obtain ⟨V, r, l, hl, hr⟩ := hp T (a ≫ g)
  let l' := h.lift l (yoneda.map r ≫ a) (by simpa using hl.w)
  refine ⟨V, r, l', ?_, hr⟩
  have hl' : IsPullback (l' ≫ q) (yoneda.map r) p (a ≫ g) := by
    simpa [l'] using hl
  exact hl'.of_right (by simp [l']) h

private theorem locally_surjective_of_square
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    {A B F G : Cᵒᵖ ⥤ Type u} {q : A ⟶ B} {p' : A ⟶ G}
    {p : B ⟶ F} {g : G ⟶ F} (h : IsPullback q p' p g)
    [Presheaf.IsLocallySurjective J p] : Presheaf.IsLocallySurjective J p' := by
  constructor
  intro T x
  apply J.superset_covering ?_ (Presheaf.imageSieve_mem J p (g.app _ x))
  rintro V i ⟨b, hb⟩
  obtain ⟨a, _, ha⟩ := Types.exists_of_isPullback
    (h.map ((evaluation Cᵒᵖ (Type u)).obj (Opposite.op V))) b (G.map i.op x)
      (hb.trans (NatTrans.naturality_apply g i.op x).symm)
  exact ⟨a, ha⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem descend_kernel_pair {C : Type*} [Category C]
    (J : GrothendieckTopology C) {A B F : Cᵒᵖ ⥤ Type u}
    (s t : B ⟶ A) (p : A ⟶ F) (hR : IsPullback s t p p)
    [Presheaf.IsLocallySurjective J p] (G : Sheaf J (Type u))
    (l : A ⟶ G.obj) (hl : s ≫ l = t ≫ l) :
    ∃! k : F ⟶ G.obj, p ≫ k = l := by
  classical
  have heq (V : Cᵒᵖ) (a b : A.obj V) (hab : p.app V a = p.app V b) :
      l.app V a = l.app V b := by
    obtain ⟨r, hr, ht⟩ := Types.exists_of_isPullback
      (hR.map ((evaluation Cᵒᵖ (Type u)).obj V)) a b hab
    rw [← hr, ← ht]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hl V) r
  let family (V : Cᵒᵖ) (x : F.obj V) :
      Presieve.FamilyOfElements G.obj (Presheaf.imageSieve p x).arrows :=
    fun W i hi ↦ l.app (Opposite.op W) (Presheaf.localPreimage p x i hi)
  have hfamily (V : Cᵒᵖ) (x : F.obj V) : (family V x).Compatible := by
    intro V₁ V₂ W j₁ j₂ i₁ i₂ hi₁ hi₂ hij
    dsimp [family]
    rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
    apply heq
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply,
      Presheaf.app_localPreimage, Presheaf.app_localPreimage,
      ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hij]
  let H (V : Cᵒᵖ) (x : F.obj V) :=
    (isSheaf_iff_isSheaf_of_type J G.obj).mp G.property
      (Presheaf.imageSieve p x) (Presheaf.imageSieve_mem J p x)
  let d (V : Cᵒᵖ) (x : F.obj V) := (H V x).amalgamate (family V x) (hfamily V x)
  have hd (V : Cᵒᵖ) (x : F.obj V) (W : C) (i : W ⟶ V.unop)
      (a : A.obj (Opposite.op W)) (ha : p.app (Opposite.op W) a = F.map i.op x) :
      G.obj.map i.op (d V x) = l.app (Opposite.op W) a := by
    have hi : (Presheaf.imageSieve p x) i := ⟨a, ha⟩
    exact ((H V x).valid_glue (hfamily V x) i hi).trans
      (heq _ _ _ ((Presheaf.app_localPreimage p x i hi).trans ha.symm))
  let k : F ⟶ G.obj :=
    { app := fun V ↦ ↾(d V)
      naturality := by
        intro V W f
        ext x
        apply (((isSheaf_iff_isSheaf_of_type J G.obj).mp G.property).isSeparated _
          (Presheaf.imageSieve_mem J p (F.map f x))).ext
        rintro Z i ⟨a, ha⟩
        symm
        change G.obj.map i.op (G.obj.map f (d V x)) =
          G.obj.map i.op (d W (F.map f x))
        rw [← Functor.map_comp_apply]
        exact (hd V x Z (i ≫ f.unop) a (by simpa using ha)).trans
          (hd W (F.map f x) Z i a ha).symm }
  have hk : p ≫ k = l := by
    ext V a
    simpa [k] using hd V (p.app V a) V.unop (𝟙 _) a (by simp)
  refine ⟨k, hk, ?_⟩
  intro k' hk'
  ext V x
  apply (((isSheaf_iff_isSheaf_of_type J G.obj).mp G.property).isSeparated _
    (Presheaf.imageSieve_mem J p x)).ext
  rintro W i ⟨a, ha⟩
  change G.obj.map i.op (k'.app V x) = G.obj.map i.op (k.app V x)
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, ← ha]
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app hk' (Opposite.op W)) a).trans
    (ConcreteCategory.congr_hom (NatTrans.congr_app hk (Opposite.op W)) a).symm

private theorem kernel_pair_universal {C : Type*} [Category C]
    (J : GrothendieckTopology C) {A B F : Cᵒᵖ ⥤ Type u}
    (s t : B ⟶ A) (p : A ⟶ F) (hR : IsPullback s t p p)
    [Presheaf.IsLocallySurjective J p] :
    ∃ η : coequalizer s t ⟶ F, coequalizer.π s t ≫ η = p ∧
      ∀ G : Sheaf J (Type u), Function.Bijective (fun k : F ⟶ G.obj ↦ η ≫ k) := by
  let η := coequalizer.desc p hR.w
  have he : coequalizer.π s t ≫ η = p := coequalizer.π_desc _ _
  refine ⟨η, he, ?_⟩
  intro G
  constructor
  · intro k k' h
    change η ≫ k = η ≫ k' at h
    have hh : p ≫ k = p ≫ k' := by
      simpa only [← Category.assoc, he] using congrArg (coequalizer.π s t ≫ ·) h
    obtain ⟨d, _, hd⟩ := descend_kernel_pair J s t p hR G (p ≫ k)
      (by simp only [← Category.assoc, hR.w])
    exact (hd k rfl).trans (hd k' hh.symm).symm
  · intro l
    let d := coequalizer.π s t ≫ l
    obtain ⟨k, hk, _⟩ := descend_kernel_pair J s t p hR G d
      (by dsimp [d]; rw [← Category.assoc, ← Category.assoc, coequalizer.condition])
    refine ⟨k, ?_⟩
    apply coequalizer.hom_ext
    simpa only [← Category.assoc, he] using hk

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem basechange_kernel_pair {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {U R T T' : Over S}
    (p : yoneda.obj U ⟶ F) (f : F ⟶ yoneda.obj T)
    (s t : R ⟶ U) (hR : IsPullback (yoneda.map s) (yoneda.map t) p p)
    (b : U ⟶ T) (a : T' ⟶ T)
    (s₀ t₀ : Limits.pullback (s ≫ b) a ⟶ Limits.pullback b a)
    (hs : s₀ ≫ pullback.fst b a = pullback.fst (s ≫ b) a ≫ s)
    (ht : t₀ ≫ pullback.fst b a = pullback.fst (s ≫ b) a ≫ t)
    (hsb : s₀ ≫ pullback.snd b a = pullback.snd (s ≫ b) a)
    (htb : t₀ ≫ pullback.snd b a = pullback.snd (s ≫ b) a)
    (p₀ : yoneda.obj (Limits.pullback b a) ⟶ Limits.pullback f (yoneda.map a))
    (h₀ : p₀ ≫ pullback.fst f (yoneda.map a) = yoneda.map (pullback.fst b a) ≫ p)
    (h₁ : p₀ ≫ pullback.snd f (yoneda.map a) = yoneda.map (pullback.snd b a)) :
    IsPullback (yoneda.map s₀) (yoneda.map t₀) p₀ p₀ := by
  apply IsPullback.of_forall_isPullback_app
  intro H
  rw [Types.isPullback_iff]
  have he (x : H.unop ⟶ Limits.pullback b a) :
      (pullback.fst f (yoneda.map a)).app H (p₀.app H x) =
        p.app H (x ≫ pullback.fst b a) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app h₀ H) x
  have he' (x : H.unop ⟶ Limits.pullback b a) :
      (pullback.snd f (yoneda.map a)).app H (p₀.app H x) =
        x ≫ pullback.snd b a := ConcreteCategory.congr_hom (NatTrans.congr_app h₁ H) x
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro r
    change p₀.app H (r ≫ s₀) = p₀.app H (r ≫ t₀)
    apply Types.ext_of_isPullback ((IsPullback.of_hasPullback f (yoneda.map a)).app H)
    · simp only [he, Category.assoc, hs, ht]
      have hh := congrArg (fun l ↦ l.app H (r ≫ pullback.fst (s ≫ b) a)) hR.w
      exact hh
    · simp only [he', Category.assoc, hsb, htb]
  · intro r r' hrr
    change r ≫ s₀ = r' ≫ s₀ ∧ r ≫ t₀ = r' ≫ t₀ at hrr
    apply pullback.hom_ext
    · apply Types.ext_of_isPullback (hR.app H)
      · change (r ≫ pullback.fst (s ≫ b) a) ≫ s =
          (r' ≫ pullback.fst (s ≫ b) a) ≫ s
        simpa only [Category.assoc, ← hs] using congrArg
          (· ≫ pullback.fst b a) hrr.1
      · change (r ≫ pullback.fst (s ≫ b) a) ≫ t =
          (r' ≫ pullback.fst (s ≫ b) a) ≫ t
        simpa only [Category.assoc, ← ht] using congrArg
          (· ≫ pullback.fst b a) hrr.2
    · simpa only [Category.assoc, hsb] using congrArg (· ≫ pullback.snd b a) hrr.1
  · intro x y hxy
    have hpx : p.app H (x ≫ pullback.fst b a) =
        p.app H (y ≫ pullback.fst b a) := by rw [← he, ← he, hxy]
    obtain ⟨r, hrs, hrt⟩ := Types.exists_of_isPullback (hR.app H) _ _ hpx
    have hbase : x ≫ pullback.snd b a = y ≫ pullback.snd b a := by
      rw [← he', ← he', hxy]
    change r ≫ s = x ≫ pullback.fst b a at hrs
    change r ≫ t = y ≫ pullback.fst b a at hrt
    let z : H.unop ⟶ Limits.pullback (s ≫ b) a :=
      pullback.lift r (x ≫ pullback.snd b a) (by
        rw [← Category.assoc, hrs, Category.assoc, pullback.condition, Category.assoc])
    refine ⟨z, ?_, ?_⟩
    · apply pullback.hom_ext <;> simp [z, Category.assoc, hs, hsb, hrs]
    · apply pullback.hom_ext <;> simp [z, Category.assoc, ht, htb, hrt, hbase]

private theorem restricted_kernel_pair {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {R U V : Over S} (s t : R ⟶ U)
    (p : yoneda.obj U ⟶ F) (h : IsPullback (yoneda.map s) (yoneda.map t) p p)
    (g : V ⟶ U) :
    IsPullback
      (yoneda.map (pullback.fst (pullback.snd g s ≫ t) g ≫ pullback.fst g s))
      (yoneda.map (pullback.snd (pullback.snd g s ≫ t) g))
      (yoneda.map g ≫ p) (yoneda.map g ≫ p) := by
  have h₁ := ((IsPullback.of_hasPullback g s).flip.map yoneda).paste_horiz h.flip
  have h₂ := (IsPullback.of_hasPullback (pullback.snd g s ≫ t) g).map yoneda
  have h₁' : IsPullback (yoneda.map (pullback.snd g s ≫ t))
      (yoneda.map (pullback.fst g s)) p (yoneda.map g ≫ p) := by
    simpa only [Functor.map_comp] using h₁
  have h₂' : IsPullback (yoneda.map (pullback.fst (pullback.snd g s ≫ t) g))
      (yoneda.map (pullback.snd (pullback.snd g s ≫ t) g))
      (yoneda.map (pullback.snd g s ≫ t)) (yoneda.map g) := h₂
  simpa only [Functor.map_comp] using (h₂'.flip.paste_vert h₁').flip

set_option backward.isDefEq.respectTransparency false in
private theorem affine_quotient {S : Scheme.{u}} (U R : Over S)
    [IsAffine U.left] [IsAffine R.left] (s t : R ⟶ U) [Mono (prod.lift s t)]
    [s.left.IsFiniteLocallyFree] [t.left.IsFiniteLocallyFree]
    (hrel : ∀ H : Over S, Equivalence (fun x y : H ⟶ U ↦
      ∃ r : H ⟶ R, r ≫ s = x ∧ r ≫ t = y)) :
    ∃ (Q : Over S) (e : U ⟶ Q), IsAffine Q.left ∧ e.left.IsFiniteLocallyFree ∧
      Surjective e.left ∧ Presheaf.IsSheaf (Scheme.fppfTopology.over S) (yoneda.obj Q) ∧
      ∃ η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ yoneda.obj Q,
        coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η = yoneda.map e ∧
        ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
          Function.Bijective (fun l : yoneda.obj Q ⟶ G.obj ↦ η ≫ l) := by
  classical
  let Ua : Over S := Over.mk (U.left.isoSpec.inv ≫ U.hom)
  let Ra : Over S := Over.mk (R.left.isoSpec.inv ≫ R.hom)
  let iU : U ≅ Ua := Over.isoMk U.left.isoSpec (by simp [Ua])
  let iR : R ≅ Ra := Over.isoMk R.left.isoSpec (by simp [Ra])
  let sa : Ra ⟶ Ua := iR.inv ≫ s ≫ iU.hom
  let ta : Ra ⟶ Ua := iR.inv ≫ t ≫ iU.hom
  have hmono : Mono (prod.lift sa ta) := by
    constructor
    intro H v w h
    have hs : (v ≫ iR.inv) ≫ s = (w ≫ iR.inv) ≫ s := by
      simpa [sa] using (h =≫ prod.fst) =≫ iU.inv
    have ht : (v ≫ iR.inv) ≫ t = (w ≫ iR.inv) ≫ t := by
      simpa [ta] using (h =≫ prod.snd) =≫ iU.inv
    apply (cancel_mono iR.inv).mp
    apply (cancel_mono (prod.lift s t)).mp
    exact prod.hom_ext (by simpa using hs) (by simpa using ht)
  have : Mono (prod.lift sa ta :
      Over.mk Ra.hom ⟶ Limits.prod (Over.mk Ua.hom) (Over.mk Ua.hom)) := hmono
  have hsfl : sa.left.IsFiniteLocallyFree := by
    dsimp [sa]
    constructor
  have htfl : ta.left.IsFiniteLocallyFree := by
    dsimp [ta]
    constructor
  let := hsfl
  let := htfl
  have hrel' : ∀ H : Over S, Equivalence (fun x y : H ⟶ Ua ↦
      ∃ r : H ⟶ Ra, r ≫ sa = x ∧ r ≫ ta = y) := by
    intro H
    have heq (x y : H ⟶ Ua) :
        (∃ r : H ⟶ Ra, r ≫ sa = x ∧ r ≫ ta = y) ↔
          ∃ r : H ⟶ R, r ≫ s = x ≫ iU.inv ∧ r ≫ t = y ≫ iU.inv := by
      constructor
      · rintro ⟨r, hr, ht⟩
        exact ⟨r ≫ iR.inv, by simpa [sa] using hr =≫ iU.inv,
          by simpa [ta] using ht =≫ iU.inv⟩
      · rintro ⟨r, hr, ht⟩
        exact ⟨r ≫ iR.hom, by simp [sa, reassoc_of% hr],
          by simp [ta, reassoc_of% ht]⟩
    exact ⟨fun x ↦ (heq x x).mpr ((hrel H).refl _),
      fun h ↦ (heq _ _).mpr ((hrel H).symm ((heq _ _).mp h)),
      fun h h' ↦ (heq _ _).mpr ((hrel H).trans ((heq _ _).mp h) ((heq _ _).mp h'))⟩
  obtain ⟨hf, hsur, _, m, he, _, hsh, ηa, hηa, hη⟩ :=
    finiteFlat_affineRelation_quotient Ua.hom Ra.hom sa ta hrel'
  let Q : Over S := Over.mk m
  let ea : Ua ⟶ Q := Over.homMk (affineRelationQuotientMap sa.left ta.left) he
  let e := iU.hom ≫ ea
  let d := parallelPairIso (yoneda.map s) (yoneda.map t) (yoneda.map sa) (yoneda.map ta)
    (yoneda.mapIso iR) (yoneda.mapIso iU)
    (by
      change yoneda.map s ≫ yoneda.map iU.hom = yoneda.map iR.hom ≫ yoneda.map sa
      simp only [← yoneda.map_comp]
      congr 1
      simp [sa])
    (by
      change yoneda.map t ≫ yoneda.map iU.hom = yoneda.map iR.hom ≫ yoneda.map ta
      simp only [← yoneda.map_comp]
      congr 1
      simp [ta])
  let δ := HasColimit.isoOfNatIso d
  let η := δ.hom ≫ ηa
  have hπ : coequalizer.π (yoneda.map s) (yoneda.map t) ≫ δ.hom =
      yoneda.map iU.hom ≫ coequalizer.π (yoneda.map sa) (yoneda.map ta) :=
    HasColimit.isoOfNatIso_ι_hom d WalkingParallelPair.one
  refine ⟨Q, e, show IsAffine (Spec _) from inferInstance, ?_, ?_, hsh, η, ?_, ?_⟩
  · let := hf
    change (U.left.isoSpec.hom ≫ affineRelationQuotientMap sa.left ta.left).IsFiniteLocallyFree
    constructor
  · let := hsur
    change Surjective (U.left.isoSpec.hom ≫ affineRelationQuotientMap sa.left ta.left)
    infer_instance
  · dsimp [η]
    rw [← Category.assoc, hπ, Category.assoc, hηa]
    exact (yoneda.map_comp _ _).symm
  · intro G
    change Function.Bijective (fun l ↦ δ.hom ≫ ηa ≫ l)
    constructor
    · intro l l' h
      apply (hη G).injective
      exact (cancel_epi δ.hom).mp h
    · intro v
      obtain ⟨l, hl⟩ := (hη G).surjective (δ.inv ≫ v)
      dsimp only at hl ⊢
      exact ⟨l, by rw [hl, Iso.hom_inv_id_assoc]⟩

private theorem isCompl_ranges_of_iso {Y Z : Scheme.{u}} (i : Y ≅ Z)
    (V W : Y.Opens) (h : IsCompl V W) :
    IsCompl (Set.range (V.ι ≫ i.hom)) (Set.range (W.ι ≫ i.hom)) := by
  have hr (V : Y.Opens) : Set.range (V.ι ≫ i.hom) = i.inv ⁻¹' (V : Set Y) := by
    ext z
    constructor
    · rintro ⟨v, rfl⟩
      simp
    · intro hz
      refine ⟨⟨i.inv z, hz⟩, ?_⟩
      change i.hom (i.inv z) = z
      simp
  rw [hr, hr]
  exact (h.map TopologicalSpace.Opens.frameHom).preimage i.inv

private theorem schemePointMap_comp {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {U V : Over S} (d : U ⟶ V) (v : yoneda.obj V ⟶ F) (x : U.left) :
    schemePointMap (yoneda.map d ≫ v) x = schemePointMap v (d.left x) := by
  apply Quot.sound
  let rx : Over.mk (U.left.fromSpecResidueField x ≫ U.hom) ⟶ U :=
    Over.homMk (U.left.fromSpecResidueField x) rfl
  let ry : Over.mk (V.left.fromSpecResidueField (d.left x) ≫ V.hom) ⟶ V :=
    Over.homMk (V.left.fromSpecResidueField (d.left x)) rfl
  let e : Over.mk (U.left.fromSpecResidueField x ≫ U.hom) ⟶
      Over.mk (V.left.fromSpecResidueField (d.left x) ≫ V.hom) :=
    Over.homMk (Spec.map (d.left.residueFieldMap x)) (by
      simp only [Over.mk_hom, ← Category.assoc,
        Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
      simp [Category.assoc])
  refine ⟨U.left.residueField x, inferInstance, U.left.fromSpecResidueField x ≫ U.hom,
    𝟙 _, e, ?_⟩
  change F.map (𝟙 _).op (v.app _ (rx ≫ d)) = F.map e.op (v.app _ ry)
  rw [op_id, F.map_id, types_id_apply, ← NatTrans.naturality_apply]
  congr 1
  apply Over.OverMorphism.ext
  exact (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField d.left x).symm

private theorem range_subset_of_fieldImage {S : Scheme.{u}} {X : AlgebraicSpace S}
    {V W : Over S} (v : yoneda.obj V ⟶ X.obj.obj) (w : yoneda.obj W ⟶ X.obj.obj)
    (h : ∀ (U : Over S) (g : yoneda.obj U ⟶ X.obj.obj), IsFieldSpectrum U →
      FieldPointImage U g V v → FieldPointImage U g W w) :
    Set.range (schemePointMap v) ⊆ Set.range (schemePointMap w) := by
  rintro _ ⟨x, rfl⟩
  let U : Over S := Over.mk (V.left.fromSpecResidueField x ≫ V.hom)
  let rx : U ⟶ V := Over.homMk (V.left.fromSpecResidueField x) rfl
  have hU : IsFieldSpectrum U := ⟨V.left.residueField x, inferInstance, ⟨Iso.refl _⟩⟩
  obtain ⟨E, i, j, hE, he⟩ := h U (yoneda.map rx ≫ v) hU
    ⟨U, 𝟙 U, rx, hU, by simp⟩
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  let y : E.left := e.inv (IsLocalRing.closedPoint K)
  have hx : rx.left (i.left y) = x := Scheme.fromSpecResidueField_apply _ _
  refine ⟨j.left y, ?_⟩
  rw [← schemePointMap_comp j w y, ← he, schemePointMap_comp i,
    schemePointMap_comp rx, hx]

private theorem mono_of_representable_open {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {W : Over S} (w : yoneda.obj W ⟶ F)
    (hw : IsRepresentableWith (fun _ _ m ↦ IsOpenImmersion m.left) w) : Mono w := by
  apply (NatTrans.mono_iff_mono_app w).mpr
  intro H
  apply (mono_iff_injective _).mpr
  intro a b hab
  let v := yoneda.map a ≫ w
  obtain ⟨P, p, q, hP, hp⟩ := hw H.unop v
  have : IsOpenImmersion p.left := hp
  have : Mono p := Over.mono_of_mono_left p
  have : Mono (yoneda.map p) := inferInstance
  have hb : yoneda.map b ≫ w = v := by
    apply yonedaEquiv.injective
    simpa only [v, yonedaEquiv_comp, yonedaEquiv_yoneda_map] using hab.symm
  let la := hP.lift (yoneda.map a) (𝟙 _) (by simp [v])
  let lb := hP.lift (yoneda.map b) (𝟙 _) (by simp [hb])
  have hab' : la = lb := (cancel_mono (yoneda.map p)).mp (by
    simp [la, lb])
  apply yoneda.map_injective
  calc
    yoneda.map a = la ≫ q := (hP.lift_fst _ _ _).symm
    _ = lb ≫ q := congrArg (· ≫ q) hab'
    _ = yoneda.map b := hP.lift_fst _ _ _

private theorem openSubspace_of_representable_open {S : Scheme.{u}}
    (X : AlgebraicSpace S) (Z : Over S) (w : yoneda.obj Z ⟶ X.obj.obj)
    (hw : IsRepresentableWith (fun _ _ m ↦ IsOpenImmersion m.left) w) :
    ∃ (W : OpenSubspace X) (eW : yoneda.obj Z ≅ W.val.toFunctor),
      eW.hom ≫ W.val.ι = w := by
  have : Mono w := mono_of_representable_open w hw
  let e : yoneda.obj Z ≅ (Subfunctor.range w).toFunctor := asIso (Subfunctor.toRange w)
  have hι : IsRepresentableWith (fun _ _ m ↦ IsOpenImmersion m.left)
      (Subfunctor.range w).ι := by
    intro T a
    obtain ⟨U, p, q, hP, hp⟩ := hw T a
    refine ⟨U, p, q ≫ e.hom, ?_, hp⟩
    exact hP.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp [e]) (by simp)
  exact ⟨⟨Subfunctor.range w, hι⟩, e, Subfunctor.toRange_ι w⟩

private theorem schematic_image_of_affine_open {S : Scheme.{u}}
    (T T' : Over S) [IsAffine T.left] [IsAffine T'.left]
    (a : T' ⟶ T) [Etale a.left] (X : AlgebraicSpace S)
    (f : X.obj.obj ⟶ yoneda.obj T)
    (hlocal : ∀ (H : Over S) (v : yoneda.obj H ⟶ X.obj.obj) (c : H ⟶ T),
      IsEtale v → yoneda.map c = v ≫ f → Scheme.Hom.IsLocallyQuasiFinite c.left)
    (hdiag : IsRepresentableWith (fun _ _ m ↦ IsClosedImmersion m.left)
      (Limits.pullback.diagonal f))
    (Q : Over S) [IsAffine Q.left] (c : Q ⟶ T')
    (z : yoneda.obj Q ⟶ Limits.pullback f (yoneda.map a))
    (hzc : z ≫ Limits.pullback.snd f (yoneda.map a) = yoneda.map c)
    (hz : IsRepresentableWith (fun _ _ m ↦ IsOpenImmersion m.left) z) :
    ∃ (W : OpenSubspace X) (Z : Over S) (eW : yoneda.obj Z ≅ W.val.toFunctor),
      Set.range (schemePointMap (z ≫ Limits.pullback.fst f (yoneda.map a))) =
        Set.range (schemePointMap (eW.hom ≫ W.val.ι)) := by
  let v := z ≫ Limits.pullback.fst f (yoneda.map a)
  have hcomm : v ≫ f = yoneda.map c ≫ yoneda.map a := by
    rw [← hzc, Category.assoc, Category.assoc, pullback.condition]
  have hlift : Limits.pullback.lift v (yoneda.map c) hcomm = z := by
    apply pullback.hom_ext <;> simp [v, hzc]
  obtain ⟨Z, w, _, hw, him⟩ := etale_quasiAffine_image_scheme T T' a X f hlocal hdiag
    Q v c hcomm (hlift ▸ hz) ⟨Q, 𝟙 Q, c, by simp, inferInstance,
      inferInstance, inferInstance⟩
  obtain ⟨W, eW, heW⟩ := openSubspace_of_representable_open X Z w hw
  refine ⟨W, Z, eW, ?_⟩
  rw [heW]
  exact Set.Subset.antisymm
    (range_subset_of_fieldImage v w (fun U g hU ↦ (him U g hU).mp))
    (range_subset_of_fieldImage w v (fun U g hU ↦ (him U g hU).mpr))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A finite clopen restriction of a closed affine atlas relation has an affine quotient,
an open embedding after étale base change, and a schematic open image containing the
original point. `W` is the open subfunctor itself, and `eW` represents it by a scheme.
The last two clauses compare images in the existing field-valued point-class quotient.

Source: Stacks Project, Spaces and Morphisms, Tag 03XX,
proposition-locally-quasi-finite-separated-over-scheme, fourth and final proof paragraphs
(blueprint: lem-a1-closed-relation-schematic-neighbourhood).

Proof:
1. Apply lem-a1-etale-atlas-presentation: the kernel pair has surjective étale projections
   and is an equivalence relation. Apply the chartwise hypothesis to the atlas. Then
   lem-a1-proper-etale-relation-finite-neighbourhood gives an affine étale neighbourhood,
   the residue-field isomorphism, a lift of u, and finite clopen object and relation pieces.
   Its full-restriction clause identifies the latter with the displayed kernel pair.
2. By lem-weil-pbc-finite-morphism-permanence the pieces finite over the affine base are
   affine. By lem-weil-pbc-finite-permanence-over-separated each restricted projection is
   finite. They remain étale, hence flat and locally finitely presented by
   def-weil-etale-morphism, and are finite locally free by def-pc-finite-locally-free.
3. Apply lem-a1-finite-flat-affine-relation-quotient over S. Its invariant-ring spectrum
   represents the fppf sheafification of the sectionwise restricted relation quotient.
   Descend the map to T' through this universal property, using that h_T' is a sheaf.
   Yoneda then supplies the quotient's T' structure and the required compatibility.
4. Compute the base-changed atlas and its kernel pair directly in presheaves.
   The original quotient universal property gives local surjectivity, which survives
   pullback; sheaf gluing along the kernel pair gives the base-changed quotient property.
   The clopen inclusion is étale by lem-weil-pbc-open-immersion-etale. Compare its full
   restricted kernel pair with the canonical restriction, and apply
   lem-trf-etale-relation-finding-opens to obtain the canonical open immersion.
5. The map from the affine quotient to affine T' is affine by
   lem-weil-pbc-morphism-affine-schemes-affine, hence quasi-affine via its identity open
   immersion. Apply lem-a1-etale-quasi-affine-image-scheme to get the represented open W
   whose point image equals the image of this quotient in X.
6. The residue-field point at u' maps to the quotient. Its image in X is the class of
   p(u): the lift maps to u, and extension of residue fields preserves the class by
   def-a1-algebraic-space-point-classes. Image equality therefore puts p(u) in W.
-/
theorem exists_closed_relation_schematic_neighbourhood
    {S : Scheme.{u}} (T : Over S) [IsAffine T.left]
    (X : AlgebraicSpace S) (f : X.obj.obj ⟶ yoneda.obj T)
    (hlocal : ∀ (H : Over S) (v : yoneda.obj H ⟶ X.obj.obj) (c : H ⟶ T),
      IsEtale v → yoneda.map c = v ≫ f → Scheme.Hom.IsLocallyQuasiFinite c.left)
    (hdiag : IsRepresentableWith (fun _ _ m ↦ IsClosedImmersion m.left)
      (Limits.pullback.diagonal f))
    (U R : Over S) [IsAffine U.left] [IsAffine R.left]
    (p : yoneda.obj U ⟶ X.obj.obj) (hp : IsEtale p) (hpsur : IsSurjective p)
    (b : U ⟶ T) (hb : yoneda.map b = p ≫ f) (s t : R ⟶ U)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) p p)
    (j : R ⟶ Limits.pullback b b)
    (hjs : j ≫ Limits.pullback.fst b b = s) (hjt : j ≫ Limits.pullback.snd b b = t)
    (hj : IsClosedImmersion j.left)
    (η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ X.obj.obj)
    (hηp : coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η = p)
    (hη : ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun k : X.obj.obj ⟶ G.obj ↦ η ≫ k))
    (u₀ : U.left) :
    ∃ (T' : Over S) (a : T' ⟶ T) (q' : T'.left),
      IsAffine T'.left ∧ Etale a.left ∧ a.left q' = b.left u₀ ∧
      IsIso (a.left.residueFieldMap q') ∧
      ∃ (U' A : Over S) (g : U' ⟶ Limits.pullback b a) (gA : A ⟶ Limits.pullback b a),
        IsOpenImmersion g.left ∧ IsOpenImmersion gA.left ∧
        IsCompl (Set.range fun y : U'.left ↦ g.left y)
          (Set.range fun y : A.left ↦ gA.left y) ∧
        ∃ u' : U'.left,
          (g ≫ Limits.pullback.fst b a).left u' = u₀ ∧
          (g ≫ Limits.pullback.snd b a).left u' = q' ∧
          IsFinite (g ≫ Limits.pullback.snd b a).left ∧ IsAffine U'.left ∧
          ∃ (R' B : Over S) (k : R' ⟶ Limits.pullback (s ≫ b) a)
            (kB : B ⟶ Limits.pullback (s ≫ b) a),
            IsOpenImmersion k.left ∧ IsOpenImmersion kB.left ∧
            IsCompl (Set.range fun y : R'.left ↦ k.left y)
              (Set.range fun y : B.left ↦ kB.left y) ∧
            IsFinite (k ≫ Limits.pullback.snd (s ≫ b) a).left ∧ IsAffine R'.left ∧
            ∃ (s' t' : R' ⟶ U'),
              k ≫ Limits.pullback.fst (s ≫ b) a ≫ s = s' ≫ g ≫ Limits.pullback.fst b a ∧
              k ≫ Limits.pullback.fst (s ≫ b) a ≫ t = t' ≫ g ≫ Limits.pullback.fst b a ∧
              k ≫ Limits.pullback.snd (s ≫ b) a = s' ≫ g ≫ Limits.pullback.snd b a ∧
              s'.left.IsFiniteLocallyFree ∧ t'.left.IsFiniteLocallyFree ∧
              Etale s'.left ∧ Etale t'.left ∧
              ∃ (Q : Over S) (c : Q ⟶ T') (e : U' ⟶ Q)
                (z : yoneda.obj Q ⟶ Limits.pullback f (yoneda.map a)),
                IsAffine Q.left ∧ e ≫ c = g ≫ Limits.pullback.snd b a ∧
                yoneda.map e ≫ z ≫ Limits.pullback.fst f (yoneda.map a) =
                  yoneda.map (g ≫ Limits.pullback.fst b a) ≫ p ∧
                z ≫ Limits.pullback.snd f (yoneda.map a) = yoneda.map c ∧
                IsPullback (yoneda.map s') (yoneda.map t')
                  (yoneda.map e ≫ z) (yoneda.map e ≫ z) ∧
                Presheaf.IsSheaf (Scheme.fppfTopology.over S) (yoneda.obj Q) ∧
                (∃ η' : coequalizer (yoneda.map s') (yoneda.map t') ⟶ yoneda.obj Q,
                  coequalizer.π (yoneda.map s') (yoneda.map t') ≫ η' = yoneda.map e ∧
                  ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
                    Function.Bijective (fun l : yoneda.obj Q ⟶ G.obj ↦ η' ≫ l)) ∧
                IsRepresentableWith (fun _ _ m ↦ IsOpenImmersion m.left) z ∧
                ∃ (W : OpenSubspace X) (Z : Over S) (eW : yoneda.obj Z ≅ W.val.toFunctor),
                  Set.range (schemePointMap (z ≫ Limits.pullback.fst f (yoneda.map a))) =
                    Set.range (schemePointMap (eW.hom ≫ W.val.ι)) ∧
                  schemePointMap p u₀ ∈ Set.range (schemePointMap (eW.hom ≫ W.val.ι))  := by
  classical
  obtain ⟨hmono, hrel, hs, hssur, ht, htsur, _⟩ :=
    etale_atlas_presentation X U p hp hpsur R s t hR X.obj η hη
  have hst : s ≫ b = t ≫ b := by
    apply yoneda.map_injective
    simpa only [Functor.map_comp, hb, Category.assoc] using congrArg (· ≫ f) hR.w
  have hstl : s.left ≫ b.left = t.left ≫ b.left := congrArg Over.Hom.left hst
  let jS : R.left ⟶ Limits.pullback b.left b.left :=
    pullback.lift s.left t.left hstl
  have hpb := (IsPullback.of_hasPullback b b).map (Over.forget S)
  have hjS : jS = j.left ≫ hpb.isoPullback.hom := by
    apply pullback.hom_ext <;> simp [jS, ← Over.comp_left, hjs, hjt]
  have : IsClosedImmersion jS := by
    rw [hjS]
    exact inferInstance
  have hrelS : ∀ (H : Scheme.{u}) (hH : H ⟶ T.left),
      Equivalence (fun (a b' : {g : H ⟶ U.left // g ≫ b.left = hH}) ↦
        ∃ r : H ⟶ R.left, r ≫ s.left = a.1 ∧ r ≫ t.left = b'.1) := by
    intro H hH
    let Hs : Over S := Over.mk (hH ≫ T.hom)
    let liftU (a : {g : H ⟶ U.left // g ≫ b.left = hH}) : Hs ⟶ U :=
      Over.homMk a.1 (by rw [← b.w, ← Category.assoc, a.2]; rfl)
    have hiff (a b' : {g : H ⟶ U.left // g ≫ b.left = hH}) :
        (∃ r : H ⟶ R.left, r ≫ s.left = a.1 ∧ r ≫ t.left = b'.1) ↔
          p.app (Opposite.op Hs) (liftU a) = p.app (Opposite.op Hs) (liftU b') := by
      rw [← (hrel Hs).2]
      constructor
      · rintro ⟨r, hrs, hrt⟩
        refine ⟨Over.homMk r ?_, ?_, ?_⟩
        · rw [← s.w, ← Category.assoc, hrs]
          exact (liftU a).w
        · exact Over.OverMorphism.ext hrs
        · exact Over.OverMorphism.ext hrt
      · rintro ⟨r, hrs, hrt⟩
        exact ⟨r.left, congrArg Over.Hom.left hrs, congrArg Over.Hom.left hrt⟩
    exact ⟨fun a ↦ (hiff a a).mpr rfl,
      fun hab ↦ (hiff _ _).mpr ((hiff _ _).mp hab).symm,
      fun hab hbc ↦ (hiff _ _).mpr (((hiff _ _).mp hab).trans ((hiff _ _).mp hbc))⟩
  obtain ⟨T₁, a₁, q₁, hT₁, ha₁, hq₁, hk₁, Uo, Ao, hUA, u₁, hu₁, huq,
    hUfin, Ro, Bo, hRB, hRfin, q, hqiso, hqk, hqs, hqt, hs₁, ht₁, hrel₁⟩ :=
    exists_finite_etale_restricted_relation_neighbourhood b.left (s.left ≫ b.left)
      (hlocal U p b hp hb) s.left t.left rfl hstl.symm hs ht jS
      (by simp [jS]) (by simp [jS]) inferInstance hrelS u₀
  let T' : Over S := Over.mk (a₁ ≫ T.hom)
  let a : T' ⟶ T := Over.homMk a₁ rfl
  have eu : IsPullback (Limits.pullback.fst b a).left
      (Limits.pullback.snd b a).left b.left a₁ :=
    (IsPullback.of_hasPullback b a).map (Over.forget S)
  have er : IsPullback (Limits.pullback.fst (s ≫ b) a).left
      (Limits.pullback.snd (s ≫ b) a).left (s.left ≫ b.left) a₁ :=
    (IsPullback.of_hasPullback (s ≫ b) a).map (Over.forget S)
  let gS := Uo.ι ≫ eu.isoPullback.inv
  let gAS := Ao.ι ≫ eu.isoPullback.inv
  let U' : Over S := Over.mk (gS ≫ (Limits.pullback b a).hom)
  let A : Over S := Over.mk (gAS ≫ (Limits.pullback b a).hom)
  let g : U' ⟶ Limits.pullback b a := Over.homMk gS rfl
  let gA : A ⟶ Limits.pullback b a := Over.homMk gAS rfl
  let kS := Ro.ι ≫ er.isoPullback.inv
  let kBS := Bo.ι ≫ er.isoPullback.inv
  let R' : Over S := Over.mk (kS ≫ (Limits.pullback (s ≫ b) a).hom)
  let B : Over S := Over.mk (kBS ≫ (Limits.pullback (s ≫ b) a).hom)
  let k : R' ⟶ Limits.pullback (s ≫ b) a := Over.homMk kS rfl
  let kB : B ⟶ Limits.pullback (s ≫ b) a := Over.homMk kBS rfl
  have hgs : (g ≫ Limits.pullback.fst b a).left =
      Uo.ι ≫ Limits.pullback.fst b.left a₁ := by
    change (Uo.ι ≫ eu.isoPullback.inv) ≫ _ = _
    rw [Category.assoc, eu.isoPullback_inv_fst]
  have hgb : (g ≫ Limits.pullback.snd b a).left =
      Uo.ι ≫ Limits.pullback.snd b.left a₁ := by
    change (Uo.ι ≫ eu.isoPullback.inv) ≫ _ = _
    rw [Category.assoc, eu.isoPullback_inv_snd]
  have hks : (k ≫ Limits.pullback.fst (s ≫ b) a).left =
      Ro.ι ≫ Limits.pullback.fst (s.left ≫ b.left) a₁ := by
    change (Ro.ι ≫ er.isoPullback.inv) ≫ _ = _
    rw [Category.assoc, er.isoPullback_inv_fst]
  have hkb : (k ≫ Limits.pullback.snd (s ≫ b) a).left =
      Ro.ι ≫ Limits.pullback.snd (s.left ≫ b.left) a₁ := by
    change (Ro.ι ≫ er.isoPullback.inv) ≫ _ = _
    rw [Category.assoc, er.isoPullback_inv_snd]
  have hg : IsOpenImmersion g.left := by
    change IsOpenImmersion (Uo.ι ≫ eu.isoPullback.inv)
    infer_instance
  have hgA : IsOpenImmersion gA.left := by
    change IsOpenImmersion (Ao.ι ≫ eu.isoPullback.inv)
    infer_instance
  have hk : IsOpenImmersion k.left := by
    change IsOpenImmersion (Ro.ι ≫ er.isoPullback.inv)
    infer_instance
  have hkB : IsOpenImmersion kB.left := by
    change IsOpenImmersion (Bo.ι ≫ er.isoPullback.inv)
    infer_instance
  have hUfin' : IsFinite (g ≫ Limits.pullback.snd b a).left := hgb ▸ hUfin
  have hRfin' : IsFinite (k ≫ Limits.pullback.snd (s ≫ b) a).left := hkb ▸ hRfin
  have : IsAffine T'.left := hT₁
  have : IsAffine U'.left := isAffine_of_isAffineHom (g ≫ Limits.pullback.snd b a).left
  have : IsAffine R'.left :=
    isAffine_of_isAffineHom (k ≫ Limits.pullback.snd (s ≫ b) a).left
  let s₀ : Limits.pullback (s.left ≫ b.left) a₁ ⟶ Limits.pullback b.left a₁ :=
    pullback.map _ _ _ _ s.left (𝟙 T₁) (𝟙 T.left) (by simp) (by simp)
  let t₀ : Limits.pullback (s.left ≫ b.left) a₁ ⟶ Limits.pullback b.left a₁ :=
    pullback.map _ _ _ _ t.left (𝟙 T₁) (𝟙 T.left) (by simpa using hstl) (by simp)
  let P₀ := Limits.pullback Uo.ι s₀
  let Q₀ := Limits.pullback (Limits.pullback.snd Uo.ι s₀ ≫ t₀) Uo.ι
  let sS : R'.left ⟶ U'.left :=
    q ≫ Limits.pullback.fst (Limits.pullback.snd Uo.ι s₀ ≫ t₀) Uo.ι ≫
      Limits.pullback.fst Uo.ι s₀
  let tS : R'.left ⟶ U'.left :=
    q ≫ Limits.pullback.snd (Limits.pullback.snd Uo.ι s₀ ≫ t₀) Uo.ι
  have hsS : Ro.ι ≫ s₀ = sS ≫ Uo.ι := hqs
  have htS : Ro.ι ≫ t₀ = tS ≫ Uo.ι := hqt
  have hsq : sS ≫ Uo.ι ≫ Limits.pullback.snd b.left a₁ =
      Ro.ι ≫ Limits.pullback.snd (s.left ≫ b.left) a₁ := by
    rw [← Category.assoc, ← hsS]
    simp [s₀]
  have htq : tS ≫ Uo.ι ≫ Limits.pullback.snd b.left a₁ =
      Ro.ι ≫ Limits.pullback.snd (s.left ≫ b.left) a₁ := by
    rw [← Category.assoc, ← htS]
    simp [t₀]
  let s' : R' ⟶ U' := Over.homMk sS (by
    rw [← (g ≫ Limits.pullback.snd b a).w,
      ← (k ≫ Limits.pullback.snd (s ≫ b) a).w]
    rw [hgb, hkb]
    simpa only [Category.assoc] using congrArg (· ≫ T'.hom) hsq)
  let t' : R' ⟶ U' := Over.homMk tS (by
    rw [← (g ≫ Limits.pullback.snd b a).w,
      ← (k ≫ Limits.pullback.snd (s ≫ b) a).w]
    rw [hgb, hkb]
    simpa only [Category.assoc] using congrArg (· ≫ T'.hom) htq)
  have hscomp : k ≫ Limits.pullback.fst (s ≫ b) a ≫ s =
      s' ≫ g ≫ Limits.pullback.fst b a := by
    apply Over.OverMorphism.ext
    change (k ≫ Limits.pullback.fst (s ≫ b) a).left ≫ s.left =
      sS ≫ (g ≫ Limits.pullback.fst b a).left
    rw [hks, hgs, ← Category.assoc, ← hsS]
    simp [s₀]
  have htcomp : k ≫ Limits.pullback.fst (s ≫ b) a ≫ t =
      t' ≫ g ≫ Limits.pullback.fst b a := by
    apply Over.OverMorphism.ext
    change (k ≫ Limits.pullback.fst (s ≫ b) a).left ≫ t.left =
      tS ≫ (g ≫ Limits.pullback.fst b a).left
    rw [hks, hgs, ← Category.assoc, ← htS]
    simp [t₀]
  have hsb : k ≫ Limits.pullback.snd (s ≫ b) a =
      s' ≫ g ≫ Limits.pullback.snd b a := by
    apply Over.OverMorphism.ext
    change (k ≫ Limits.pullback.snd (s ≫ b) a).left =
      sS ≫ (g ≫ Limits.pullback.snd b a).left
    rw [hkb, hgb, hsq]
  have htb : k ≫ Limits.pullback.snd (s ≫ b) a =
      t' ≫ g ≫ Limits.pullback.snd b a := by
    apply Over.OverMorphism.ext
    change (k ≫ Limits.pullback.snd (s ≫ b) a).left =
      tS ≫ (g ≫ Limits.pullback.snd b a).left
    rw [hkb, hgb, htq]
  have hs' : Etale s'.left := hs₁
  have ht' : Etale t'.left := ht₁
  have : IsFinite (s'.left ≫ (g ≫ Limits.pullback.snd b a).left) := by
    rw [← Over.comp_left, ← hsb]
    exact hRfin'
  have : IsFinite (t'.left ≫ (g ≫ Limits.pullback.snd b a).left) := by
    rw [← Over.comp_left, ← htb]
    exact hRfin'
  have : IsFinite s'.left := IsFinite.of_comp _ (g ≫ Limits.pullback.snd b a).left
  have : IsFinite t'.left := IsFinite.of_comp _ (g ≫ Limits.pullback.snd b a).left
  have hsfree : s'.left.IsFiniteLocallyFree := ⟨⟩
  have htfree : t'.left.IsFiniteLocallyFree := ⟨⟩
  let p₀ : yoneda.obj (Limits.pullback b a) ⟶ Limits.pullback f (yoneda.map a) :=
    Limits.pullback.lift (yoneda.map (Limits.pullback.fst b a) ≫ p)
      (yoneda.map (Limits.pullback.snd b a)) (by
        rw [Category.assoc, ← hb, ← Functor.map_comp, ← Functor.map_comp,
          pullback.condition])
  have hp₀ : IsPullback (yoneda.map (Limits.pullback.fst b a)) p₀ p
      (Limits.pullback.fst f (yoneda.map a)) := by
    have h := (IsPullback.of_hasPullback b a).map yoneda
    have h' : IsPullback (yoneda.map (Limits.pullback.fst b a))
        (yoneda.map (Limits.pullback.snd b a)) (p ≫ f) (yoneda.map a) := by
      simpa only [hb] using h
    have h'' : IsPullback (yoneda.map (Limits.pullback.fst b a))
        (p₀ ≫ pullback.snd f (yoneda.map a)) (p ≫ f) (yoneda.map a) := by
      simpa [p₀] using h'
    exact h''.of_bot (by simp [p₀]) (IsPullback.of_hasPullback f (yoneda.map a))
  let u : U' ⟶ U := g ≫ pullback.fst b a
  let d : U' ⟶ T' := g ≫ pullback.snd b a
  have hw : yoneda.map u ≫ p ≫ f = yoneda.map d ≫ yoneda.map a := by
    rw [← hb, ← yoneda.map_comp, ← yoneda.map_comp]
    exact congrArg yoneda.map (by simp [u, d, pullback.condition])
  let v : yoneda.obj U' ⟶ Limits.pullback f (yoneda.map a) :=
    pullback.lift (yoneda.map u ≫ p) (yoneda.map d) hw
  have hvfst : v ≫ pullback.fst f (yoneda.map a) = yoneda.map u ≫ p := by simp [v]
  have hvsnd : v ≫ pullback.snd f (yoneda.map a) = yoneda.map d := by simp [v]
  have hsv : yoneda.map s' ≫ v = yoneda.map t' ≫ v := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hvfst]
      have hsu : s' ≫ u = k ≫ pullback.fst (s ≫ b) a ≫ s := hscomp.symm
      have htu : t' ≫ u = k ≫ pullback.fst (s ≫ b) a ≫ t := htcomp.symm
      rw [← Functor.map_comp_assoc, hsu, ← Functor.map_comp_assoc, htu]
      simp only [Functor.map_comp, Category.assoc, hR.w]
    · simp only [Category.assoc, hvsnd, ← yoneda.map_comp]
      exact congrArg yoneda.map (hsb.symm.trans htb)
  have hfull : IsPullback (yoneda.map s') (yoneda.map t') v v := by
    apply IsPullback.of_forall_isPullback_app
    intro H
    apply (Types.isPullback_iff _ _ _ _).mpr
    refine ⟨congrArg (fun z ↦ z.app H) hsv, ?_, ?_⟩
    · intro x y h
      have hxs : x ≫ s' = y ≫ s' := h.1
      have hxt : x ≫ t' = y ≫ t' := h.2
      have : Mono k := Over.mono_of_mono_left k
      apply (cancel_mono k).mp
      apply pullback.hom_ext
      · apply (cancel_mono (prod.lift s t)).mp
        apply prod.hom_ext
        · simpa only [Category.assoc, prod.lift_fst, hscomp] using hxs =≫ g ≫ pullback.fst b a
        · simpa only [Category.assoc, prod.lift_snd, htcomp] using hxt =≫ g ≫ pullback.fst b a
      · simpa only [Category.assoc, hsb] using hxs =≫ g ≫ pullback.snd b a
    · intro x y hxy
      have hxyfst : p.app H (x ≫ u) = p.app H (y ≫ u) := by
        have h := congrArg (fun z ↦ (pullback.fst f (yoneda.map a)).app H z) hxy
        change (v ≫ pullback.fst f (yoneda.map a)).app H x =
          (v ≫ pullback.fst f (yoneda.map a)).app H y at h
        rw [hvfst] at h
        exact h
      obtain ⟨r, hrs, hrt⟩ := Types.exists_of_isPullback (hR.app H) (x ≫ u) (y ≫ u) hxyfst
      have hxyd : x ≫ d = y ≫ d := by
        have h := congrArg (fun z ↦ (pullback.snd f (yoneda.map a)).app H z) hxy
        change (v ≫ pullback.snd f (yoneda.map a)).app H x =
          (v ≫ pullback.snd f (yoneda.map a)).app H y at h
        rw [hvsnd] at h
        exact h
      change r ≫ s = x ≫ u at hrs
      change r ≫ t = y ≫ u at hrt
      let r₀ : H.unop ⟶ Limits.pullback (s ≫ b) a :=
        pullback.lift r (x ≫ d) (by
          rw [← Category.assoc, hrs]
          simp [u, d, pullback.condition])
      let rf := r₀.left ≫ er.isoPullback.hom
      have hrf₁ : rf ≫ pullback.fst (s.left ≫ b.left) a₁ = r.left := by
        simp only [rf, Category.assoc, er.isoPullback_hom_fst]
        exact congrArg Over.Hom.left (pullback.lift_fst r (x ≫ d) _)
      have hrf₂ : rf ≫ pullback.snd (s.left ≫ b.left) a₁ = (x ≫ d).left := by
        simp only [rf, Category.assoc, er.isoPullback_hom_snd]
        exact congrArg Over.Hom.left (pullback.lift_snd r (x ≫ d) _)
      have hxs : x.left ≫ Uo.ι = rf ≫ s₀ := by
        apply pullback.hom_ext
        · simp only [Category.assoc, s₀, pullback.map, pullback.lift_fst]
          rw [← Category.assoc rf, hrf₁]
          rw [← hgs]
          exact (congrArg (fun z ↦ z.left) hrs).symm
        · simp only [Category.assoc, s₀, pullback.map, pullback.lift_snd, Category.comp_id]
          rw [hrf₂]
          exact (congrArg (fun z ↦ z.left) (show x ≫ d = x ≫ d from rfl)).trans
            (by rw [Over.comp_left, hgb]) |>.symm
      have hyt : y.left ≫ Uo.ι = rf ≫ t₀ := by
        apply pullback.hom_ext
        · simp only [Category.assoc, t₀, pullback.map, pullback.lift_fst]
          rw [← Category.assoc rf, hrf₁]
          rw [← hgs]
          exact (congrArg (fun z ↦ z.left) hrt).symm
        · simp only [Category.assoc, t₀, pullback.map, pullback.lift_snd, Category.comp_id]
          rw [hrf₂, congrArg (fun z ↦ z.left) hxyd, Over.comp_left, hgb]
      let l : H.unop.left ⟶ P₀ := pullback.lift x.left rf hxs
      let m : H.unop.left ⟶ Q₀ := pullback.lift l y.left (by
        simpa [l] using hyt.symm)
      let rr := m ≫ inv q
      have hrrs : rr ≫ sS = x.left := by simp [rr, sS, m, l]
      have hrrt : rr ≫ tS = y.left := by simp [rr, tS, m]
      let r' : H.unop ⟶ R' := Over.homMk rr (by
        rw [← Over.w s', ← Category.assoc]
        change (rr ≫ sS) ≫ U'.hom = _
        rw [hrrs]
        exact Over.w x)
      exact ⟨r', Over.OverMorphism.ext hrrs, Over.OverMorphism.ext hrrt⟩
  have hmon : Mono (prod.lift s' t') := by
    constructor
    intro H x y hxy
    apply yoneda.map_injective
    apply hfull.hom_ext
    · simpa only [← yoneda.map_comp, Category.assoc, prod.lift_fst] using
        congrArg yoneda.map (congrArg (fun z ↦ z ≫ prod.fst) hxy)
    · simpa only [← yoneda.map_comp, Category.assoc, prod.lift_snd] using
        congrArg yoneda.map (congrArg (fun z ↦ z ≫ prod.snd) hxy)
  let := hmon
  have hrel' : ∀ H : Over S, Equivalence (fun x y : H ⟶ U' ↦
      ∃ r : H ⟶ R', r ≫ s' = x ∧ r ≫ t' = y) := by
    intro H
    have heq (x y : H ⟶ U') :
        (∃ r : H ⟶ R', r ≫ s' = x ∧ r ≫ t' = y) ↔
          v.app (Opposite.op H) x = v.app (Opposite.op H) y := by
      constructor
      · rintro ⟨r, rfl, rfl⟩
        exact congrArg (fun z ↦ z.app (Opposite.op H) r) hsv
      · intro h
        exact Types.exists_of_isPullback (hfull.app (Opposite.op H)) x y h
    exact ⟨fun x ↦ (heq x x).mpr rfl,
      fun h ↦ (heq _ _).mpr ((heq _ _).mp h).symm,
      fun h h' ↦ (heq _ _).mpr (((heq _ _).mp h).trans ((heq _ _).mp h'))⟩
  let := hsfree
  let := htfree
  obtain ⟨Q, e, hQa, hefl, hesur, hQsh, η', hη'e, hη'⟩ :=
    affine_quotient U' R' s' t' hrel'
  let := hQa
  let Qsh : Sheaf (Scheme.fppfTopology.over S) (Type u) := ⟨yoneda.obj Q, hQsh⟩
  have hdrel : yoneda.map s' ≫ yoneda.map d = yoneda.map t' ≫ yoneda.map d := by
    simp only [← yoneda.map_comp]
    exact congrArg yoneda.map (hsb.symm.trans htb)
  let Dsh : Sheaf (Scheme.fppfTopology.over S) (Type u) :=
    ⟨yoneda.obj T', (isSheaf_iff_isSheaf_of_type _ _).mpr
      (CategoryTheory.GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)⟩
  let dc := coequalizer.desc (yoneda.map d) hdrel
  obtain ⟨cc, hcc⟩ := (hη' Dsh).surjective dc
  change η' ≫ cc = dc at hcc
  let c : Q ⟶ T' := Yoneda.fullyFaithful.preimage cc
  have hc : yoneda.map c = cc := Yoneda.fullyFaithful.map_preimage cc
  have hec : e ≫ c = d := by
    apply yoneda.map_injective
    rw [yoneda.map_comp, hc, ← hη'e, Category.assoc, hcc]
    exact coequalizer.π_desc _ _
  have hup : yoneda.map s' ≫ (yoneda.map u ≫ p) =
      yoneda.map t' ≫ (yoneda.map u ≫ p) := by
    simpa only [Category.assoc, hvfst] using hsv =≫ pullback.fst f (yoneda.map a)
  let up := coequalizer.desc (yoneda.map u ≫ p) hup
  obtain ⟨α, hα⟩ := (hη' X.obj).surjective up
  change η' ≫ α = up at hα
  have heα : yoneda.map e ≫ α = yoneda.map u ≫ p := by
    rw [← hη'e, Category.assoc, hα]
    exact coequalizer.π_desc _ _
  have hαf : α ≫ f = yoneda.map c ≫ yoneda.map a := by
    apply (hη' ⟨yoneda.obj T, (isSheaf_iff_isSheaf_of_type _ _).mpr
      (CategoryTheory.GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)⟩).injective
    apply coequalizer.hom_ext
    simp only [← Category.assoc, hη'e, heα]
    rw [Category.assoc, hw, ← yoneda.map_comp e c, hec]
  let z : yoneda.obj Q ⟶ Limits.pullback f (yoneda.map a) :=
    pullback.lift α (yoneda.map c) hαf
  have hez : yoneda.map e ≫ z = v := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, z, pullback.lift_fst, hvfst] using heα
    · simp only [Category.assoc, z, pullback.lift_snd, hvsnd,
        ← yoneda.map_comp, hec]
  let S₀ : Limits.pullback (s ≫ b) a ⟶ Limits.pullback b a :=
    pullback.lift (pullback.fst (s ≫ b) a ≫ s) (pullback.snd (s ≫ b) a)
      (by simp [pullback.condition])
  let T₀ : Limits.pullback (s ≫ b) a ⟶ Limits.pullback b a :=
    pullback.lift (pullback.fst (s ≫ b) a ≫ t) (pullback.snd (s ≫ b) a)
      (by simp [← hst, pullback.condition])
  have hkp₀ := basechange_kernel_pair p f s t hR b a S₀ T₀
    (by simp [S₀]) (by simp [T₀]) (by simp [S₀]) (by simp [T₀]) p₀
    (by simp [p₀]) (by simp [p₀])
  have hplocal : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) p := by
    have := universal_locally_surjective _ _ X.obj η hη
    have : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
        (coequalizer.π (yoneda.map s) (yoneda.map t)) := by
      apply Presheaf.isLocallySurjective_of_surjective
      intro H
      exact (epi_iff_surjective _).mp inferInstance
    rw [← hηp]
    infer_instance
  have hp₀local := locally_surjective_of_square (Scheme.fppfTopology.over S) hp₀
  obtain ⟨η₀, hη₀p, hη₀⟩ := kernel_pair_universal
    (Scheme.fppfTopology.over S) (yoneda.map S₀) (yoneda.map T₀) p₀ hkp₀
  let F₀ : Sheaf (Scheme.fppfTopology.over S) (Type u) :=
    ⟨Limits.pullback f (yoneda.map a), by
      apply ObjectProperty.prop_limit
        (Presheaf.IsSheaf (Scheme.fppfTopology.over S)) (cospan f (yoneda.map a))
      rintro (_ | _ | _)
      · change Presheaf.IsSheaf (Scheme.fppfTopology.over S) (yoneda.obj T)
        exact (isSheaf_iff_isSheaf_of_type _ _).mpr
          (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)
      · exact X.obj.property
      · change Presheaf.IsSheaf (Scheme.fppfTopology.over S) (yoneda.obj T')
        exact (isSheaf_iff_isSheaf_of_type _ _).mpr
          (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)⟩
  have hp₀et : IsEtale p₀ := representable_of_square _ hp₀ hp
  have hp₀sur : IsSurjective p₀ := representable_of_square _ hp₀ hpsur
  have : Etale S₀.left := property_of_square _ p₀ hp₀et S₀
    (yoneda.map T₀) hkp₀.flip
  have : Etale T₀.left := property_of_square _ p₀ hp₀et T₀
    (yoneda.map S₀) hkp₀
  have : Surjective S₀.left := property_of_square _ p₀ hp₀sur S₀
    (yoneda.map T₀) hkp₀.flip
  have : Surjective T₀.left := property_of_square _ p₀ hp₀sur T₀
    (yoneda.map S₀) hkp₀
  have hmono₀ : Mono (prod.lift S₀ T₀) := by
    constructor
    intro H x y h
    apply yoneda.map_injective
    apply hkp₀.hom_ext
    · simpa using congrArg yoneda.map (h =≫ prod.fst)
    · simpa using congrArg yoneda.map (h =≫ prod.snd)
  have hrel₀ (H : Over S) : Equivalence (fun x y : H ⟶ Limits.pullback b a ↦
      ∃ r : H ⟶ Limits.pullback (s ≫ b) a, r ≫ S₀ = x ∧ r ≫ T₀ = y) := by
    have hi (x y : H ⟶ Limits.pullback b a) :
        (∃ r : H ⟶ Limits.pullback (s ≫ b) a, r ≫ S₀ = x ∧ r ≫ T₀ = y) ↔
        p₀.app (Opposite.op H) x = p₀.app (Opposite.op H) y := by
      constructor
      · rintro ⟨r, rfl, rfl⟩
        exact ConcreteCategory.congr_hom (NatTrans.congr_app hkp₀.w (Opposite.op H)) r
      · exact Types.exists_of_isPullback (hkp₀.app (Opposite.op H)) x y
    exact ⟨fun x ↦ (hi x x).mpr rfl,
      fun h ↦ (hi _ _).mpr ((hi _ _).mp h).symm,
      fun h h' ↦ (hi _ _).mpr (((hi _ _).mp h).trans ((hi _ _).mp h'))⟩
  let ds := pullback.fst (pullback.snd g S₀ ≫ T₀) g ≫ pullback.fst g S₀
  let dt := pullback.snd (pullback.snd g S₀ ≫ T₀) g
  have hcan := restricted_kernel_pair S₀ T₀ p₀ hkp₀ g
  have hv : yoneda.map g ≫ p₀ = v := by
    apply pullback.hom_ext <;> simp [p₀, v, u, d, Functor.map_comp]
  rw [hv] at hcan
  let erel := hcan.isoIsPullback _ _ hfull
  let δ := HasColimit.isoOfNatIso (parallelPairIso (yoneda.map ds) (yoneda.map dt)
    (yoneda.map s') (yoneda.map t') erel (Iso.refl _)
    (by simp [ds, erel]) (by simp [dt, erel]))
  let ηcan := δ.hom ≫ η'
  have hηcan (G : Sheaf (Scheme.fppfTopology.over S) (Type u)) :
      Function.Bijective (fun l : yoneda.obj Q ⟶ G.obj ↦ ηcan ≫ l) := by
    constructor
    · intro l l' h
      exact (hη' G).injective ((cancel_epi δ.hom).mp h)
    · intro l
      obtain ⟨k, hk⟩ := (hη' G).surjective (δ.inv ≫ l)
      exact ⟨k, by simp [ηcan, hk]⟩
  obtain ⟨z₀, hz₀, hopen₀⟩ := etale_relation_finding_opens S₀ T₀ hrel₀ g
    F₀ η₀ hη₀ Qsh ηcan hηcan
  have hzc : z₀ = z := by
    apply (hη' F₀).injective
    apply coequalizer.hom_ext
    have hπ : coequalizer.π (yoneda.map ds) (yoneda.map dt) ≫ δ.hom =
        coequalizer.π (yoneda.map s') (yoneda.map t') := by
      change _ ≫ (HasColimit.isoOfNatIso _).hom = _
      rw [HasColimit.isoOfNatIso_ι_hom]
      rfl
    have hh := hz₀
    change (coequalizer.π (yoneda.map ds) (yoneda.map dt) ≫ ηcan) ≫ z₀ = _ at hh
    simpa only [ηcan, ← Category.assoc, hπ, hη'e, hη₀p, hv, hez] using hh
  have hopen : IsRepresentableWith (fun _ _ m ↦ IsOpenImmersion m.left) z :=
    hzc ▸ hopen₀
  have : Etale a.left := ha₁
  obtain ⟨W, Z, eW, hW⟩ := schematic_image_of_affine_open T T' a X f hlocal hdiag
    Q c z (by simp [z]) hopen
  refine ⟨T', a, q₁, hT₁, ha₁, hq₁, hk₁, U', A, g, gA, hg, hgA,
    isCompl_ranges_of_iso eu.isoPullback.symm Uo Ao hUA, u₁, ?_, ?_, hUfin',
    inferInstance, R', B, k, kB, hk, hkB,
    isCompl_ranges_of_iso er.isoPullback.symm Ro Bo hRB, hRfin', inferInstance,
    s', t', hscomp, htcomp, hsb, hsfree, htfree, hs', ht', Q, c, e, z,
    hQa, hec, ?_, ?_, ?_, hQsh, ⟨η', hη'e, hη'⟩, hopen, W, Z, eW, hW, ?_⟩
  · rw [hgs]
    exact hu₁
  · rw [hgb]
    exact huq
  · simpa only [Category.assoc, z, pullback.lift_fst] using heα
  · simp [z]
  · simpa only [hez] using hfull
  · rw [← hW]
    refine ⟨e.left u₁, ?_⟩
    rw [← schemePointMap_comp e, ← Category.assoc, hez, hvfst,
      schemePointMap_comp u]
    congr 1
    change (g ≫ pullback.fst b a).left u₁ = u₀
    rw [hgs]
    exact hu₁

end AlgebraicGeometry.AlgebraicSpace
