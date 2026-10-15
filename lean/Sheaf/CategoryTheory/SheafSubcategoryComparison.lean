/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.IndexedCoveringClass
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Canonical
import Sheaf.CategoryTheory.SmallSetOfCoveringFamilies
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology

/-!
# A generating subcategory of sheaves presents the topos

Source: Stacks Project, Sites, Tag 03A1, and Sets, Tag 000X
(blueprint: lem-weil-pbc-sheaf-subcategory-comparison).
-/

@[expose] public section

universe u v w

open CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Epimorphic indexed families in a subcategory of sheaves, expressed by joint right
cancellation. This is precisely epimorphy of the map from the coproduct, by its universal
property, without choosing that coproduct or restricting its index size.
Source: Sites, Tag 03A1 (blueprint: lem-weil-pbc-sheaf-subcategory-comparison). -/
def sheafSubcategoryEpimorphicFamilies {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) :
    Set (Σ A : E, PreZeroHypercover.{max u v w} A) :=
  {p | ∀ (B : Sheaf J (Type u)) (f g : F.obj p.1 ⟶ B),
    (∀ i, F.map (p.2.f i) ≫ f = F.map (p.2.f i) ≫ g) → f = g}

/-- The restricted Yoneda presheaf functor, with restriction maps given by precomposition
and functoriality in the sheaf by postcomposition.
Source: Sites, Tag 03A1, Hom calculation in the proof of (5)
(blueprint: lem-weil-pbc-sheaf-subcategory-comparison). -/
def sheafSubcategoryNerve {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) : Sheaf J (Type u) ⥤ Eᵒᵖ ⥤ Type u :=
  yoneda ⋙ (Functor.whiskeringLeft Eᵒᵖ (Sheaf J (Type u))ᵒᵖ (Type u)).obj F.op

-- Local lifting is detected by the sheaf closure of the sectionwise image.
private def familyImage {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) (A : E)
    (R : PreZeroHypercover.{max u v w} A) : Subfunctor (F.obj A).obj where
  obj U := {a | ∃ (i : R.I₀) (b : (F.obj (R.X i)).obj.obj U),
    (F.map (R.f i)).hom.app U b = a}
  map := by
    intro U V f a ha
    obtain ⟨i, b, rfl⟩ := ha
    exact ⟨i, (F.obj (R.X i)).obj.map f b,
      (NatTrans.naturality_apply (F.map (R.f i)).hom f b)⟩

private theorem familyImage_sieve {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) (A : E)
    (R : PreZeroHypercover.{max u v w} A) (U : C) (a : (F.obj A).obj.obj (op U)) :
    Sieve.generate (fun (V : C) (f : V ⟶ U) ↦
      ∃ (i : R.I₀) (b : (F.obj (R.X i)).obj.obj (op V)),
        (F.map (R.f i)).hom.app (op V) b = (F.obj A).obj.map f.op a) =
      (familyImage F A R).sieveOfSection a := by
  apply le_antisymm
  · exact (Sieve.generate_le_iff _ _).mpr (fun V f hf ↦ hf)
  · exact Sieve.le_generate _

private theorem family_epi_iff_local {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) (A : E)
    (R : PreZeroHypercover.{max u v w} A) :
    (⟨A, R⟩ ∈ sheafSubcategoryEpimorphicFamilies F ↔
      ∀ (U : C) (a : (F.obj A).obj.obj (op U)),
        Sieve.generate (fun (V : C) (f : V ⟶ U) ↦
          ∃ (i : R.I₀) (b : (F.obj (R.X i)).obj.obj (op V)),
            (F.map (R.f i)).hom.app (op V) b = (F.obj A).obj.map f.op a) ∈ J U) := by
  conv_rhs =>
    intro U a
    rw [familyImage_sieve F A R U a]
  constructor
  · intro hepi
    let S := familyImage F A R
    have hA : Presieve.IsSheaf J (F.obj A).obj :=
      (isSheaf_iff_isSheaf_of_type _ _).mp (F.obj A).property
    let G : Sheaf J (Type u) := ⟨(S.sheafify J).toFunctor,
      (isSheaf_iff_isSheaf_of_type _ _).mpr (S.sheafify_isSheaf hA)⟩
    let inc : G ⟶ F.obj A := ⟨(S.sheafify J).ι⟩
    have hi : ∀ i, ∃ t : F.obj (R.X i) ⟶ G, t ≫ inc = F.map (R.f i) := by
      intro i
      refine ⟨⟨{
        app := fun U ↦ ↾fun b ↦
          ⟨(F.map (R.f i)).hom.app U b, S.le_sheafify J U ⟨i, b, rfl⟩⟩
        naturality := ?_ }⟩, ?_⟩
      · intro U V f
        ext b
        apply Subtype.ext
        exact (NatTrans.naturality_apply (F.map (R.f i)).hom f b)
      · rfl
    have : Epi inc := ⟨by
      intro B f g h
      apply hepi B f g
      intro i
      obtain ⟨t, ht⟩ := hi i
      rw [← ht, Category.assoc, Category.assoc, h]⟩
    have : Mono inc := (sheafToPresheaf J _).mono_of_mono_map (by
      change Mono (S.sheafify J).ι
      infer_instance)
    have : IsIso inc := isIso_of_mono_of_epi inc
    have : IsIso inc.hom := (sheafToPresheaf J _).map_isIso inc
    have htop : S.sheafify J = ⊤ :=
      (Subfunctor.eq_top_iff_isIso _).mpr (inferInstanceAs (IsIso inc.hom))
    intro U a
    change a ∈ (S.sheafify J).obj (op U)
    rw [htop]
    trivial
  · intro hlocal B f g hfg
    ext U a
    apply (((isSheaf_iff_isSheaf_of_type _ _).mp B.property).isSeparated _
      (hlocal U.unop a)).ext
    intro V t ht
    obtain ⟨i, b, hb⟩ := ht
    have h := congrArg (fun q : F.obj (R.X i) ⟶ B ↦ q.hom.app (op V) b) (hfg i)
    change f.hom.app (op V) ((F.map (R.f i)).hom.app (op V) b) =
      g.hom.app (op V) ((F.map (R.f i)).hom.app (op V) b) at h
    rw [hb] at h
    exact (f.hom.naturality_apply t.op a).symm.trans
      (h.trans (g.hom.naturality_apply t.op a))

private theorem family_epi_pullback {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) (A B : E)
    (R : PreZeroHypercover.{max u v w} A)
    (hR : ⟨A, R⟩ ∈ sheafSubcategoryEpimorphicFamilies F)
    (f : B ⟶ A) (P : R.I₀ → E) (p : ∀ i, P i ⟶ B) (q : ∀ i, P i ⟶ R.X i)
    (hp : ∀ i, IsPullback (F.map (p i)) (F.map (q i)) (F.map f) (F.map (R.f i))) :
    ⟨B, {I₀ := R.I₀, X := P, f := p}⟩ ∈ sheafSubcategoryEpimorphicFamilies F := by
  apply (family_epi_iff_local F B _).mpr
  intro U b
  rw [familyImage_sieve]
  have hlocal := (family_epi_iff_local F A R).mp hR U ((F.map f).hom.app (op U) b)
  rw [familyImage_sieve] at hlocal
  apply J.superset_covering ?_ hlocal
  intro V t ht
  obtain ⟨i, a, ha⟩ := ht
  have hi := (hp i).map ((sheafToPresheaf J (Type u)) ⋙
    (evaluation Cᵒᵖ (Type u)).obj (op V))
  obtain ⟨c, hc, _⟩ := Types.exists_of_isPullback hi ((F.obj B).obj.map t.op b) a
    (by exact ((F.map f).hom.naturality_apply t.op b).trans ha.symm)
  exact ⟨i, c, hc⟩

private theorem family_isCoveringClass {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (hpb : ∀ (A B T : E) (f : A ⟶ T) (g : B ⟶ T),
      ∃ (P : E) (p : P ⟶ A) (q : P ⟶ B),
        IsPullback (F.map p) (F.map q) (F.map f) (F.map g)) :
    PreZeroHypercover.IsCoveringClass
      (sheafSubcategoryEpimorphicFamilies.{u, v, w} F) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro A B f hf T g h heq
    let := hf
    exact (cancel_epi (F.map f)).mp (heq PUnit.unit)
  · intro A R S hR hS B f g heq
    apply hR B f g
    intro i
    apply hS i B (F.map (R.f i) ≫ f) (F.map (R.f i) ≫ g)
    intro j
    simpa only [PreZeroHypercover.bind_f, F.map_comp, Category.assoc] using heq ⟨i, j⟩
  · intro A R hR B f
    choose P p q hp using fun i ↦ hpb B (R.X i) A f (R.f i)
    exact ⟨P, p, q, fun i ↦ (hp i).of_map_of_faithful F,
      family_epi_pullback F A B R hR f P p q hp⟩

private def epiPrecoverage {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) : Precoverage E where
  coverings A := {S | ∀ (B : Sheaf J (Type u)) (f g : F.obj A ⟶ B),
    (∀ (T : E) (a : T ⟶ A), S a → F.map a ≫ f = F.map a ≫ g) → f = g}

private theorem family_epi_iff_cover {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) (A : E)
    (R : PreZeroHypercover.{max u v w} A) :
    ⟨A, R⟩ ∈ sheafSubcategoryEpimorphicFamilies F ↔
      R.presieve₀ ∈ epiPrecoverage F A := by
  constructor
  · intro h B f g hfg
    exact h B f g (fun i ↦ hfg _ _ ⟨i⟩)
  · intro h B f g hfg
    apply h B f g
    rintro T a ⟨i⟩
    exact hfg i

private theorem epiPrecoverage_site {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (hpb : ∀ (A B T : E) (f : A ⟶ T) (g : B ⟶ T),
      ∃ (P : E) (p : P ⟶ A) (q : P ⟶ B),
        IsPullback (F.map p) (F.map q) (F.map f) (F.map g)) :
    (epiPrecoverage F).IsSiteForCoverings := by
  classical
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · intro A B f hf T g h heq
    exact (cancel_epi (F.map f)).mp (heq A f (Presieve.singleton_self f))
  · intro A R T hR hT B f g heq
    apply hR B f g
    intro Y a ha
    apply hT Y a ha B (F.map a ≫ f) (F.map a ≫ g)
    intro Z b hb
    simpa only [F.map_comp, Category.assoc] using
      heq Z (b ≫ a) (Presieve.bind_comp _ ha hb)
  · intro I A U a ha B f
    let R : PreZeroHypercover.{max u v} A := ⟨I, U, a⟩
    have hR : ⟨A, R⟩ ∈ sheafSubcategoryEpimorphicFamilies F :=
      (family_epi_iff_cover F A R).mpr ha
    choose P p q hp using fun i ↦ hpb B (U i) A f (a i)
    refine ⟨P, p, q, fun i ↦ (hp i).of_map_of_faithful F, ?_⟩
    exact (family_epi_iff_cover F B _).mp
      (family_epi_pullback F A B R hR f P p q hp)

private def presieveFamily {E : Type v} [Category.{u} E] (A : E) (S : Presieve A) :
    PreZeroHypercover.{max u v w} A where
  I₀ := ULift.{w} {x : Σ B : E, (B ⟶ A) // S x.2}
  X i := i.down.val.1
  f i := i.down.val.2

private theorem presieveFamily_support {E : Type v} [Category.{u} E]
    (A : E) (S : Presieve A) : (presieveFamily.{u, v, w} A S).presieve₀ = S := by
  funext B
  ext f
  constructor
  · rintro ⟨i⟩
    exact i.down.property
  · intro hf
    exact Presieve.ofArrows.mk (ι := (presieveFamily.{u, v, w} A S).I₀)
      (ULift.up ⟨⟨B, f⟩, hf⟩)

-- Glue matching maps on the covering sieve of all local lifts of a section.
private theorem family_descent {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) (A : E)
    (R : PreZeroHypercover.{max u v w} A)
    (hR : ⟨A, R⟩ ∈ sheafSubcategoryEpimorphicFamilies F)
    (hpb : ∀ (A B T : E) (f : A ⟶ T) (g : B ⟶ T),
      ∃ (P : E) (p : P ⟶ A) (q : P ⟶ B),
        IsPullback (F.map p) (F.map q) (F.map f) (F.map g))
    [F.Faithful]
    (B : Sheaf J (Type u)) (x : ∀ i, F.obj (R.X i) ⟶ B)
    (hx : ∀ (i j : R.I₀) (T : E) (p : T ⟶ R.X i) (q : T ⟶ R.X j),
      p ≫ R.f i = q ≫ R.f j → F.map p ≫ x i = F.map q ≫ x j) :
    ∃! t : F.obj A ⟶ B, ∀ i, F.map (R.f i) ≫ t = x i := by
  classical
  have hB : Presieve.IsSheaf J B.obj := (isSheaf_iff_isSheaf_of_type _ _).mp B.property
  have agree : ∀ (i j : R.I₀) (U : C) (b : (F.obj (R.X i)).obj.obj (op U))
      (c : (F.obj (R.X j)).obj.obj (op U)),
      (F.map (R.f i)).hom.app (op U) b = (F.map (R.f j)).hom.app (op U) c →
        (x i).hom.app (op U) b = (x j).hom.app (op U) c := by
    intro i j U b c hbc
    obtain ⟨P, p, q, hp⟩ := hpb (R.X i) (R.X j) A (R.f i) (R.f j)
    have hw : p ≫ R.f i = q ≫ R.f j := F.map_injective (by simpa using hp.w)
    have hpU := hp.map ((sheafToPresheaf J (Type u)) ⋙
      (evaluation Cᵒᵖ (Type u)).obj (op U))
    obtain ⟨d, hd, hd'⟩ := Types.exists_of_isPullback hpU b c hbc
    change (F.map p).hom.app (op U) d = b at hd
    change (F.map q).hom.app (op U) d = c at hd'
    have he := congrArg (fun k : F.obj P ⟶ B ↦ k.hom.app (op U) d) (hx i j P p q hw)
    change (x i).hom.app (op U) ((F.map p).hom.app (op U) d) =
      (x j).hom.app (op U) ((F.map q).hom.app (op U) d) at he
    simpa only [hd, hd'] using he
  have hlocal (U : C) (a : (F.obj A).obj.obj (op U)) :
      (familyImage F A R).sieveOfSection a ∈ J U := by
    rw [← familyImage_sieve]
    exact (family_epi_iff_local F A R).mp hR U a
  have hex (U : C) (a : (F.obj A).obj.obj (op U)) :
      ∃! b : B.obj.obj (op U), ∀ (V : C) (f : V ⟶ U) (i : R.I₀)
        (c : (F.obj (R.X i)).obj.obj (op V)),
        (F.map (R.f i)).hom.app (op V) c = (F.obj A).obj.map f.op a →
          B.obj.map f.op b = (x i).hom.app (op V) c := by
    let S := (familyImage F A R).sieveOfSection a
    choose idx lift hlift using fun (V : C) (f : V ⟶ U) (hf : S f) ↦ hf
    let y : Presieve.FamilyOfElements B.obj S.arrows := fun V f hf ↦
      (x (idx V f hf)).hom.app (op V) (lift V f hf)
    have hy : y.Compatible := by
      intro V W Z p q f g hf hg hpq
      dsimp [y]
      rw [← (x _).hom.naturality_apply, ← (x _).hom.naturality_apply]
      apply agree
      rw [(F.map _).hom.naturality_apply, (F.map _).hom.naturality_apply,
        hlift, hlift]
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hpq]
    obtain ⟨b, hb, huniq⟩ := hB S (hlocal U a) y hy
    have hb' : ∀ (V : C) (f : V ⟶ U) (i : R.I₀)
        (c : (F.obj (R.X i)).obj.obj (op V)),
        (F.map (R.f i)).hom.app (op V) c = (F.obj A).obj.map f.op a →
          B.obj.map f.op b = (x i).hom.app (op V) c := by
      intro V f i c hc
      have hf : S f := ⟨i, c, hc⟩
      rw [hb f hf]
      exact agree _ _ V _ c ((hlift V f hf).trans hc.symm)
    refine ⟨b, hb', ?_⟩
    intro b' hb''
    apply huniq b'
    intro V f hf
    exact hb'' V f _ _ (hlift V f hf)
  choose val hval using fun (U : C) (a : (F.obj A).obj.obj (op U)) ↦ (hex U a).exists
  let t : F.obj A ⟶ B := ⟨{
    app := fun U ↦ ↾fun a ↦ val U.unop a
    naturality := by
      intro U V f
      ext a
      change val V.unop ((F.obj A).obj.map f a) = B.obj.map f (val U.unop a)
      apply (hex V.unop ((F.obj A).obj.map f a)).unique
      · exact hval V.unop ((F.obj A).obj.map f a)
      · intro W g i c hc
        rw [← ConcreteCategory.comp_apply, ← B.obj.map_comp]
        exact hval U.unop a W (g ≫ f.unop) i c (by
          simpa only [op_comp, Quiver.Hom.op_unop, Functor.map_comp,
            ConcreteCategory.comp_apply] using hc) }⟩
  have hfac : ∀ i, F.map (R.f i) ≫ t = x i := by
    intro i
    ext U a
    have h := hval U.unop ((F.map (R.f i)).hom.app U a) U.unop (𝟙 _) i a
      (by simp)
    simpa [t] using h
  refine ⟨t, hfac, ?_⟩
  intro t' ht'
  exact hR B t' t (fun i ↦ (ht' i).trans (hfac i).symm)

private theorem nerve_isSheafFor {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (hpb : ∀ (A B T : E) (f : A ⟶ T) (g : B ⟶ T),
      ∃ (P : E) (p : P ⟶ A) (q : P ⟶ B),
        IsPullback (F.map p) (F.map q) (F.map f) (F.map g))
    (B : Sheaf J (Type u)) (A : E) (S : Presieve A)
    (hS : S ∈ epiPrecoverage F A) :
    Presieve.IsSheafFor ((sheafSubcategoryNerve F).obj B) S := by
  classical
  let R := presieveFamily.{u, v, 0} A S
  have hsup : R.presieve₀ = S := presieveFamily_support A S
  rw [← hsup, Presieve.isSheafFor_arrows_iff]
  intro x hx
  have hR := (family_epi_iff_cover F A R).mpr (hsup.symm ▸ hS)
  exact family_descent F A R hR hpb B x (fun i j T p q hpq ↦ hx i j T p q hpq)

private theorem epiPrecoverage_pullback {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (hpb : ∀ (A B T : E) (f : A ⟶ T) (g : B ⟶ T),
      ∃ (P : E) (p : P ⟶ A) (q : P ⟶ B),
        IsPullback (F.map p) (F.map q) (F.map f) (F.map g))
    (A B : E) (f : B ⟶ A) (S : Presieve A) (hS : S ∈ epiPrecoverage F A) :
    ((Sieve.generate S).pullback f).arrows ∈ epiPrecoverage F B := by
  classical
  let R := presieveFamily.{u, v, 0} A S
  have hsup : R.presieve₀ = S := presieveFamily_support A S
  have hR := (family_epi_iff_cover F A R).mpr (hsup.symm ▸ hS)
  choose P p q hp using fun i ↦ hpb B (R.X i) A f (R.f i)
  have hP := family_epi_pullback F A B R hR f P p q hp
  intro T g h heq
  apply hP T g h
  intro i
  apply heq _ _
  change Sieve.generate S (p i ≫ f)
  rw [((hp i).of_map_of_faithful F).w]
  apply (Sieve.generate S).downward_closed
  apply Sieve.le_generate
  rw [← hsup]
  exact R.presieve₀_f i

private theorem nerve_isSheaf {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (hpb : ∀ (A B T : E) (f : A ⟶ T) (g : B ⟶ T),
      ∃ (P : E) (p : P ⟶ A) (q : P ⟶ B),
        IsPullback (F.map p) (F.map q) (F.map f) (F.map g))
    (B : Sheaf J (Type u)) :
    Presieve.IsSheaf (epiPrecoverage F).toGrothendieck ((sheafSubcategoryNerve F).obj B) := by
  apply (Precoverage.isSheaf_toGrothendieck_iff _).mpr
  intro A B f S hS
  exact nerve_isSheafFor F hpb _ B _ (epiPrecoverage_pullback F hpb A B f S hS)

private noncomputable def nerve_representable_iso {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful] :
    F ⋙ sheafSubcategoryNerve F ≅ yoneda :=
  NatIso.ofComponents (fun A ↦ NatIso.ofComponents
    (fun B ↦ ((Functor.FullyFaithful.ofFullyFaithful F).homEquiv).symm.toIso)
    (by
      intro X Y f
      ext x
      apply F.map_injective
      change F.map (F.preimage (F.map f.unop ≫ x)) =
        F.map (f.unop ≫ F.preimage x)
      simp)) (by
    intro X Y f
    ext Z x
    apply F.map_injective
    change F.map (F.preimage (x ≫ F.map f)) = F.map (F.preimage x ≫ f)
    simp)

private theorem epiPrecoverage_subcanonical {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (hpb : ∀ (A B T : E) (f : A ⟶ T) (g : B ⟶ T),
      ∃ (P : E) (p : P ⟶ A) (q : P ⟶ B),
        IsPullback (F.map p) (F.map q) (F.map f) (F.map g)) :
    (epiPrecoverage F).toGrothendieck.Subcanonical := by
  apply GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj
  intro A
  exact Presieve.isSheaf_iso _ ((nerve_representable_iso F).app A)
    (nerve_isSheaf F hpb (F.obj A))

-- Choose representatives of sheafified representables and transport their functoriality.
private noncomputable def representableLift {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (hrep : ∀ U : C, ∃ A : E,
      Nonempty (F.obj A ≅ (presheafToSheaf J (Type u)).obj (yoneda.obj U))) : C ⥤ E where
  obj U := (hrep U).choose
  map {U V} f := F.preimage ((hrep U).choose_spec.some.hom ≫
    (presheafToSheaf J (Type u)).map (yoneda.map f) ≫ (hrep V).choose_spec.some.inv)
  map_id U := F.map_injective (by simp)
  map_comp f g := F.map_injective (by simp)

private noncomputable def representableLiftIso {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (hrep : ∀ U : C, ∃ A : E,
      Nonempty (F.obj A ≅ (presheafToSheaf J (Type u)).obj (yoneda.obj U))) :
    representableLift F hrep ⋙ F ≅ yoneda ⋙ presheafToSheaf J (Type u) :=
  NatIso.ofComponents (fun U ↦ (hrep U).choose_spec.some) (by
    intro U V f
    dsimp [representableLift]
    simp)

private noncomputable def sectionEquiv {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (hrep : ∀ U : C, ∃ A : E,
      Nonempty (F.obj A ≅ (presheafToSheaf J (Type u)).obj (yoneda.obj U)))
    (U : C) (B : Sheaf J (Type u)) :
    (F.obj ((representableLift F hrep).obj U) ⟶ B) ≃ B.obj.obj (op U) :=
  (Iso.homCongr ((representableLiftIso F hrep).app U) (Iso.refl B)).trans
    (((sheafificationAdjunction J (Type u)).homEquiv _ _).trans yonedaEquiv)

set_option backward.isDefEq.respectTransparency false in
private theorem sectionEquiv_precomp {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (hrep : ∀ U : C, ∃ A : E,
      Nonempty (F.obj A ≅ (presheafToSheaf J (Type u)).obj (yoneda.obj U)))
    (U V : C) (f : V ⟶ U) (B : Sheaf J (Type u))
    (x : F.obj ((representableLift F hrep).obj U) ⟶ B) :
    sectionEquiv F hrep V B (F.map ((representableLift F hrep).map f) ≫ x) =
      B.obj.map f.op (sectionEquiv F hrep U B x) := by
  dsimp [sectionEquiv, Iso.homCongr]
  simp only [Category.comp_id]
  have h : (representableLiftIso F hrep).inv.app V ≫
      F.map ((representableLift F hrep).map f) ≫ x =
      (presheafToSheaf J (Type u)).map (yoneda.map f) ≫
        (representableLiftIso F hrep).inv.app U ≫ x := by
    dsimp [representableLift, representableLiftIso]
    simp
  rw [h]
  exact (congrArg yonedaEquiv ((sheafificationAdjunction J (Type u)).homEquiv_naturality_left
    (yoneda.map f) ((representableLiftIso F hrep).inv.app U ≫ x))).trans
      (yonedaEquiv_naturality _ _).symm

set_option backward.isDefEq.respectTransparency false in
private theorem sectionEquiv_postcomp {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (hrep : ∀ U : C, ∃ A : E,
      Nonempty (F.obj A ≅ (presheafToSheaf J (Type u)).obj (yoneda.obj U)))
    (U : C) (B D : Sheaf J (Type u)) (x : F.obj ((representableLift F hrep).obj U) ⟶ B)
    (f : B ⟶ D) :
    sectionEquiv F hrep U D (x ≫ f) = f.hom.app (op U) (sectionEquiv F hrep U B x) := by
  dsimp [sectionEquiv, Iso.homCongr]
  simp only [Category.comp_id, ← Category.assoc]
  exact (congrArg yonedaEquiv ((sheafificationAdjunction J (Type u)).homEquiv_naturality_right
    ((representableLiftIso F hrep).inv.app U ≫ x) f)).trans (yonedaEquiv_comp _ _)

private theorem lift_image_cover {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (hrep : ∀ U : C, ∃ A : E,
      Nonempty (F.obj A ≅ (presheafToSheaf J (Type u)).obj (yoneda.obj U)))
    (U : C) (S : Sieve U) (hS : S ∈ J U) :
    S.arrows.map (representableLift F hrep) ∈
      epiPrecoverage F ((representableLift F hrep).obj U) := by
  intro B f g heq
  apply (sectionEquiv F hrep U B).injective
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp B.property).isSeparated S hS).ext
  intro V a ha
  rw [← sectionEquiv_precomp, ← sectionEquiv_precomp]
  rw [heq _ _ (Presieve.map.of ha)]

set_option backward.isDefEq.respectTransparency false in
private theorem lift_coverDense {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (hrep : ∀ U : C, ∃ A : E,
      Nonempty (F.obj A ≅ (presheafToSheaf J (Type u)).obj (yoneda.obj U))) :
    (representableLift F hrep).IsCoverDense (epiPrecoverage F).toGrothendieck := by
  constructor
  intro A
  rw [← Sieve.generate_sieve (Sieve.coverByImage _ A)]
  apply Precoverage.generate_mem_toGrothendieck (J := epiPrecoverage F)
  intro B f g heq
  ext ⟨U⟩ a
  let x := (sectionEquiv F hrep U (F.obj A)).symm a
  have hx := heq _ (F.preimage x)
    (show Sieve.coverByImage (representableLift F hrep) A (F.preimage x) from
      ⟨U, 𝟙 _, F.preimage x, by simp⟩)
  have h := congrArg (sectionEquiv F hrep U B) hx
  simpa [sectionEquiv_postcomp, x] using h

set_option backward.isDefEq.respectTransparency false in
private theorem sectionEquiv_map {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (hrep : ∀ U : C, ∃ A : E,
      Nonempty (F.obj A ≅ (presheafToSheaf J (Type u)).obj (yoneda.obj U)))
    (U V : C) (f : U ⟶ V) :
    sectionEquiv F hrep U ((presheafToSheaf J (Type u)).obj (yoneda.obj V))
      (F.map ((representableLift F hrep).map f) ≫ (representableLiftIso F hrep).hom.app V) =
      (toSheafify J (yoneda.obj V)).app (op U) f := by
  dsimp [sectionEquiv, Iso.homCongr, representableLift, representableLiftIso]
  simp only [F.map_preimage, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id]
  have h := (sheafificationAdjunction J (Type u)).homEquiv_naturality_left
    (yoneda.map f) (𝟙 ((presheafToSheaf J (Type u)).obj (yoneda.obj V)))
  have hh := (congrArg yonedaEquiv h).trans (congrArg
    (fun a ↦ yonedaEquiv (yoneda.map f ≫ a))
    ((sheafificationAdjunction J (Type u)).homEquiv_id (yoneda.obj V)))
  simpa only [Category.comp_id, yonedaEquiv_comp, yonedaEquiv_yoneda_map,
    sheafificationAdjunction_unit_app, sheafToPresheaf, ObjectProperty.ι_obj] using hh

private theorem lift_locallyFull {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (hrep : ∀ U : C, ∃ A : E,
      Nonempty (F.obj A ≅ (presheafToSheaf J (Type u)).obj (yoneda.obj U))) :
    (representableLift F hrep).IsLocallyFull (epiPrecoverage F).toGrothendieck := by
  constructor
  intro U V f
  let v := representableLift F hrep
  let i := representableLiftIso F hrep
  let B := (presheafToSheaf J (Type u)).obj (yoneda.obj V)
  let s := sectionEquiv F hrep U B (F.map f ≫ i.hom.app V)
  have hS : v.imageSieve f ∈ J U := by
    apply J.superset_covering ?_ (Presheaf.imageSieve_mem J
      (toSheafify J (yoneda.obj V)) s)
    intro W a ha
    obtain ⟨b, hb⟩ := ha
    refine ⟨b, ?_⟩
    apply F.map_injective
    apply (cancel_mono (i.hom.app V)).mp
    apply (sectionEquiv F hrep W B).injective
    rw [sectionEquiv_map]
    rw [F.map_comp, Category.assoc]
    rw [sectionEquiv_precomp]
    exact hb
  have hh := Precoverage.generate_mem_toGrothendieck (lift_image_cover F hrep U _ hS)
  simpa only [Sieve.generate_map_eq_functorPushforward, Sieve.generate_sieve] using hh

private theorem lift_locallyFaithful {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (hrep : ∀ U : C, ∃ A : E,
      Nonempty (F.obj A ≅ (presheafToSheaf J (Type u)).obj (yoneda.obj U))) :
    (representableLift F hrep).IsLocallyFaithful (epiPrecoverage F).toGrothendieck := by
  constructor
  intro U V f g hfg
  have heq : (toSheafify J (yoneda.obj V)).app (op U) f =
      (toSheafify J (yoneda.obj V)).app (op U) g := by
    rw [← sectionEquiv_map F hrep, ← sectionEquiv_map F hrep, hfg]
  have hS : Sieve.equalizer f g ∈ J U :=
    Presheaf.equalizerSieve_mem J (toSheafify J (yoneda.obj V)) f g heq
  have hh := Precoverage.generate_mem_toGrothendieck (lift_image_cover F hrep U _ hS)
  simpa only [Sieve.generate_map_eq_functorPushforward, Sieve.generate_sieve] using hh

private noncomputable def nerve_restrict_iso {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (hrep : ∀ U : C, ∃ A : E,
      Nonempty (F.obj A ≅ (presheafToSheaf J (Type u)).obj (yoneda.obj U))) :
    sheafSubcategoryNerve F ⋙
        (Functor.whiskeringLeft _ _ (Type u)).obj (representableLift F hrep).op ≅
      sheafToPresheaf J (Type u) :=
  NatIso.ofComponents (fun B ↦ NatIso.ofComponents
    (fun U ↦ (sectionEquiv F hrep U.unop B).toIso) (by
      intro U V f
      ext x
      exact sectionEquiv_precomp F hrep U.unop V.unop f.unop B x)) (by
    intro B D f
    ext U x
    exact sectionEquiv_postcomp F hrep U.unop B D x f)

-- Closed sieves detect the topology, so every ambient sheaf suffices to reflect covers.
private theorem lift_inducedTopology {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (hrep : ∀ U : C, ∃ A : E,
      Nonempty (F.obj A ≅ (presheafToSheaf J (Type u)).obj (yoneda.obj U)))
    (hpb : ∀ (A B T : E) (f : A ⟶ T) (g : B ⟶ T),
      ∃ (P : E) (p : P ⟶ A) (q : P ⟶ B),
        IsPullback (F.map p) (F.map q) (F.map f) (F.map g)) :
    (representableLift F hrep).inducedTopology (epiPrecoverage F).toGrothendieck = J := by
  let v := representableLift F hrep
  let K := (epiPrecoverage F).toGrothendieck
  let := lift_coverDense F hrep
  let := lift_locallyFull F hrep
  let := lift_locallyFaithful F hrep
  apply le_antisymm
  · apply le_topology_of_closedSieves_isSheaf
    let B : Sheaf J (Type u) := ⟨(Functor.closedSieves J).toFunctor,
      (isSheaf_iff_isSheaf_of_type _ _).mpr (classifier_isSheaf J)⟩
    have h := v.op_comp_isSheaf_of_isSheaf_type (v.inducedTopology K)
      (nerve_isSheaf F hpb B)
    exact Presieve.isSheaf_iso _ ((nerve_restrict_iso F hrep).app B) h
  · intro U S hS
    rw [Functor.mem_inducedTopology_iff_of_isCoverDense]
    have hh := Precoverage.generate_mem_toGrothendieck (lift_image_cover F hrep U S hS)
    simpa only [Sieve.generate_map_eq_functorPushforward, Sieve.generate_sieve] using hh

private theorem lift_denseSubsite {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (hrep : ∀ U : C, ∃ A : E,
      Nonempty (F.obj A ≅ (presheafToSheaf J (Type u)).obj (yoneda.obj U)))
    (hpb : ∀ (A B T : E) (f : A ⟶ T) (g : B ⟶ T),
      ∃ (P : E) (p : P ⟶ A) (q : P ⟶ B),
        IsPullback (F.map p) (F.map q) (F.map f) (F.map g)) :
    (representableLift F hrep).IsDenseSubsite J (epiPrecoverage F).toGrothendieck := by
  let := lift_coverDense F hrep
  let := lift_locallyFull F hrep
  let := lift_locallyFaithful F hrep
  have h : (representableLift F hrep).IsDenseSubsite
      ((representableLift F hrep).inducedTopology (epiPrecoverage F).toGrothendieck)
      (epiPrecoverage F).toGrothendieck := inferInstance
  simpa only [lift_inducedTopology F hrep hpb] using h

private noncomputable def nerveToSheaf {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (hpb : ∀ (A B T : E) (f : A ⟶ T) (g : B ⟶ T),
      ∃ (P : E) (p : P ⟶ A) (q : P ⟶ B),
        IsPullback (F.map p) (F.map q) (F.map f) (F.map g)) :
    Sheaf J (Type u) ⥤ Sheaf (epiPrecoverage F).toGrothendieck (Type u) where
  obj B := ⟨(sheafSubcategoryNerve F).obj B,
    (isSheaf_iff_isSheaf_of_type _ _).mpr (nerve_isSheaf F hpb B)⟩
  map f := ⟨(sheafSubcategoryNerve F).map f⟩

private theorem nerveToSheaf_isEquivalence {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (hrep : ∀ U : C, ∃ A : E,
      Nonempty (F.obj A ≅ (presheafToSheaf J (Type u)).obj (yoneda.obj U)))
    (hpb : ∀ (A B T : E) (f : A ⟶ T) (g : B ⟶ T),
      ∃ (P : E) (p : P ⟶ A) (q : P ⟶ B),
        IsPullback (F.map p) (F.map q) (F.map f) (F.map g)) :
    (nerveToSheaf F hpb).IsEquivalence := by
  let v := representableLift F hrep
  let K := (epiPrecoverage F).toGrothendieck
  let := lift_denseSubsite F hrep hpb
  let W := v.sheafPushforwardContinuous (Type u) J K
  let N := nerveToSheaf F hpb
  have i : N ⋙ W ≅ 𝟭 _ :=
    NatIso.ofComponents (fun B ↦ (fullyFaithfulSheafToPresheaf J (Type u)).preimageIso
      ((nerve_restrict_iso F hrep).app B)) (by
      intro B D f
      apply (sheafToPresheaf J (Type u)).map_injective
      exact (nerve_restrict_iso F hrep).hom.naturality f)
  let : (N ⋙ W).IsEquivalence := Functor.isEquivalence_of_iso i.symm
  exact Functor.isEquivalence_of_comp_right N W

private noncomputable def nerve_representable_sheaf_iso {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J (Type u)) [F.Full] [F.Faithful]
    (hpb : ∀ (A B T : E) (f : A ⟶ T) (g : B ⟶ T),
      ∃ (P : E) (p : P ⟶ A) (q : P ⟶ B),
        IsPullback (F.map p) (F.map q) (F.map f) (F.map g)) :
    let := epiPrecoverage_subcanonical F hpb
    F ⋙ nerveToSheaf F hpb ≅ (epiPrecoverage F).toGrothendieck.yoneda := by
  let := epiPrecoverage_subcanonical F hpb
  exact NatIso.ofComponents (fun A ↦
    (fullyFaithfulSheafToPresheaf _ (Type u)).preimageIso
      ((nerve_representable_iso F).app A)) (by
      intro A B f
      apply (sheafToPresheaf _ (Type u)).map_injective
      exact (nerve_representable_iso F).hom.naturality f)

/-- A full pullback-closed subcategory containing the sheafified representables presents
its ambient topos, with any prescribed small collection of epimorphic families retained.
Source: Sites, Tag 03A1 (1)-(5), and Sets, Tag 000X
(blueprint: lem-weil-pbc-sheaf-subcategory-comparison).

Proof plan:
1. Sheafification adjunction and Yoneda identify maps from a sheafified representable
   to B with sections of B. Presheaf coproducts are sectionwise; sheafifying them gives
   sheaf coproducts. Local representation of sheafification sections and the epi/local
   surjectivity criterion identify joint epimorphy with the displayed local lifting sieve.
   This also applies to the empty family.
2. Isomorphisms, composites and pullbacks are epimorphic families, using successive
   local lifts and sectionwise fibre products. Fullness and the closure hypothesis
   realize the pullbacks in E.
3. Apply exists_small_coveringFamilies (000X), adjoining the prescribed families, the
   images of the original coverings, and all-sections covers by sheafified representables.
   Equal supports have the same matching families: the diagonal forces equal assignments
   to repeated arrows. Thus the resulting precoverage generates the required topology.
4. Matching maps into a sheaf descend along local lifts. Their values agree on fibre
   products and glue uniquely, independently of the lifts. This proves the nerve is a
   sheaf, and fullness identifies the nerve of F(A) with the representable at A.
5. Sheafified Yoneda is continuous: it takes coverings to epimorphic families and
   preserves existing covering pullbacks by left exactness of sheafification.
6. Local lifting of the unit section of a sheafified representable proves cocontinuity.
7. Local equality and local representation for sheafification prove local faithfulness
   and local fullness, respectively, without a subcanonicity assumption on C.
8. All-sections covers give cover density. Apply the special-cocontinuous comparison
   theorem. Its inverse image on representables is F, naturally in E.
9. The direct-image compatible families are exactly maps of sheaves, by the adjunction
   and Yoneda section bijections. This identifies the equivalence functor with the nerve,
   including both its restriction maps and its functoriality in the ambient sheaf. -/
theorem sheafSubcategory_comparison {C : Type u} [SmallCategory C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    {E : Type v} [Category.{u} E]
    (F : E ⥤ Sheaf J.toGrothendieck (Type u)) [F.Full] [F.Faithful]
    (hrep : ∀ U : C, ∃ A : E,
      Nonempty (F.obj A ≅ (presheafToSheaf J.toGrothendieck (Type u)).obj (yoneda.obj U)))
    (hpb : ∀ (A B T : E) (f : A ⟶ T) (g : B ⟶ T),
      ∃ (P : E) (p : P ⟶ A) (q : P ⟶ B),
        IsPullback (F.map p) (F.map q) (F.map f) (F.map g))
    (Cov₀ : Set (Σ A : E, PreZeroHypercover.{max u v w} A))
    (hsmall : Small.{max u v w} Cov₀)
    (hsub : Cov₀ ⊆ sheafSubcategoryEpimorphicFamilies F) :
    (∀ (A : E) (R : PreZeroHypercover.{max u v w} A),
      (⟨A, R⟩ ∈ sheafSubcategoryEpimorphicFamilies F ↔
        ∀ (U : C) (a : (F.obj A).obj.obj (op U)),
          Sieve.generate (fun (V : C) (f : V ⟶ U) ↦
            ∃ (i : R.I₀) (b : (F.obj (R.X i)).obj.obj (op V)),
              (F.map (R.f i)).hom.app (op V) b = (F.obj A).obj.map f.op a)
            ∈ J.toGrothendieck U)) ∧
    ∃ (Cov' : Set (Σ A : E, PreZeroHypercover.{max u v w} A))
      (K : Precoverage E) (hK : K.toGrothendieck.Subcanonical)
      (e : Sheaf J.toGrothendieck (Type u) ≌ Sheaf K.toGrothendieck (Type u)),
      Small.{max u v w} Cov' ∧ Cov₀ ⊆ Cov' ∧
      Cov' ⊆ sheafSubcategoryEpimorphicFamilies F ∧
      PreZeroHypercover.IsCoveringClass Cov' ∧ K.IsSiteForCoverings ∧
      (∀ (A : E) (R : PreZeroHypercover.{max u v w} A),
        ⟨A, R⟩ ∈ sheafSubcategoryEpimorphicFamilies F →
          ∃ R' : PreZeroHypercover.{max u v w} A,
            ⟨A, R'⟩ ∈ Cov' ∧ R.presieve₀ = R'.presieve₀) ∧
      (∀ (A : E) (S : Presieve A),
        S ∈ K A ↔ ∃ R : PreZeroHypercover.{max u v w} A,
          ⟨A, R⟩ ∈ Cov' ∧ S = R.presieve₀) ∧
      Nonempty (e.functor ⋙ sheafToPresheaf K.toGrothendieck (Type u) ≅
        sheafSubcategoryNerve F) ∧
      Nonempty (F ⋙ e.functor ⋙ sheafToPresheaf K.toGrothendieck (Type u) ≅ yoneda) ∧
      Nonempty ((@GrothendieckTopology.yoneda E _ K.toGrothendieck hK) ⋙ e.inverse ≅ F) := by
  classical
  -- The argument works directly with the associated Grothendieck topology.
  have _ := hJ
  refine ⟨fun A R ↦ family_epi_iff_local F A R, ?_⟩
  obtain ⟨Cov', hsmall', h₀, hsub', hclass', hcover⟩ :=
    PreZeroHypercover.exists_small_coveringFamilies
      (sheafSubcategoryEpimorphicFamilies F) (family_isCoveringClass F hpb) Cov₀ hsmall hsub
  let K := epiPrecoverage F
  let hK := epiPrecoverage_subcanonical F hpb
  let := nerveToSheaf_isEquivalence F hrep hpb
  let e := (nerveToSheaf F hpb).asEquivalence
  refine ⟨Cov', K, hK, e, hsmall', h₀, hsub', hclass', epiPrecoverage_site F hpb,
    hcover, ?_, ⟨Iso.refl _⟩, ⟨nerve_representable_iso F⟩, ?_⟩
  · intro A S
    constructor
    · intro hS
      let R := presieveFamily.{u, v, w} A S
      have hR : ⟨A, R⟩ ∈ sheafSubcategoryEpimorphicFamilies F := by
        rw [family_epi_iff_cover, presieveFamily_support]
        exact hS
      obtain ⟨R', hR', heq⟩ := hcover A R hR
      exact ⟨R', hR', (presieveFamily_support A S).symm.trans heq⟩
    · rintro ⟨R, hR, rfl⟩
      exact (family_epi_iff_cover F A R).mp (hsub' hR)
  · exact ⟨Functor.isoWhiskerRight (nerve_representable_sheaf_iso F hpb).symm e.inverse ≪≫
      Functor.associator F e.functor e.inverse ≪≫
      Functor.isoWhiskerLeft F e.unitIso.symm ≪≫ Functor.rightUnitor F⟩

end CategoryTheory
