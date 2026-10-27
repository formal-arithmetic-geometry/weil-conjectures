/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.LargeSetSheafification
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty

/-!
# Sheafification comparison from representable fppf generators

Source: Stacks Project, Groupoids, Tag 045Z, injectivity and covering-surjectivity
argument, abstracted to compatible representable generators; Sites, Tags 00WH and 00WK
(blueprint: lem-trf-fppf-generator-sheafification-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

-- The universal property identifies any chosen unit with the canonical one.
private theorem chosen_unit_locallyBijective
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (Type v)] [J.WEqualsLocallyBijective (Type v)]
    (P : Cᵒᵖ ⥤ Type v) (F : Sheaf J (Type v)) (η : P ⟶ F.obj)
    (hη : ∀ (G : Sheaf J (Type v)) (θ : P ⟶ G.obj),
      ∃! φ : F ⟶ G, η ≫ φ.hom = θ) :
    Presheaf.IsLocallyInjective J η ∧ Presheaf.IsLocallySurjective J η := by
  obtain ⟨a, ha, hua⟩ := hη ((presheafToSheaf J (Type v)).obj P) (toSheafify J P)
  let b : (presheafToSheaf J (Type v)).obj P ⟶ F :=
    ⟨sheafifyLift J η F.property⟩
  have hb : toSheafify J P ≫ b.hom = η := toSheafify_sheafifyLift J η F.property
  have hab : a ≫ b = 𝟙 F := by
    obtain ⟨c, hc, huc⟩ := hη F η
    exact (huc (a ≫ b) (by
      change η ≫ (a.hom ≫ b.hom) = η
      rw [← Category.assoc, ha, hb])).trans
      (huc (𝟙 F) (by simp)).symm
  have hba : b ≫ a = 𝟙 _ := by
    apply (sheafToPresheaf J (Type v)).map_injective
    apply sheafify_hom_ext J _ _
      ((presheafToSheaf J (Type v)).obj P).property
    change toSheafify J P ≫ (b.hom ≫ a.hom) = toSheafify J P ≫ 𝟙 _
    rw [← Category.assoc, hb, ha, Category.comp_id]
  have : IsIso b := ⟨⟨a, hba, hab⟩⟩
  have : IsIso b.hom := (sheafToPresheaf J (Type v)).map_isIso b
  rw [← hb]
  constructor <;> infer_instance

private theorem fppf_over_cover_mem
    {S : Scheme.{u}} {T : Over S} {I : Type*} (V : I → Over S)
    (f : ∀ i, V i ⟶ T)
    (h : Presieve.ofArrows (fun i ↦ (V i).left) (fun i ↦ (f i).left) ∈
      fppfPrecoverage T.left) :
    Sieve.generate (Presieve.ofArrows V f) ∈ (fppfTopology.over S) T := by
  rw [over_toGrothendieck_eq_toGrothendieck_comap_forget]
  apply Precoverage.generate_mem_toGrothendieck
  simpa only [Precoverage.mem_comap_iff, Presieve.map_ofArrows,
    Over.forget_obj, Over.forget_map] using h

-- Extract an actual fppf family, with indices in the coefficient universe.
private theorem generator_local_representatives
    {S : Scheme.{u}} {U : Over S}
    (P : (Over S)ᵒᵖ ⥤ Type (max (u + 1) v))
    (q : uliftYoneda.{max (u + 1) v}.obj U ⟶ P)
    (hq : ∀ T : Over S, Function.Surjective (q.app (op T)))
    (F : Sheaf (fppfTopology.over S) (Type (max (u + 1) v))) (η : P ⟶ F.obj)
    [Presheaf.IsLocallySurjective (fppfTopology.over S) η]
    (T : Over S) (z : F.obj.obj (op T)) :
    ∃ (I : Type (max (u + 1) v)) (V : I → Over S)
      (f : ∀ i, V i ⟶ T) (a : ∀ i, V i ⟶ U),
      Presieve.ofArrows (fun i ↦ (V i).left) (fun i ↦ (f i).left) ∈
        fppfPrecoverage T.left ∧
      ∀ i, F.obj.map (f i).op z =
        η.app (op (V i)) (q.app (op (V i)) (ULift.up (a i))) := by
  classical
  have : (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}).ContainsIdentities :=
    ⟨fun X ↦ ⟨inferInstanceAs (Flat (𝟙 X)),
      inferInstanceAs (LocallyOfFinitePresentation (𝟙 X))⟩⟩
  have : fppfPrecoverage.{u}.HasIsos := by unfold fppfPrecoverage; infer_instance
  let K := fppfPrecoverage.comap (Over.forget S)
  have h : Presheaf.imageSieve η z ∈ K.toGrothendieck T := by
    rw [← over_toGrothendieck_eq_toGrothendieck_comap_forget]
    exact Presheaf.imageSieve_mem (fppfTopology.over S) η z
  obtain ⟨R, hR, hle⟩ := K.mem_toGrothendieck_iff_of_isStableUnderComposition.mp h
  obtain ⟨I, V, f, rfl⟩ := R.exists_eq_ofArrows
  have hreindex : Presieve.ofArrows (fun i : ULift.{v} I ↦ V i.down)
      (fun i ↦ f i.down) = Presieve.ofArrows V f := by
    exact Presieve.ofArrows_comp_eq_of_surjective f
      (a := ULift.down) (fun i ↦ ⟨ULift.up i, rfl⟩)
  choose t ht using fun i ↦ hle _ (f i) (Presieve.ofArrows.mk i)
  choose a ha using fun i ↦ hq (V i) (t i)
  refine ⟨ULift.{v} I, fun i ↦ V i.down, fun i ↦ f i.down,
    fun i ↦ (a i.down).down, ?_, ?_⟩
  · have hR' : Presieve.ofArrows (fun i : ULift.{v} I ↦ V i.down)
        (fun i ↦ f i.down) ∈ K T := hreindex.symm ▸ hR
    simpa only [K, Precoverage.mem_comap_iff, Presieve.map_ofArrows,
      Over.forget_obj, Over.forget_map] using hR'
  · intro i
    exact (ht i.down).symm.trans (congrArg (η.app _) (ha i.down).symm)

private theorem generator_pullback_cover
    {S : Scheme.{u}} {U U' : Over S} (g : U' ⟶ U) [Etale g.left]
    [Surjective g.left] {T : Over S} {I : Type*} (V : I → Over S)
    (f : ∀ i, V i ⟶ T) (a : ∀ i, V i ⟶ U)
    (hcov : Presieve.ofArrows (fun i ↦ (V i).left) (fun i ↦ (f i).left) ∈
      fppfPrecoverage T.left) :
    (∀ i, Etale (pullback.fst (a i) g).left ∧
      Surjective (pullback.fst (a i) g).left ∧
      Presieve.singleton (pullback.fst (a i) g).left ∈
        fppfPrecoverage (V i).left) ∧
    Presieve.ofArrows (fun i ↦ (pullback (a i) g).left)
      (fun i ↦ ((pullback.fst (a i) g) ≫ f i).left) ∈ fppfPrecoverage T.left := by
  have he (i : I) : Etale (pullback.fst (a i) g).left :=
    MorphismProperty.of_isPullback (P := @Etale)
      (((IsPullback.of_hasPullback (a i) g).map (Over.forget S)).flip)
      (show Etale g.left from inferInstance)
  have hs (i : I) : Surjective (pullback.fst (a i) g).left :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (((IsPullback.of_hasPullback (a i) g).map (Over.forget S)).flip)
      (show Surjective g.left from inferInstance)
  refine ⟨fun i ↦ ⟨he i, hs i, ?_⟩, ?_⟩
  · have := he i
    have := hs i
    exact (pullback.fst (a i) g).left.singleton_mem_fppfPrecoverage
  · rw [fppfPrecoverage, ofArrows_mem_precoverage_iff] at hcov ⊢
    refine ⟨?_, ?_⟩
    · intro x
      obtain ⟨i, y, hy⟩ := hcov.1 x
      obtain ⟨w, hw⟩ := (hs i).surj y
      exact ⟨i, w, by simpa only [Over.comp_left, Scheme.Hom.comp_apply, hw] using hy⟩
    · intro i
      have := he i
      have : Flat (f i).left := (hcov.2 i).1
      have : LocallyOfFinitePresentation (f i).left := (hcov.2 i).2
      change Flat ((pullback.fst (a i) g).left ≫ (f i).left) ∧
        LocallyOfFinitePresentation ((pullback.fst (a i) g).left ≫ (f i).left)
      exact ⟨inferInstance, inferInstance⟩

/-- Compatible representable generators give an injective comparison of chosen
sheafifications, and an étale surjection of generators gives the displayed local lifts,
pullback coverings, unique gluing and natural inverse. The universal properties `hη`
and `hη'` allow arbitrary chosen sheafifications, rather than just the adjunction's choice.
`uliftYoneda` is the representable presheaf with its values lifted into the value universe.
All coverings below are actual fppf covering families, not just covering sieves.
Source: Stacks Project, Groupoids, Tag 045Z; Sites, Tags 00WH, 00WK and 00W6;
Topologies, Tag 021O (blueprint: lem-trf-fppf-generator-sheafification-comparison).

Proof:
1. Identify each chosen sheafification with the canonical one by its universal
   property. Its unit is locally bijective, including in the larger value universe.
2. The universal property of `η'` gives the unique `α`. Since `vmap` is injective,
   `vmap ≫ η` is locally injective. Cancel the locally bijective `η'` to show that
   `α` is locally injective, hence sectionwise injective between sheaves.
3. Extract an actual fppf cover from the covering image sieve of `η`. Lift each
   representative through the sectionwise surjection `q`, raising the cover's
   index universe with `ULift` when necessary.
4. For surjective `g`, its pullback projections are étale and surjective, hence
   singleton fppf covers. Their composites with the original family cover `T`:
   lift a point through the original family and then through the projection.
5. The pullback equation, `hcompat`, `hα` and naturality give the displayed image
   formula. These local preimages make `α` locally surjective. Mathlib's sheaf
   local-bijection criterion glues them and proves `α` is an isomorphism.
6. Take `β = inv α`. Naturality and the image formula, followed by injectivity of
   `α`, prove overlap compatibility and the restriction formula for `β(z)`.
   The inverse equations show its image is `z`. Injectivity proves uniqueness
   and independence of every choice of cover and representatives. -/
theorem fppf_generator_sheafification_comparison
    {S : Scheme.{u}} {U U' : Over S} (g : U' ⟶ U) [Etale g.left]
    (P P' : (Over S)ᵒᵖ ⥤ Type (max (u + 1) v))
    (vmap : P' ⟶ P)
    (hv : ∀ T : Over S, Function.Injective (vmap.app (op T)))
    (q : uliftYoneda.{max (u + 1) v}.obj U ⟶ P)
    (q' : uliftYoneda.{max (u + 1) v}.obj U' ⟶ P')
    (hq : ∀ T : Over S, Function.Surjective (q.app (op T)))
    (hq' : ∀ T : Over S, Function.Surjective (q'.app (op T)))
    (hcompat : q' ≫ vmap = uliftYoneda.map g ≫ q)
    (F F' : Sheaf (fppfTopology.over S) (Type (max (u + 1) v)))
    (η : P ⟶ F.obj) (η' : P' ⟶ F'.obj)
    (hη : ∀ (G : Sheaf (fppfTopology.over S) (Type (max (u + 1) v)))
      (θ : P ⟶ G.obj), ∃! φ : F ⟶ G, η ≫ φ.hom = θ)
    (hη' : ∀ (G : Sheaf (fppfTopology.over S) (Type (max (u + 1) v)))
      (θ : P' ⟶ G.obj), ∃! φ : F' ⟶ G, η' ≫ φ.hom = θ) :
    ∃ α : F' ⟶ F,
      η' ≫ α.hom = vmap ≫ η ∧
      (∀ α' : F' ⟶ F, η' ≫ α'.hom = vmap ≫ η → α' = α) ∧
      (∀ T : Over S, Function.Injective (α.hom.app (op T))) ∧
      (Surjective g.left →
        (∀ (T : Over S) (z : F.obj.obj (op T)),
          (∃ (I : Type (max (u + 1) v)) (V : I → Over S)
            (f : ∀ i, V i ⟶ T) (a : ∀ i, V i ⟶ U),
            Presieve.ofArrows (fun i ↦ (V i).left) (fun i ↦ (f i).left) ∈
              fppfPrecoverage T.left ∧
            ∀ i, F.obj.map (f i).op z =
              η.app (op (V i)) (q.app (op (V i)) (ULift.up (a i)))) ∧
          (∀ (I : Type (max (u + 1) v)) (V : I → Over S)
            (f : ∀ i, V i ⟶ T) (a : ∀ i, V i ⟶ U),
            Presieve.ofArrows (fun i ↦ (V i).left) (fun i ↦ (f i).left) ∈
              fppfPrecoverage T.left →
            (∀ i, F.obj.map (f i).op z =
              η.app (op (V i)) (q.app (op (V i)) (ULift.up (a i)))) →
            (∀ i, Etale (pullback.fst (a i) g).left ∧
              Surjective (pullback.fst (a i) g).left ∧
              Presieve.singleton (pullback.fst (a i) g).left ∈
                fppfPrecoverage (V i).left) ∧
            Presieve.ofArrows (fun i ↦ (pullback (a i) g).left)
              (fun i ↦ ((pullback.fst (a i) g) ≫ f i).left) ∈
                fppfPrecoverage T.left ∧
            (∀ i, α.hom.app (op (pullback (a i) g))
              (η'.app (op (pullback (a i) g))
                (q'.app (op (pullback (a i) g)) (ULift.up (pullback.snd (a i) g)))) =
                  F.obj.map ((pullback.fst (a i) g) ≫ f i).op z) ∧
            (∀ (i j : I) (Z : Over S) (r : Z ⟶ pullback (a i) g)
              (s : Z ⟶ pullback (a j) g),
              r ≫ pullback.fst (a i) g ≫ f i = s ≫ pullback.fst (a j) g ≫ f j →
              F'.obj.map r.op (η'.app (op (pullback (a i) g))
                (q'.app (op (pullback (a i) g)) (ULift.up (pullback.snd (a i) g)))) =
              F'.obj.map s.op (η'.app (op (pullback (a j) g))
                (q'.app (op (pullback (a j) g)) (ULift.up (pullback.snd (a j) g))))) ∧
            ∃! x : F'.obj.obj (op T),
              (∀ i, F'.obj.map ((pullback.fst (a i) g) ≫ f i).op x =
                η'.app (op (pullback (a i) g))
                  (q'.app (op (pullback (a i) g)) (ULift.up (pullback.snd (a i) g)))) ∧
              α.hom.app (op T) x = z)) ∧
        (∃ β : F ⟶ F', β ≫ α = 𝟙 F ∧ α ≫ β = 𝟙 F' ∧
          ∀ (T : Over S) (z : F.obj.obj (op T)) (x : F'.obj.obj (op T)),
            α.hom.app (op T) x = z → β.hom.app (op T) z = x) ∧
        IsIso α) := by
  classical
  -- Surjectivity of q' is part of the original interface; only that of q is needed.
  have _ := hq'
  have : (fppfTopology.over S).WEqualsLocallyBijective (Type (max (u + 1) v)) :=
    largeSetSheafification_locallyBijective (fppfTopology.over S)
  obtain ⟨hηinj, hηsurj⟩ := chosen_unit_locallyBijective _ P F η hη
  obtain ⟨hη'inj, hη'surj⟩ := chosen_unit_locallyBijective _ P' F' η' hη'
  have := hηinj
  have := hηsurj
  have := hη'inj
  have := hη'surj
  obtain ⟨α, hα, huα⟩ := hη' F (vmap ≫ η)
  have : Presheaf.IsLocallyInjective (fppfTopology.over S) vmap :=
    Presheaf.isLocallyInjective_of_injective _ _ (fun T ↦ hv T.unop)
  have : Presheaf.IsLocallyInjective (fppfTopology.over S) α.hom := by
    apply (Presheaf.comp_isLocallyInjective_iff _ η' α.hom).mp
    rw [hα]
    infer_instance
  have hinj (T : Over S) : Function.Injective (α.hom.app (op T)) :=
    (Sheaf.isLocallyInjective_iff_injective α).mp inferInstance (op T)
  refine ⟨α, hα, huα, hinj, ?_⟩
  intro hg
  have := hg
  have reps := generator_local_representatives P q hq F η
  -- The image of the specified lift is calculated before using descent.
  have himage {T : Over S} (z : F.obj.obj (op T))
      {I : Type (max (u + 1) v)} (V : I → Over S)
      (f : ∀ i, V i ⟶ T) (a : ∀ i, V i ⟶ U)
      (hz : ∀ i, F.obj.map (f i).op z =
        η.app (op (V i)) (q.app (op (V i)) (ULift.up (a i)))) (i : I) :
      α.hom.app (op (pullback (a i) g))
        (η'.app (op (pullback (a i) g))
          (q'.app (op (pullback (a i) g)) (ULift.up (pullback.snd (a i) g)))) =
      F.obj.map ((pullback.fst (a i) g) ≫ f i).op z := by
    let W := pullback (a i) g
    let b := pullback.snd (a i) g
    let p := pullback.fst (a i) g
    have hc := congrArg (fun t ↦ t.app (op W) (ULift.up b)) hcompat
    change vmap.app (op W) (q'.app (op W) (ULift.up b)) =
      q.app (op W) (ULift.up (b ≫ g)) at hc
    have hA := congrArg (fun t ↦ t.app (op W)
      (q'.app (op W) (ULift.up b))) hα
    change α.hom.app (op W) (η'.app (op W) (q'.app (op W) (ULift.up b))) =
      η.app (op W) (vmap.app (op W) (q'.app (op W) (ULift.up b))) at hA
    have hn := congrArg (fun t :
      (uliftYoneda.{max (u + 1) v}.obj U).obj (op (V i)) ⟶ F.obj.obj (op W) ↦
        t (ULift.up (a i))) ((q ≫ η).naturality p.op)
    change η.app (op W) (q.app (op W) (ULift.up (p ≫ a i))) =
      F.obj.map p.op (η.app (op (V i)) (q.app (op (V i)) (ULift.up (a i)))) at hn
    change α.hom.app (op W) (η'.app (op W) (q'.app (op W) (ULift.up b))) = _
    rw [hA, hc, ← pullback.condition, hn, ← hz i]
    exact (F.obj.map_comp_apply (f i).op p.op z).symm
  have : Sheaf.IsLocallySurjective α := by
    constructor
    intro T z
    obtain ⟨I, V, f, a, hcov, hz⟩ := reps T z
    obtain ⟨_, hcov'⟩ := generator_pullback_cover g V f a hcov
    apply (fppfTopology.over S).superset_covering _
      (fppf_over_cover_mem _ _ hcov')
    apply (Sieve.generate_le_iff _ _).mpr
    rintro Y k ⟨i⟩
    exact ⟨η'.app (op (pullback (a i) g))
      (q'.app (op (pullback (a i) g)) (ULift.up (pullback.snd (a i) g))),
      himage z V f a hz i⟩
  have : IsIso α := (Sheaf.isLocallyBijective_iff_isIso α).mp ⟨inferInstance, inferInstance⟩
  let β : F ⟶ F' := inv α
  have hβ (T : Over S) (z : F.obj.obj (op T)) :
      α.hom.app (op T) (β.hom.app (op T) z) = z := by
    have h := congrArg (fun t : F ⟶ F ↦ t.hom.app (op T) z) (IsIso.inv_hom_id α)
    exact h
  refine ⟨?_, ⟨β, IsIso.inv_hom_id α, IsIso.hom_inv_id α, ?_⟩, inferInstance⟩
  · intro T z
    refine ⟨reps T z, ?_⟩
    intro I V f a hcov hz
    obtain ⟨hp, hcov'⟩ := generator_pullback_cover g V f a hcov
    refine ⟨hp, hcov', himage z V f a hz, ?_, ?_⟩
    · intro i j Z r s hrs
      apply hinj Z
      rw [α.hom.naturality_apply, α.hom.naturality_apply,
        himage z V f a hz i, himage z V f a hz j,
        ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp]
      rw [hrs]
    · refine ⟨β.hom.app (op T) z, ⟨?_, hβ T z⟩, ?_⟩
      · intro i
        apply hinj (pullback (a i) g)
        rw [α.hom.naturality_apply, hβ, himage z V f a hz i]
      · intro x hx
        exact hinj T (hx.2.trans (hβ T z).symm)
  · intro T z x hx
    exact hinj T ((hβ T z).trans hx.symm)

end AlgebraicGeometry.Scheme
