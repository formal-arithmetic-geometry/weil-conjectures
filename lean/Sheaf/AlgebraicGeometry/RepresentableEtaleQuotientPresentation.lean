/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Sheaf.AlgebraicGeometry.EtaleRelationKernelPair
import WeilConjectures.AlgebraicGeometry.FpqcDescentEtale

/-!
# Presentations by representable quotients of étale equivalence relations

Source: Stacks Project, Spaces, Tag 02WV (lemma-when-it-works-it-works), and Tag 0265
(lemma-presentation-quasi-compact), second step
(blueprint: lem-trf-representable-etale-quotient-presentation).

The coequalizer is the pointwise quotient presheaf, and `hη` specifies its sheafification
by the universal property. Representability is assumed only for the quotient map.
The local isomorphisms are characterized by their projections to the covering scheme
and to `V`; this specifies the canonical isomorphisms, including the orientation of `s,t`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

-- Sites, Tags 00WB and 00WK: the local image is a sheaf. The universal property
-- retracts its inclusion, so every section belongs to the local image.
private theorem universal_unit_locallySurjective
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    {A : Cᵒᵖ ⥤ Type u} (F : Sheaf J (Type u)) (η : A ⟶ F.obj)
    (hη : ∀ G : Sheaf J (Type u),
      Function.Bijective (fun g : F.obj ⟶ G.obj ↦ η ≫ g)) :
    Presheaf.IsLocallySurjective J η := by
  let B := (Subfunctor.range η).sheafify J
  have hB : Presheaf.IsSheaf J B.toFunctor :=
    (isSheaf_iff_isSheaf_of_type J _).mpr
      ((Subfunctor.range η).sheafify_isSheaf
        ((isSheaf_iff_isSheaf_of_type J _).mp F.property))
  obtain ⟨l, hl⟩ := (hη ⟨B.toFunctor, hB⟩).surjective
    (Subfunctor.toRangeSheafify J η)
  change η ≫ l = Subfunctor.toRangeSheafify J η at hl
  have he : l ≫ B.ι = 𝟙 F.obj := by
    apply (hη F).injective
    change η ≫ l ≫ B.ι = η ≫ 𝟙 F.obj
    rw [← Category.assoc, hl]
    rfl
  rw [Presheaf.isLocallySurjective_iff_range_sheafify_eq_top']
  apply le_antisymm le_top
  intro U x _
  have hx : (l.app U x).val = x := by
    simpa using congrArg (fun k ↦ k.app U x) he
  exact hx ▸ (l.app U x).property

-- Spaces, Tag 02WV: the coequalizer projection is pointwise surjective; compose
-- with the locally surjective unit and extract a generating covering family.
private theorem local_lifts {S : Scheme.{u}} {R V : Over S} (s t : R ⟶ V)
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ F.obj)
    (hη : ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun g : F.obj ⟶ G.obj ↦ η ≫ g))
    (T : Over S) (x : F.obj.obj (op T)) :
    ∃ (I : Type (u + 1)) (T' : I → Over S) (f : ∀ i, T' i ⟶ T)
      (a : ∀ i, T' i ⟶ V),
      Presieve.ofArrows (fun i ↦ (T' i).left) (fun i ↦ (f i).left) ∈
        Scheme.fppfPrecoverage T.left ∧
      ∀ i, (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η).app (op (T' i)) (a i) =
        F.obj.map (f i).op x := by
  classical
  let π := coequalizer.π (yoneda.map s) (yoneda.map t)
  have : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) π := by
    apply Presheaf.isLocallySurjective_of_surjective
    intro U
    exact (CategoryTheory.epi_iff_surjective (π.app U)).mp inferInstance
  have := universal_unit_locallySurjective _ F η hη
  have hcover := Presheaf.imageSieve_mem (Scheme.fppfTopology.over S) (π ≫ η) x
  rw [GrothendieckTopology.mem_over_iff] at hcover
  have : (@Flat ⊓ @LocallyOfFinitePresentation :
      MorphismProperty Scheme.{u}).ContainsIdentities :=
    ⟨fun X ↦ ⟨inferInstanceAs (Flat (𝟙 X)),
      inferInstanceAs (LocallyOfFinitePresentation (𝟙 X))⟩⟩
  have : Scheme.fppfPrecoverage.{u}.HasIsos := by
    unfold Scheme.fppfPrecoverage
    infer_instance
  obtain ⟨W, hW, hle⟩ :=
    Scheme.fppfPrecoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hcover
  obtain ⟨I, Z, g, rfl⟩ := W.exists_eq_ofArrows
  have hl (i : I) := (Sieve.overEquiv_iff _ (g i)).mp (hle _ _ ⟨i⟩)
  choose a ha using hl
  exact ⟨I, fun i ↦ Over.mk (g i ≫ T.hom), fun i ↦ Over.homMk (g i), a, hW, ha⟩

-- Spaces, Tag 02WV: paste the two pullback squares into squares with the same
-- cospan, and use Yoneda to recover their unique isomorphism.
private theorem local_model {C : Type*} [Category C] [HasPullbacks C]
    {R V P T W : C} (s t : R ⟶ V)
    {F : Cᵒᵖ ⥤ Type u} (q : yoneda.obj V ⟶ F) (x : yoneda.obj T ⟶ F)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) q q)
    (p : P ⟶ T) (b : P ⟶ V)
    (hP : IsPullback (yoneda.map b) (yoneda.map p) q x)
    (f : W ⟶ T) (a : W ⟶ V) (ha : yoneda.map a ≫ q = yoneda.map f ≫ x) :
    ∃! e : pullback p f ≅ pullback a t,
      e.hom ≫ pullback.fst a t = pullback.snd p f ∧
      e.hom ≫ pullback.snd a t ≫ s = pullback.fst p f ≫ b := by
  let hA := ((IsPullback.of_hasPullback p f).map yoneda).paste_horiz hP
  let hB := ((IsPullback.of_hasPullback a t).flip.map yoneda).paste_horiz hR
  rw [ha] at hB
  let e := yoneda.preimageIso (hA.isoIsPullback _ _ hB)
  have he₁ : e.hom ≫ pullback.fst a t = pullback.snd p f := by
    apply yoneda.map_injective
    simp [e]
  have he₂ : e.hom ≫ pullback.snd a t ≫ s = pullback.fst p f ≫ b := by
    apply yoneda.map_injective
    simp [e, Functor.map_comp]
  refine ⟨e, ⟨he₁, he₂⟩, ?_⟩
  intro e' he'
  apply Iso.ext
  apply yoneda.map_injective
  apply hB.hom_ext
  · simpa only [← Functor.map_comp, Category.assoc] using
      congrArg yoneda.map (he'.2.trans he₂.symm)
  · simpa only [← Functor.map_comp] using congrArg yoneda.map (he'.1.trans he₁.symm)

/-- Every scheme pullback of a representable quotient map of an étale equivalence relation
is étale and surjective. Fppf-local representatives identify that pullback with the base
change of `t`, with its map to `V` given by `s`. Every quotient section has étale-local lifts.
Source: Stacks Project, Spaces, Tag 02WV, full pullback and descent proof, and Tag 0265,
second step, which runs that argument assuming only representability of the quotient map
(blueprint: lem-trf-representable-etale-quotient-presentation).

Proof:
1. Apply lem-weil-pbc-site-sheafification-sections-local to the quotient presheaf.
   It gives an fppf cover and quotient classes lifting the section. Choose representatives
   `aᵢ : Tᵢ → V` of these classes.
2. By lem-trf-etale-relation-kernel-pair, a pair of maps to `V` has equal quotient images
   exactly when it comes from a unique map to `R` with coordinates `(s,t)`. Applied to
   the map to `V` from the represented pullback and the local lift `aᵢ`, this gives the
   isomorphism `P ×_T Tᵢ ≅ Tᵢ ×_V R`. The fibre-product universal property and
   lem-galois-yoneda-fully-faithful give its uniqueness and its two projection equations.
3. The right projection is étale by lem-weil-pbc-etale-scheme-base-change. Reflexivity
   at `id_V` supplies `e : V → R` with `e ≫ s = e ≫ t = id`, so the projection has a
   section and is surjective.
4. The fppf cover is fpqc: base change to an affine open using
   lem-trf-fppf-covering-base-change, then apply lem-pc-fppf-affine-refinement.
   The lemma lem-weil-pbc-open-preimage-fibre-product identifies the pulled-back open
   with its scheme fibre product; the affine opens of that open subscheme are affine
   opens of the original covering members. These give the fpqc witnesses.
5. Apply lem-galois-fpqc-descend-etale to descend étaleness to `P → T`. Joint
   surjectivity of the fppf cover and the local sections from Step 3 give surjectivity.
6. The singleton étale cover `P → T` and its tautological map `P → V` lift the original
   section. No diagonal representability or algebraic-space assumption is used. -/
theorem representable_etale_quotient_presentation {S : Scheme.{u}} {R V : Over S}
    (s t : R ⟶ V) [Mono (prod.lift s t)]
    (hrel : ∀ T : Over S, Equivalence (fun a b : T ⟶ V ↦
      ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b))
    [Etale s.left] [Etale t.left]
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ F.obj)
    (hη : ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun g : F.obj ⟶ G.obj ↦ η ≫ g))
    (hrep : AlgebraicSpace.IsRepresentable
      (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η)) :
    ∀ (T : Over S) (x : F.obj.obj (op T)),
      (∀ (P : Over S) (p : P ⟶ T) (b : P ⟶ V),
        IsPullback (yoneda.map b) (yoneda.map p)
          (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η) (yonedaEquiv.symm x) →
        Etale p.left ∧ Surjective p.left ∧
          ∃ (I : Type (u + 1)) (T' : I → Over S) (f : ∀ i, T' i ⟶ T)
            (a : ∀ i, T' i ⟶ V),
            Presieve.ofArrows (fun i ↦ (T' i).left) (fun i ↦ (f i).left) ∈
              Scheme.fppfPrecoverage T.left ∧
            ∀ i,
              (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η).app (op (T' i)) (a i) =
                F.obj.map (f i).op x ∧
              ∃! e : pullback p (f i) ≅ pullback (a i) t,
                e.hom ≫ pullback.fst (a i) t = pullback.snd p (f i) ∧
                e.hom ≫ pullback.snd (a i) t ≫ s = pullback.fst p (f i) ≫ b) ∧
      (∃ (I : Type (u + 1)) (E : I → Over S) (g : ∀ i, E i ⟶ T)
        (b : ∀ i, E i ⟶ V),
        Presieve.ofArrows (fun i ↦ (E i).left) (fun i ↦ (g i).left) ∈
          Scheme.etalePrecoverage T.left ∧
        ∀ i, (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η).app (op (E i)) (b i) =
          F.obj.map (g i).op x) := by
  classical
  let q := coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η
  have hR := etale_relation_kernel_pair s t hrel F η hη
  intro T x
  obtain ⟨I, W, f, a, hf, ha⟩ := local_lifts s t F η hη T x
  have ha' (i : I) : yoneda.map (a i) ≫ q = yoneda.map (f i) ≫ yonedaEquiv.symm x := by
    apply yonedaEquiv.injective
    simp only [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    change q.app (op (W i)) (a i) = F.obj.map (f i).op x
    exact ha i
  have hmain (P : Over S) (p : P ⟶ T) (b : P ⟶ V)
      (hP : IsPullback (yoneda.map b) (yoneda.map p) q (yonedaEquiv.symm x)) :
      Etale p.left ∧ Surjective p.left ∧
        ∀ i, ∃! e : pullback p (f i) ≅ pullback (a i) t,
          e.hom ≫ pullback.fst (a i) t = pullback.snd p (f i) ∧
          e.hom ≫ pullback.snd (a i) t ≫ s = pullback.fst p (f i) ≫ b := by
    have hm (i : I) := local_model s t q (yonedaEquiv.symm x) hR p b hP
      (f i) (a i) (ha' i)
    have het (i : I) : Etale (pullback.snd p (f i)).left := by
      obtain ⟨e, he, -⟩ := hm i
      have : Etale (pullback.fst (a i) t).left :=
        MorphismProperty.of_isPullback
          (((IsPullback.of_hasPullback (a i) t).flip).map (Over.forget S))
          (inferInstanceAs (Etale t.left))
      have heq := congrArg (fun k ↦ k.left) he.1
      change e.hom.left ≫ (pullback.fst (a i) t).left =
        (pullback.snd p (f i)).left at heq
      rw [← heq]
      infer_instance
    have hep : Etale p.left := by
      apply etale_of_fpqc_cover p.left (fun i ↦ (W i).left) (fun i ↦ (f i).left)
        (Scheme.fppfPrecoverage_le_fpqcPrecoverage _ hf)
      intro i
      let hp := (IsPullback.of_hasPullback p (f i)).map (Over.forget S)
      have : Etale (pullback.snd p (f i)).left := het i
      have heq : hp.isoPullback.inv ≫ (pullback.snd p (f i)).left =
          pullback.snd p.left (f i).left := hp.isoPullback_inv_snd
      rw [← heq]
      infer_instance
    have hsurj : Surjective p.left := by
      constructor
      intro z
      obtain ⟨i, y, hy⟩ := ((Scheme.ofArrows_mem_precoverage_iff _).mp hf).1 z
      let l := yoneda.preimage (hP.lift (yoneda.map (a i)) (yoneda.map (f i)) (ha' i))
      have hl : l ≫ p = f i := by
        apply yoneda.map_injective
        simp [l]
      refine ⟨l.left y, ?_⟩
      have hl' := congrArg (fun k ↦ k.left) hl
      exact (congrArg (fun k : (W i).left ⟶ T.left ↦ k y) hl').trans hy
    exact ⟨hep, hsurj, hm⟩
  refine ⟨?_, ?_⟩
  · intro P p b hP
    obtain ⟨hep, hsp, hm⟩ := hmain P p b hP
    exact ⟨hep, hsp, I, W, f, a, hf, fun i ↦ ⟨ha i, hm i⟩⟩
  · obtain ⟨P, p, b', hP, -⟩ := hrep T (yonedaEquiv.symm x)
    let b := yoneda.preimage b'
    have hb : yoneda.map b = b' := yoneda.map_preimage b'
    rw [← hb] at hP
    obtain ⟨hep, hsp, -⟩ := hmain P p b hP
    refine ⟨PUnit.{u + 2}, fun _ ↦ P, fun _ ↦ p, fun _ ↦ b, ?_, ?_⟩
    · rw [Presieve.ofArrows_pUnit]
      exact (Scheme.singleton_mem_precoverage_iff _ _).mpr ⟨hsp.surj, hep⟩
    · intro i
      have hw := congrArg yonedaEquiv hP.w
      simp only [yonedaEquiv_comp, yonedaEquiv_yoneda_map] at hw
      exact hw

end AlgebraicGeometry.Scheme
