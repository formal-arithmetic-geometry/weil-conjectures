/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: K1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-!
# Criterion for a property of morphisms to descend along fpqc coverings

Source: Stacks Project, Descent, Lemma Tag 02KP
(blueprint: lem-weil-pbc-fpqc-local-on-base-criterion).
-/

/-- A property of morphisms satisfying invariance under isomorphism, flat base change,
Zariski locality on the base, and affine faithfully-flat descent descends along fpqc coverings.
Source: Stacks Project, Descent, Lemma Tag 02KP and Definition Tag 02KO;
Topologies, Definition Tag 022B and Lemma Tag 022E
(blueprint: lem-weil-pbc-fpqc-local-on-base-criterion).

The isomorphism invariance and Zariski locality are encoded by `IsZariskiLocalAtTarget P`.
Its preservation of open restrictions follows from `hflat`, since open immersions are flat.
Thus its two-way locality adds nothing to conditions (0), (1), and (2) of the node.

Proof (the seven steps of the node, expanding the source's omitted details):
1. Reduce by Zariski locality to each affine open `U` of `S` (`def-pc-scheme`).
2. Refine the fpqc family over `U` by finitely many affine opens `V_j` of its members,
   whose images cover `U` (022E and `def-weil-pbc-fpqc-covering`).
3. Their finite disjoint union `U'` is affine (`lem-weil-pbc-affine-morphism-permanence`)
   and maps surjectively to `U`. The component inclusions cover `U'`
   (`lem-weil-pbc-scheme-coproduct-family`), and their stalk maps are isomorphisms
   (`def-weil-open-immersion`), so this map is flat (`def-weil-flat-morphism`) and
   surjective (`def-weil-surjective-morphism`). The empty union is `Spec 0`.
4. Base change each given `P`-morphism to `V_j` by the flat open inclusion using `hflat`.
   Open preimages are fibre products (`lem-weil-pbc-open-preimage-fibre-product`);
   uniqueness (`def-pc-fibre-product`), invariance under isomorphisms, and cartesian
   pasting (`lem-weil-pbc-cartesian-square-pasting`) identify these with the required
   base changes of the restriction of `f` to `U`.
5. Restrict its base change to `U'` to the component images. The component-to-image
   isomorphisms (`lem-weil-pbc-open-immersion-iso-onto-image`), open-preimage fibre
   products, and cartesian pasting identify these restrictions with step 4.
   Isomorphism invariance and Zariski locality on `U'` give `P` for this base change.
6. Apply `hdesc` to the flat surjection `U' ⟶ U` between affine schemes; uniqueness
   of fibre products transports `P` to the chosen pullback if necessary.
7. Every affine restriction of `f` has `P`; the affine opens cover `S`, so Zariski
   locality gives `P f`. -/
theorem fpqc_local_on_base_criterion
    (P : MorphismProperty Scheme.{u})
    (hflat : ∀ {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S),
      Flat g → P f → P (pullback.snd f g))
    [IsZariskiLocalAtTarget P]
    (hdesc : ∀ {S T X : Scheme.{u}} [IsAffine S] [IsAffine T]
      (f : X ⟶ S) (g : T ⟶ S),
      Flat g → Surjective g → P (pullback.snd f g) → P f)
    {S : Scheme.{u}} {Z : Scheme.{u}} (f : Z ⟶ S)
    {ι : Type w} {S' : ι → Scheme.{u}} (g : ∀ i, S' i ⟶ S)
    (hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)
    (H : ∀ i, P (pullback.snd f (g i))) : P f := by
  have affine_case {T X : Scheme.{u}} [IsAffine T]
      (𝒰 : Scheme.Cover.{w} Scheme.fpqcPrecoverage T) (f : X ⟶ T)
      (H : ∀ i, P (pullback.snd f (𝒰.f i))) : P f := by
    obtain ⟨𝒱, φ, hfin, hopen⟩ := QuasiCompactCover.exists_hom 𝒰.forgetQc
    have : Finite 𝒱.cover.I₀ := hfin
    have : Small.{u} 𝒱.cover.I₀ := Countable.toSmall (α := 𝒱.cover.I₀)
    let p : ∐ 𝒱.cover.X ⟶ T := Sigma.desc 𝒱.cover.f
    have : ∀ j, Flat (𝒱.cover.f j) := 𝒱.map_prop
    have : Flat p := inferInstance
    have : Surjective p :=
      Surjective.sigmaDesc_of_union_range_eq_univ 𝒱.cover.iUnion_range
    have : IsAffine (∐ 𝒱.cover.X) := inferInstance
    apply hdesc f p inferInstance inferInstance
    rw [IsZariskiLocalAtTarget.iff_of_openCover (P := P) (sigmaOpenCover _)]
    intro j
    have hsq := (IsPullback.of_hasPullback (pullback.snd f p)
      (Sigma.ι 𝒱.cover.X j)).paste_horiz (IsPullback.of_hasPullback f p)
    have hj : Sigma.ι 𝒱.cover.X j ≫ p = 𝒱.cover.f j := Sigma.ι_desc _ _
    rw [hj, ← φ.w₀ j] at hsq
    have : IsOpenImmersion (φ.h₀ j) := hopen j
    have hb := hflat (pullback.snd f (𝒰.f (φ.s₀ j))) (φ.h₀ j)
      inferInstance (H (φ.s₀ j))
    have hr := IsPullback.of_right' hsq (IsPullback.of_hasPullback f (𝒰.f (φ.s₀ j)))
    rwa [← P.cancel_left_of_respectsIso hr.isoPullback.hom,
      hr.isoPullback_hom_snd] at hb
  let 𝒰 : Scheme.Cover.{w} Scheme.fpqcPrecoverage S :=
    { I₀ := ι, X := S', f := g, mem₀ := hg }
  refine IsZariskiLocalAtTarget.of_openCover S.affineCover fun i ↦ ?_
  apply affine_case (𝒰.pullback₁ (S.affineCover.f i))
  intro j
  have hsq := (IsPullback.of_hasPullback
    (pullback.snd f (S.affineCover.f i))
    (pullback.fst (S.affineCover.f i) (g j))).paste_horiz
    (IsPullback.of_hasPullback f (S.affineCover.f i))
  rw [pullback.condition] at hsq
  exact IsZariskiLocalAtTarget.of_isPullback
    (IsPullback.of_right' hsq (IsPullback.of_hasPullback f (g j))) (H j)

end AlgebraicGeometry
