/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Gluing

/-! # The étale relation associated to a scheme descent cocycle

Source: Stacks Project, Descent, Tag 023W, definition-descent-datum-for-family-of-morphisms;
Groupoids, Tag 022P, definition-equivalence-relation; the input to Spaces, Tag 02WW,
theorem-presentation (blueprint: lem-trf-scheme-descent-cocycle-etale-relation).

The abbreviations only name the fibre products, projections and coproduct maps displayed
in the statement. The diagonal and cocycle hypotheses are expressed on all test schemes.
By the fibre-product universal property these are exactly the identities after pulling
back to the diagonal and to triple overlaps, respectively.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.SchemeDescentCocycle

variable {I : Type u} {S : Scheme.{u}} {U X : I → Scheme.{u}}
    (u : ∀ i, U i ⟶ S) (f : ∀ i, X i ⟶ U i)

/-- The specified iterated fibre product `Rᵢⱼ = Xᵢ ×[Uᵢ] (Uᵢ ×[S] Uⱼ)`.
Source: Stacks, Descent, Tag 023W (blueprint: lem-trf-scheme-descent-cocycle-etale-relation). -/
noncomputable abbrev overlap (i j : I) : Scheme.{u} :=
  pullback (f i) (pullback.fst (u i) (u j))

/-- The projection `pᵢ : Rᵢⱼ ⟶ Xᵢ`.
Source: Stacks, Descent, Tag 023W (blueprint: lem-trf-scheme-descent-cocycle-etale-relation). -/
noncomputable abbrev projection (i j : I) : overlap u f i j ⟶ X i :=
  pullback.fst (f i) (pullback.fst (u i) (u j))

/-- The other base coordinate `Rᵢⱼ ⟶ Uⱼ`; the first is `projection u f i j ≫ f i`.
Source: Stacks, Descent, Tag 023W (blueprint: lem-trf-scheme-descent-cocycle-etale-relation). -/
noncomputable abbrev otherBase (i j : I) : overlap u f i j ⟶ U j :=
  pullback.snd (f i) (pullback.fst (u i) (u j)) ≫ pullback.snd (u i) (u j)

/-- The canonical structure map `V = ∐ Xᵢ ⟶ S`.
Source: Stacks, Descent, Tag 023W (blueprint: lem-trf-scheme-descent-cocycle-etale-relation). -/
noncomputable abbrev structureMap : (∐ X) ⟶ S :=
  Sigma.desc (fun i ↦ f i ≫ u i)

/-- The source map on the specified coproduct `R = ∐ Rᵢⱼ`.
Source: Stacks, Descent, Tag 023W (blueprint: lem-trf-scheme-descent-cocycle-etale-relation). -/
noncomputable abbrev sourceMap : (∐ fun ij : I × I ↦ overlap u f ij.1 ij.2) ⟶ ∐ X :=
  Sigma.desc (fun ij ↦ projection u f ij.1 ij.2 ≫ Sigma.ι X ij.1)

/-- The target map induced by the given transition isomorphisms.
Source: Stacks, Descent, Tag 023W (blueprint: lem-trf-scheme-descent-cocycle-etale-relation). -/
noncomputable abbrev targetMap
    (θ : ∀ i j, overlap u f i j ≅ overlap u f j i) :
    (∐ fun ij : I × I ↦ overlap u f ij.1 ij.2) ⟶ ∐ X :=
  Sigma.desc (fun ij ↦ (θ ij.1 ij.2).hom ≫ projection u f ij.2 ij.1 ≫ Sigma.ι X ij.2)

private theorem overlap_condition (i j : I) :
    projection u f i j ≫ f i ≫ u i = otherBase u f i j ≫ u j := by
  simp only [projection, otherBase, pullback.condition_assoc,
    Category.assoc, pullback.condition]

private noncomputable def overlapLift {T : Scheme.{u}} (i j : I)
    (a : T ⟶ X i) (b : T ⟶ U j) (h : a ≫ f i ≫ u i = b ≫ u j) :
    T ⟶ overlap u f i j :=
  pullback.lift a (pullback.lift (a ≫ f i) b h) (by simp)

@[reassoc (attr := simp)]
private theorem overlapLift_projection {T : Scheme.{u}} (i j : I)
    (a : T ⟶ X i) (b : T ⟶ U j) (h) :
    overlapLift u f i j a b h ≫ projection u f i j = a := by
  simp [overlapLift, projection]

@[reassoc (attr := simp)]
private theorem overlapLift_otherBase {T : Scheme.{u}} (i j : I)
    (a : T ⟶ X i) (b : T ⟶ U j) (h) :
    overlapLift u f i j a b h ≫ otherBase u f i j = b := by
  simp [overlapLift, otherBase]

private theorem overlap_hom_ext {T : Scheme.{u}} (i j : I)
    (a b : T ⟶ overlap u f i j)
    (h₁ : a ≫ projection u f i j = b ≫ projection u f i j)
    (h₂ : a ≫ otherBase u f i j = b ≫ otherBase u f i j) : a = b := by
  apply pullback.hom_ext h₁
  apply pullback.hom_ext
  · simpa only [Category.assoc, ← pullback.condition] using congrArg (· ≫ f i) h₁
  · exact h₂

@[reassoc (attr := simp)]
private theorem ι_sourceMap (i j : I) :
    Sigma.ι (fun ij : I × I ↦ overlap u f ij.1 ij.2) (i, j) ≫ sourceMap u f =
      projection u f i j ≫ Sigma.ι X i := by
  simp [sourceMap]

@[reassoc (attr := simp)]
private theorem ι_targetMap (θ : ∀ i j, overlap u f i j ≅ overlap u f j i) (i j : I) :
    Sigma.ι (fun ij : I × I ↦ overlap u f ij.1 ij.2) (i, j) ≫ targetMap u f θ =
      (θ i j).hom ≫ projection u f j i ≫ Sigma.ι X j := by
  simp [targetMap]

private theorem maps_etale [∀ i, Etale (u i)]
    (θ : ∀ i j, overlap u f i j ≅ overlap u f j i) :
    Etale (sourceMap u f) ∧ Etale (targetMap u f θ) := by
  constructor
  · apply IsZariskiLocalAtSource.sigmaDesc (P := @Etale)
    intro ij
    infer_instance
  · apply IsZariskiLocalAtSource.sigmaDesc (P := @Etale)
    intro ij
    infer_instance

private theorem maps_over
    (θ : ∀ i j, overlap u f i j ≅ overlap u f j i)
    (hbase : ∀ i j,
      (θ i j).hom ≫ projection u f j i ≫ f j = otherBase u f i j ∧
      (θ i j).hom ≫ otherBase u f j i = projection u f i j ≫ f i) :
    sourceMap u f ≫ structureMap u f = targetMap u f θ ≫ structureMap u f := by
  apply Sigma.hom_ext
  rintro ⟨i, j⟩
  simpa only [Category.assoc, ι_sourceMap_assoc, ι_targetMap_assoc,
    structureMap, Sigma.ι_desc] using
    (overlap_condition u f i j).trans (congrArg (· ≫ u j) (hbase i j).1).symm

private theorem hom_ext_on_sigma {J : Type u} {F : J → Scheme.{u}}
    {T Y : Scheme.{u}} (g : T ⟶ ∐ F) (a b : T ⟶ Y)
    (h : ∀ (i : J) (Z : Scheme.{u}) (p : Z ⟶ T) (q : Z ⟶ F i),
      p ≫ g = q ≫ Sigma.ι F i → p ≫ a = p ≫ b) : a = b := by
  apply Scheme.Cover.hom_ext ((sigmaOpenCover F).pullback₁ g)
  intro i
  exact h i _ _ _ (pullback.condition)

private theorem component_ext
    (θ : ∀ i j, overlap u f i j ≅ overlap u f j i)
    (hbase : ∀ i j,
      (θ i j).hom ≫ projection u f j i ≫ f j = otherBase u f i j ∧
      (θ i j).hom ≫ otherBase u f j i = projection u f i j ≫ f i)
    {Z : Scheme.{u}} {i j k l : I}
    (a : Z ⟶ overlap u f i j) (b : Z ⟶ overlap u f k l)
    (hs : a ≫ projection u f i j ≫ Sigma.ι X i =
      b ≫ projection u f k l ≫ Sigma.ι X k)
    (ht : a ≫ (θ i j).hom ≫ projection u f j i ≫ Sigma.ι X j =
      b ≫ (θ k l).hom ≫ projection u f l k ≫ Sigma.ι X l) :
    a ≫ Sigma.ι (fun ij : I × I ↦ overlap u f ij.1 ij.2) (i, j) =
      b ≫ Sigma.ι (fun ij : I × I ↦ overlap u f ij.1 ij.2) (k, l) := by
  classical
  by_cases hi : i = k
  · subst k
    by_cases hj : j = l
    · subst l
      have hs' : a ≫ projection u f i j = b ≫ projection u f i j := by
        apply (cancel_mono (Sigma.ι X i)).mp
        simpa only [Category.assoc] using hs
      have ht' : a ≫ (θ i j).hom ≫ projection u f j i =
          b ≫ (θ i j).hom ≫ projection u f j i := by
        apply (cancel_mono (Sigma.ι X j)).mp
        simpa only [Category.assoc] using ht
      have hab : a = b := overlap_hom_ext u f i j a b hs' (by
        simpa only [Category.assoc, (hbase i j).1] using congrArg (· ≫ f j) ht')
      rw [hab]
    · have : IsEmpty Z := isEmpty_of_commSq_sigmaι_of_ne
        (g := X) (a := a ≫ (θ i j).hom ≫ projection u f j i)
        (b := b ≫ (θ i l).hom ≫ projection u f l i)
        ⟨by simpa only [Category.assoc] using ht⟩ hj
      exact (isInitialOfIsEmpty (X := Z)).hom_ext _ _
  · have : IsEmpty Z := isEmpty_of_commSq_sigmaι_of_ne
      (g := X) (a := a ≫ projection u f i j) (b := b ≫ projection u f k l)
      ⟨by simpa only [Category.assoc] using hs⟩ hi
    exact (isInitialOfIsEmpty (X := Z)).hom_ext _ _

private theorem endpoints_ext
    (θ : ∀ i j, overlap u f i j ≅ overlap u f j i)
    (hbase : ∀ i j,
      (θ i j).hom ≫ projection u f j i ≫ f j = otherBase u f i j ∧
      (θ i j).hom ≫ otherBase u f j i = projection u f i j ≫ f i)
    {T : Scheme.{u}}
    (a b : T ⟶ ∐ fun ij : I × I ↦ overlap u f ij.1 ij.2)
    (hs : a ≫ sourceMap u f = b ≫ sourceMap u f)
    (ht : a ≫ targetMap u f θ = b ≫ targetMap u f θ) : a = b := by
  apply hom_ext_on_sigma a a b
  rintro ⟨i, j⟩ Z p ar hp
  apply hom_ext_on_sigma (p ≫ b) (p ≫ a) (p ≫ b)
  rintro ⟨k, l⟩ W q br hq
  have hqa : q ≫ p ≫ a = (q ≫ ar) ≫
      Sigma.ι (fun ij : I × I ↦ overlap u f ij.1 ij.2) (i, j) := by
    rw [hp, Category.assoc]
  rw [hqa, hq]
  apply component_ext u f θ hbase
  · have e : (q ≫ p ≫ a) ≫ sourceMap u f = (q ≫ p ≫ b) ≫ sourceMap u f := by
      simpa only [Category.assoc] using congrArg (fun x ↦ (q ≫ p) ≫ x) hs
    rw [hqa, hq] at e
    simpa only [Category.assoc, ι_sourceMap] using e
  · have e : (q ≫ p ≫ a) ≫ targetMap u f θ = (q ≫ p ≫ b) ≫ targetMap u f θ := by
      simpa only [Category.assoc] using congrArg (fun x ↦ (q ≫ p) ≫ x) ht
    rw [hqa, hq] at e
    simpa only [Category.assoc, ι_targetMap] using e

/-- An étale scheme descent cocycle gives an étale equivalence relation.
Source: Stacks, Descent, Tag 023W, definition-descent-datum-for-family-of-morphisms;
Groupoids, Tag 022P, definition-equivalence-relation; input to Spaces, Tag 02WW
(blueprint: lem-trf-scheme-descent-cocycle-etale-relation).

Here `hbase` interchanges both base coordinates. The diagonal hypothesis is tested on
maps whose two base coordinates agree. In `hcocycle`, `a`, `b`, `c` are the three overlap
points on one triple overlap: the source of `b` is the transported source of `a`, the
source of `c` is the source of `a`, and the last base coordinate agrees for `b` and `c`.
The conclusion is equality of the two transported points. The remaining base coordinates
already agree by `hbase`, so this is the full triple-overlap cocycle, by Yoneda.

Proof plan (the six steps of the node):
1. Use lem-weil-pbc-scheme-coproduct-family and def-pc-fibre-product to construct the
   displayed maps. Identify each iterated overlap with `Xᵢ ×[S] Uⱼ`; base interchange
   identifies the transported point's base coordinate with the other coordinate.
2. Each component projection is étale by lem-weil-pbc-etale-scheme-base-change. Coproduct
   inclusions and transition isomorphisms are open immersions (def-weil-open-immersion).
   Apply lem-weil-pbc-etale-composition-cancellation and then
   lem-weil-pbc-etale-local-on-source to obtain étaleness of both coproduct maps.
3. For any two test points of `V`, partition the test scheme by the disjoint opens where
   they lie in components `i`, `j`. A lift to `Rᵢⱼ` has forced coordinates: its source
   point and the base of its target point. Fibre-product uniqueness and
   lem-weil-pbc-scheme-morphism-gluing give global uniqueness, hence the monomorphism.
4. On each open component of a test point, the diagonal identity supplies its reflexive
   arrow. Glue these arrows using lem-weil-pbc-scheme-morphism-gluing.
5. On the disjoint component partition, the `(i,j,i)` cocycle and diagonal identity show
   that the reverse transition reverses endpoints. Glue to prove symmetry.
6. Partition by three endpoint components. The `(i,j,k)` cocycle produces the composite
   arrow on each piece. Glue to prove transitivity. These partitions use
   lem-weil-pbc-scheme-coproduct-family and def-weil-open-immersion throughout, so the
   argument also applies to disconnected test schemes and empty covering families. -/
theorem etale_relation
    [hu : ∀ i, Etale (u i)]
    (hcover : ∀ x : S, ∃ (i : I) (y : U i), u i y = x)
    (θ : ∀ i j, overlap u f i j ≅ overlap u f j i)
    (hbase : ∀ i j,
      (θ i j).hom ≫ projection u f j i ≫ f j = otherBase u f i j ∧
      (θ i j).hom ≫ otherBase u f j i = projection u f i j ≫ f i)
    (hdiagonal : ∀ (T : Scheme.{u}) (i : I) (a : T ⟶ overlap u f i i),
      a ≫ projection u f i i ≫ f i = a ≫ otherBase u f i i →
      a ≫ (θ i i).hom ≫ projection u f i i = a ≫ projection u f i i)
    (hcocycle : ∀ (T : Scheme.{u}) (i j k : I)
      (a : T ⟶ overlap u f i j) (b : T ⟶ overlap u f j k)
      (c : T ⟶ overlap u f i k),
      a ≫ (θ i j).hom ≫ projection u f j i = b ≫ projection u f j k →
      a ≫ projection u f i j = c ≫ projection u f i k →
      b ≫ otherBase u f j k = c ≫ otherBase u f i k →
      b ≫ (θ j k).hom ≫ projection u f k j = c ≫ (θ i k).hom ≫ projection u f k i) :
    Etale (sourceMap u f) ∧ Etale (targetMap u f θ) ∧
      ∃ h : sourceMap u f ≫ structureMap u f = targetMap u f θ ≫ structureMap u f,
        Mono (pullback.lift (sourceMap u f) (targetMap u f θ) h) ∧
        ∀ T : Over S,
          Equivalence (fun a b : T ⟶ Over.mk (structureMap u f) ↦
            ∃ r : T.left ⟶ ∐ fun ij : I × I ↦ overlap u f ij.1 ij.2,
              r ≫ sourceMap u f = a.left ∧ r ≫ targetMap u f θ = b.left) := by
  classical
  have _hcover := hcover
  obtain ⟨hs, ht⟩ := maps_etale u f θ
  refine ⟨hs, ht, maps_over u f θ hbase, ?_, ?_⟩
  · constructor
    intro Z a b hab
    apply endpoints_ext u f θ hbase a b
    · simpa only [Category.assoc, pullback.lift_fst] using
        congrArg (· ≫ pullback.fst (structureMap u f) (structureMap u f)) hab
    · simpa only [Category.assoc, pullback.lift_snd] using
        congrArg (· ≫ pullback.snd (structureMap u f) (structureMap u f)) hab
  · let R := fun ij : I × I ↦ overlap u f ij.1 ij.2
    let δ (i : I) : X i ⟶ overlap u f i i :=
      overlapLift u f i i (𝟙 _) (f i) (by simp)
    have δ_target (i : I) : δ i ≫ (θ i i).hom ≫ projection u f i i = 𝟙 _ := by
      simpa only [δ, overlapLift_projection] using
        hdiagonal (X i) i (δ i) (by simp [δ])
    let d : (∐ X) ⟶ ∐ R := Sigma.desc (fun i ↦ δ i ≫ Sigma.ι R (i, i))
    have ds : d ≫ sourceMap u f = 𝟙 _ := by
      apply Sigma.hom_ext
      intro i
      simp [d, δ, R]
    have dt : d ≫ targetMap u f θ = 𝟙 _ := by
      apply Sigma.hom_ext
      intro i
      simpa [d, R, Category.assoc] using
        congrArg (· ≫ Sigma.ι X i) (δ_target i)
    have reverse_target (i j : I) :
        (θ i j).hom ≫ (θ j i).hom ≫ projection u f i j = projection u f i j := by
      let c : overlap u f i j ⟶ overlap u f i i :=
        overlapLift u f i i (projection u f i j) (projection u f i j ≫ f i) (by simp)
      have hdiag : c ≫ (θ i i).hom ≫ projection u f i i = projection u f i j := by
        simpa only [c, overlapLift_projection] using
          hdiagonal _ i c (by simp [c])
      have h := hcocycle (overlap u f i j) i j i (𝟙 _) (θ i j).hom c
        (by simp) (by simp [c]) (by simpa [c] using (hbase i j).2)
      simpa only [Category.id_comp] using h.trans hdiag
    let β : (∐ R) ⟶ ∐ R :=
      Sigma.desc (fun ij ↦ (θ ij.1 ij.2).hom ≫ Sigma.ι R (ij.2, ij.1))
    have βs : β ≫ sourceMap u f = targetMap u f θ := by
      apply Sigma.hom_ext
      rintro ⟨i, j⟩
      simp [β, R]
    have βt : β ≫ targetMap u f θ = sourceMap u f := by
      apply Sigma.hom_ext
      rintro ⟨i, j⟩
      simpa [β, R, Category.assoc] using
        congrArg (· ≫ Sigma.ι X i) (reverse_target i j)
    have compose_component {Z : Scheme.{u}} (i j k l : I)
        (a : Z ⟶ overlap u f i j) (b : Z ⟶ overlap u f k l)
        (hab : a ≫ (θ i j).hom ≫ projection u f j i ≫ Sigma.ι X j =
          b ≫ projection u f k l ≫ Sigma.ι X k) :
        ∃ c : Z ⟶ ∐ R,
          c ≫ sourceMap u f = a ≫ projection u f i j ≫ Sigma.ι X i ∧
          c ≫ targetMap u f θ =
            b ≫ (θ k l).hom ≫ projection u f l k ≫ Sigma.ι X l := by
      by_cases hjk : j = k
      · subst k
        have hab' : a ≫ (θ i j).hom ≫ projection u f j i =
            b ≫ projection u f j l := by
          apply (cancel_mono (Sigma.ι X j)).mp
          simpa only [Category.assoc] using hab
        have hcompat : (a ≫ projection u f i j) ≫ f i ≫ u i =
            (b ≫ otherBase u f j l) ≫ u l := by
          calc
            _ = a ≫ otherBase u f i j ≫ u j := by
              simp only [Category.assoc, overlap_condition]
            _ = a ≫ (θ i j).hom ≫ projection u f j i ≫ f j ≫ u j := by
              simpa only [Category.assoc] using
                (congrArg (fun x ↦ a ≫ x ≫ u j) (hbase i j).1).symm
            _ = b ≫ projection u f j l ≫ f j ≫ u j := by
              simpa only [Category.assoc] using congrArg (· ≫ f j ≫ u j) hab'
            _ = _ := by simp only [Category.assoc, overlap_condition]
        let c := overlapLift u f i l (a ≫ projection u f i j)
          (b ≫ otherBase u f j l) hcompat
        have hc := hcocycle Z i j l a b c hab' (by simp [c]) (by simp [c])
        refine ⟨c ≫ Sigma.ι R (i, l), ?_, ?_⟩
        · simp [R, c]
        · simpa only [R, Category.assoc, ι_targetMap] using
            (congrArg (· ≫ Sigma.ι X l) hc).symm
      · have : IsEmpty Z := isEmpty_of_commSq_sigmaι_of_ne
          (g := X) (a := a ≫ (θ i j).hom ≫ projection u f j i)
          (b := b ≫ projection u f k l)
          ⟨by simpa only [Category.assoc] using hab⟩ hjk
        refine ⟨a ≫ Sigma.ι R (i, j), ?_, ?_⟩
        · simp [R]
        · exact (isInitialOfIsEmpty (X := Z)).hom_ext _ _
    intro T
    constructor
    · intro a
      exact ⟨a.left ≫ d, by simp [ds], by simp [dt]⟩
    · intro a b h
      obtain ⟨r, hrs, hrt⟩ := h
      exact ⟨r ≫ β, by simp [βs, hrt], by simp [βt, hrs]⟩
    · intro a b c hab hbc
      obtain ⟨r, hrs, hrt⟩ := hab
      obtain ⟨q, hqs, hqt⟩ := hbc
      let C₁ : T.left.OpenCover := (sigmaOpenCover R).pullback₁ r
      let C₂ (ij : C₁.I₀) : (C₁.X ij).OpenCover := (sigmaOpenCover R).pullback₁ (C₁.f ij ≫ q)
      let C : T.left.OpenCover := C₁.bind C₂
      have local_lift (z : C.I₀) : ∃ v : C.X z ⟶ ∐ R,
          v ≫ sourceMap u f = C.f z ≫ a.left ∧
          v ≫ targetMap u f θ = C.f z ≫ c.left := by
        rcases z with ⟨⟨i, j⟩, ⟨k, l⟩⟩
        let ar : C.X ⟨(i, j), (k, l)⟩ ⟶ overlap u f i j :=
          (C₂ (i, j)).f (k, l) ≫ (sigmaOpenCover R).pullbackHom r (i, j)
        let br : C.X ⟨(i, j), (k, l)⟩ ⟶ overlap u f k l :=
          (sigmaOpenCover R).pullbackHom (C₁.f (i, j) ≫ q) (k, l)
        have har : ar ≫ Sigma.ι R (i, j) = C.f ⟨(i, j), (k, l)⟩ ≫ r := by
          change ((C₂ (i, j)).f (k, l) ≫
            (sigmaOpenCover R).pullbackHom r (i, j)) ≫ Sigma.ι R (i, j) =
            ((C₂ (i, j)).f (k, l) ≫ C₁.f (i, j)) ≫ r
          simpa only [Category.assoc, sigmaOpenCover_f] using
            congrArg (fun x ↦ (C₂ (i, j)).f (k, l) ≫ x)
              ((sigmaOpenCover R).pullbackHom_map r (i, j))
        have hbr : br ≫ Sigma.ι R (k, l) = C.f ⟨(i, j), (k, l)⟩ ≫ q := by
          change (sigmaOpenCover R).pullbackHom (C₁.f (i, j) ≫ q) (k, l) ≫
            Sigma.ι R (k, l) = ((C₂ (i, j)).f (k, l) ≫ C₁.f (i, j)) ≫ q
          simpa only [Category.assoc, sigmaOpenCover_f] using
            (sigmaOpenCover R).pullbackHom_map (C₁.f (i, j) ≫ q) (k, l)
        have hsar : ar ≫ projection u f i j ≫ Sigma.ι X i =
            C.f ⟨(i, j), (k, l)⟩ ≫ a.left := by
          simpa only [R, Category.assoc, ι_sourceMap] using
            (congrArg (· ≫ sourceMap u f) har).trans (by rw [Category.assoc, hrs])
        have htbr : br ≫ (θ k l).hom ≫ projection u f l k ≫ Sigma.ι X l =
            C.f ⟨(i, j), (k, l)⟩ ≫ c.left := by
          simpa only [R, Category.assoc, ι_targetMap] using
            (congrArg (· ≫ targetMap u f θ) hbr).trans (by rw [Category.assoc, hqt])
        have harbr : ar ≫ (θ i j).hom ≫ projection u f j i ≫ Sigma.ι X j =
            br ≫ projection u f k l ≫ Sigma.ι X k := by
          have e : (ar ≫ Sigma.ι R (i, j)) ≫ targetMap u f θ =
              (br ≫ Sigma.ι R (k, l)) ≫ sourceMap u f := by
            rw [har, hbr, Category.assoc, Category.assoc, hrt, hqs]
          simpa only [R, Category.assoc, ι_targetMap, ι_sourceMap] using e
        obtain ⟨v, hvs, hvt⟩ := compose_component i j k l ar br harbr
        exact ⟨v, hvs.trans hsar, hvt.trans htbr⟩
      choose v hvs hvt using local_lift
      have hv : ∀ x y, pullback.fst (C.f x) (C.f y) ≫ v x =
          pullback.snd (C.f x) (C.f y) ≫ v y := by
        intro x y
        apply endpoints_ext u f θ hbase
        · simp only [Category.assoc, hvs, pullback.condition_assoc]
        · simp only [Category.assoc, hvt, pullback.condition_assoc]
      refine ⟨Scheme.Cover.glueMorphisms C v hv, ?_, ?_⟩
      · apply Scheme.Cover.hom_ext C
        intro x
        simp only [← Category.assoc, Scheme.Cover.ι_glueMorphisms, hvs]
      · apply Scheme.Cover.hom_ext C
        intro x
        simp only [← Category.assoc, Scheme.Cover.ι_glueMorphisms, hvt]

end AlgebraicGeometry.SchemeDescentCocycle
