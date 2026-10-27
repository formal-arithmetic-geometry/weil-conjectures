/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Valuation.ValuationRing
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import WeilConjectures.Mathlib.AlgebraicGeometry.ValuativeCriterion
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Valuative base change lifting two fibre components

Source: Stacks Project, Tag 0GSH, Lemma `lemma-make-base-change`, all four clauses.
(blueprint: lem-trf-valuative-fibre-component-lift)

The reduced integral closures are represented by integral closed immersions with the
specified underlying images. Points of their fibres are kept as points of the actual
scheme-theoretic fibres, with `fiberι` giving their images in the ambient schemes.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicGeometry

private theorem fibre_value {U V : Scheme.{u}} (q : U ⟶ V) (v : V)
    (a : q.fiber v) : q (q.fiberι v a) = v := by
  have h : q.fiberι v a ∈ q ⁻¹' {v} := q.range_fiberι v ▸ Set.mem_range_self a
  exact h

private theorem fibre_point {U V : Scheme.{u}} (q : U ⟶ V) (v : V) (a : U)
    (ha : q a = v) : ∃ b : q.fiber v, q.fiberι v b = a := by
  change a ∈ Set.range (q.fiberι v)
  rw [q.range_fiberι v]
  exact ha

private theorem component_generalization {T : Type*} [TopologicalSpace T] [T0Space T]
    {a b : T} {K : Set T} (hK : K ∈ irreducibleComponents T)
    (ha : IsGenericPoint a K) (hba : b ⤳ a) : b = a := by
  have hsub : K ⊆ closure ({b} : Set T) := by
    rw [← ha.def]
    exact hba.closure_subset
  have heq := Set.Subset.antisymm (hK.2 isIrreducible_singleton.closure hsub) hsub
  exact (show IsGenericPoint b K from heq).eq ha

private theorem component_above {T : Scheme.{u}} (a : T) :
    ∃ (b : T) (K : Set T), K ∈ irreducibleComponents T ∧
      IsGenericPoint b K ∧ b ⤳ a := by
  let K := irreducibleComponent a
  have hK := irreducibleComponent_mem_irreducibleComponents a
  obtain ⟨b, hb⟩ := QuasiSober.sober hK.1 (isClosed_of_mem_irreducibleComponents _ hK)
  exact ⟨b, K, hK, hb, hb.specializes mem_irreducibleComponent⟩

/-- A valuation-ring base change lifts a generic component point in each of the two fibres.

Source: Stacks Project, Tag 0GSH, all four clauses.
(blueprint: lem-trf-valuative-fibre-component-lift)

Here `i : Y ⟶ X` presents the reduced integral closure of `y`; `x` is a point of its
scheme-theoretic fibre, and its image in `X` is `i ((i ≫ f).fiberι s x)`. The point `z`
lies in the generic fibre of `Y ×_S Spec A`; its image under the canonical base-change
closed immersion is `y'`. By the canonical fibre base-change identification this is
exactly `Y_t ×_{Spec κ(t)} Spec κ(t')`. The integral closed immersion `i'` presents
the reduced closure of `y'`, and `x'` is the required point of its special fibre.

Proof:
1. The point `y` specializes to the image of `x`. Apply
   `lem-trf-valuation-ring-specialization-lift`, namely
   `Scheme.exists_valuationSubring_of_specializes` (Stacks 01J8), to obtain a valuation
   ring and `h : Spec A ⟶ X` realizing the specialization. Set `g = h ≫ f`.
2. The pullback universal property (`def-pc-base-change`, `def-pc-fibre-product`) gives
   a section of `X ×_S Spec A ⟶ Spec A`. Since `h` factors through the reduced closure
   `Y`, this section factors through `Y ×_S Spec A`.
3. Choose the generic point of a component of its generic fibre containing the section's
   generic point. Its image in `X` generalizes `y` within `Y_t`, hence equals `y`:
   `y` is the generic point of the irreducible fibre `Y_t`. This gives `z` and `y'`.
4. The section factors through the reduced closure `Y'` of `y'`. Choose the generic
   point `x'` of a component of its special fibre containing the section's closed point.
   Its image in `Y_s` generalizes `x`; maximality of the component of `x` and uniqueness
   of generic points imply equality. These are precisely the final image and component
   conditions (`def-pc-integral-scheme`, `def-pc-scheme-fibre`, `def-sc-generic-point`,
   `def-weil-irreducible-components`). -/
theorem exists_valuative_fibre_component_lift {X S Y : Scheme.{u}} (f : X ⟶ S)
    (y : X) (i : Y ⟶ X) [IsIntegral Y] [IsClosedImmersion i]
    (hY : Set.range i = closure ({y} : Set X)) (s : S) (x : (i ≫ f).fiber s)
    (C : Set ((i ≫ f).fiber s)) (hC : C ∈ irreducibleComponents ((i ≫ f).fiber s))
    (hx : IsGenericPoint x C) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A)
      (g : Spec (CommRingCat.of A) ⟶ S)
      (t' s' : Spec (CommRingCat.of A)),
      IsGenericPoint t' Set.univ ∧ IsClosed ({s'} : Set (Spec (CommRingCat.of A))) ∧
      g t' = f y ∧ g s' = s ∧
      ∃ (z : (pullback.snd (i ≫ f) g).fiber t')
        (D : Set ((pullback.snd (i ≫ f) g).fiber t')),
        D ∈ irreducibleComponents ((pullback.snd (i ≫ f) g).fiber t') ∧
        IsGenericPoint z D ∧
        ∃ y' : (pullback f g : Scheme.{u}),
          (pullback.snd f g) y' = t' ∧ (pullback.fst f g) y' = y ∧
          (pullback.map (i ≫ f) g f g i (𝟙 _) (𝟙 _)
            (Category.comp_id _) ((Category.comp_id g).trans (Category.id_comp g).symm))
            ((pullback.snd (i ≫ f) g).fiberι t' z) = y' ∧
          ∃ (Y' : Scheme.{u}) (_ : IsIntegral Y') (i' : Y' ⟶ pullback f g)
            (_ : IsClosedImmersion i'),
            Set.range i' = closure ({y'} : Set (pullback f g : Scheme.{u})) ∧
            ∃ (x' : (i' ≫ pullback.snd f g).fiber s')
              (E : Set ((i' ≫ pullback.snd f g).fiber s')),
              E ∈ irreducibleComponents ((i' ≫ pullback.snd f g).fiber s') ∧
              IsGenericPoint x' E ∧
              (pullback.fst f g) (i' ((i' ≫ pullback.snd f g).fiberι s' x')) =
                i ((i ≫ f).fiberι s x) := by
  classical
  obtain ⟨y₀, hy₀⟩ := hY.symm ▸ (subset_closure (Set.mem_singleton y))
  have hy₀gen : IsGenericPoint y₀ Set.univ := by
    rw [isGenericPoint_iff_specializes]
    intro a
    simp only [Set.mem_univ, iff_true]
    apply i.isEmbedding.isInducing.specializes_iff.mp
    rw [hy₀, specializes_iff_mem_closure, ← hY]
    exact Set.mem_range_self a
  obtain ⟨A, ρ, hρs, hρt⟩ := Scheme.exists_valuationSubring_of_specializes
    (hy₀gen.specializes (Set.mem_univ ((i ≫ f).fiberι s x)))
  let T : Scheme.{u} := Spec (CommRingCat.of A)
  let t' : T := ⟨⊥, Ideal.isPrime_bot⟩
  let s' : T := IsLocalRing.closedPoint A
  have ht' : IsGenericPoint t' Set.univ := by
    change closure ({t'} : Set (PrimeSpectrum A)) = Set.univ
    rw [PrimeSpectrum.closure_singleton]
    exact PrimeSpectrum.zeroLocus_bot
  have hρt' : ρ t' = y₀ := by
    have h := congrArg (fun k : Spec (.of (AlgebraicClosure (Y.residueField y₀))) ⟶ Y ↦
      k (IsLocalRing.closedPoint _)) hρt
    have he : Spec.map (CommRingCat.ofHom
        (algebraMap A (AlgebraicClosure (Y.residueField y₀))))
        (IsLocalRing.closedPoint _) = t' := by
      apply PrimeSpectrum.ext
      change Ideal.comap (algebraMap A (AlgebraicClosure (Y.residueField y₀)))
        (IsLocalRing.maximalIdeal _) = ⊥
      rw [IsLocalRing.maximalIdeal_eq_bot]
      exact Ideal.comap_bot_of_injective _ Subtype.val_injective
    simp only [Scheme.Hom.comp_apply, he] at h
    exact h.trans (Y.fromSpecResidueField_apply _ _)
  let g : T ⟶ S := ρ ≫ i ≫ f
  have hgs : g s' = s := by
    dsimp [g, s']
    rw [hρs]
    exact fibre_value (i ≫ f) s x
  have hgt : g t' = f y := by
    change f (i (ρ t')) = f y
    rw [hρt', hy₀]
  let σ : T ⟶ pullback (i ≫ f) g := pullback.lift ρ (𝟙 T) rfl
  have hσ (a : T) : (pullback.snd (i ≫ f) g) (σ a) = a := by
    change (σ ≫ pullback.snd (i ≫ f) g) a = a
    simp [σ]
  have hσfst (a : T) : (pullback.fst (i ≫ f) g) (σ a) = ρ a := by
    change (σ ≫ pullback.fst (i ≫ f) g) a = ρ a
    rw [pullback.lift_fst]
  obtain ⟨zt, hzt⟩ := fibre_point (pullback.snd (i ≫ f) g) t' (σ t') (hσ t')
  obtain ⟨z, D, hD, hz, hzzt⟩ := component_above zt
  let j : pullback (i ≫ f) g ⟶ pullback f g :=
    pullback.map (i ≫ f) g f g i (𝟙 _) (𝟙 _)
      (Category.comp_id _) ((Category.comp_id g).trans (Category.id_comp g).symm)
  let y' := j ((pullback.snd (i ≫ f) g).fiberι t' z)
  have hy't : (pullback.snd f g) y' = t' := by
    change (j ≫ pullback.snd f g) _ = t'
    simp only [j, pullback.lift_snd, Category.comp_id]
    exact fibre_value _ _ z
  have hzy : (pullback.fst (i ≫ f) g)
      ((pullback.snd (i ≫ f) g).fiberι t' z) = y₀ := by
    apply Inseparable.eq
    apply Specializes.antisymm ?_ (hy₀gen.specializes (Set.mem_univ _))
    have h := hzzt.map
      (((pullback.snd (i ≫ f) g).fiberι t' ≫ pullback.fst (i ≫ f) g).continuous)
    change (pullback.fst (i ≫ f) g)
      ((pullback.snd (i ≫ f) g).fiberι t' z) ⤳
      (pullback.fst (i ≫ f) g) ((pullback.snd (i ≫ f) g).fiberι t' zt) at h
    rwa [hzt, hσfst, hρt'] at h
  have hy'y : (pullback.fst f g) y' = y := by
    change (j ≫ pullback.fst f g) _ = y
    simp only [j, pullback.lift_fst, Scheme.Hom.comp_apply, hzy, hy₀]
  refine ⟨A, inferInstance, inferInstance, inferInstance, g, t', s', ht',
    IsLocalRing.isClosed_singleton_closedPoint A, hgt, hgs, z, D, hD, hz,
    y', hy't, hy'y, rfl, ?_⟩
  let I := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure ({y'} : Set (pullback f g : Scheme.{u})), isClosed_closure⟩ :
      TopologicalSpace.Closeds (pullback f g : Scheme.{u}))
  have hI : Set.range I.subschemeι = closure ({y'} : Set (pullback f g : Scheme.{u})) := by
    simp [I]
  let e := I.subschemeι.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hI)
  have : IrreducibleSpace (closure ({y'} : Set (pullback f g : Scheme.{u}))) :=
    Subtype.irreducibleSpace isIrreducible_singleton.closure
  have : IrreducibleSpace I.subscheme := e.irreducibleSpace_iff.mpr inferInstance
  have : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  refine ⟨I.subscheme, inferInstance, I.subschemeι, inferInstance, hI, ?_⟩
  let τ := σ ≫ j
  have hτ (a : T) : (pullback.snd f g) (τ a) = a := by
    change (σ ≫ j ≫ pullback.snd f g) a = a
    simpa [j] using hσ a
  have hy'τ : y' ⤳ τ s' := by
    have h := hzzt.map (((pullback.snd (i ≫ f) g).fiberι t' ≫ j).continuous)
    have h₁ : y' ⤳ τ t' := by
      change j ((pullback.snd (i ≫ f) g).fiberι t' z) ⤳ j (σ t')
      change j ((pullback.snd (i ≫ f) g).fiberι t' z) ⤳
        j ((pullback.snd (i ≫ f) g).fiberι t' zt) at h
      rwa [hzt] at h
    exact h₁.trans ((ht'.specializes (Set.mem_univ s')).map τ.continuous)
  obtain ⟨a, ha⟩ := hI.symm ▸ hy'τ.mem_closure
  have has : (I.subschemeι ≫ pullback.snd f g) a = s' := by
    rw [Scheme.Hom.comp_apply, ha, hτ]
  obtain ⟨aₛ, haₛ⟩ := fibre_point (I.subschemeι ≫ pullback.snd f g) s' a has
  obtain ⟨x', E, hE, hx', hx'aₛ⟩ := component_above aₛ
  refine ⟨x', E, hE, hx', ?_⟩
  let v := I.subschemeι ((I.subschemeι ≫ pullback.snd f g).fiberι s' x')
  have hyv : y ⤳ (pullback.fst f g) v := by
    rw [← hy'y]
    apply Specializes.map _ (pullback.fst f g).continuous
    rw [specializes_iff_mem_closure, ← hI]
    exact Set.mem_range_self _
  obtain ⟨b, hb⟩ := hY.symm ▸ hyv.mem_closure
  have hbs : (i ≫ f) b = s := by
    rw [Scheme.Hom.comp_apply, hb]
    have hc := congrArg (fun k : pullback f g ⟶ S ↦ k v)
      (pullback.condition (f := f) (g := g))
    change f ((pullback.fst f g) v) = g ((pullback.snd f g) v) at hc
    rw [hc]
    have hv : (pullback.snd f g) v = s' := fibre_value _ _ x'
    rw [hv, hgs]
  obtain ⟨bₛ, hbₛ⟩ := fibre_point (i ≫ f) s b hbs
  have hbx : bₛ ⤳ x := by
    apply ((i ≫ f).fiberι s ≫ i).isEmbedding.isInducing.specializes_iff.mp
    have h := hx'aₛ.map
      (((I.subschemeι ≫ pullback.snd f g).fiberι s' ≫
        I.subschemeι ≫ pullback.fst f g).continuous)
    have hτx : (pullback.fst f g) (τ s') = i ((i ≫ f).fiberι s x) := by
      change (σ ≫ j ≫ pullback.fst f g) s' = _
      simp only [j, pullback.lift_fst, pullback.lift_fst_assoc, σ]
      change i (ρ s') = _
      rw [hρs]
    simpa only [Scheme.Hom.comp_apply, hbₛ, hb, haₛ, ha, hτx] using h
  have heq := component_generalization hC hx hbx
  change (pullback.fst f g) v = _
  rw [← hb, ← hbₛ, heq]

end AlgebraicGeometry
