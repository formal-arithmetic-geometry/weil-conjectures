/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S8
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Irreducible
import Sheaf.AlgebraicGeometry.IntegralNormalizationOpen
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Restricting component normalizations to a dense open

Source: Stacks Project, Varieties, Tag 0GK5, first paragraph; Morphisms, Tags 035K and 0CDV.
(blueprint: lem-weil-pbc-normalization-dense-open-components)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Restricting the normalizations of the reduced components of a finite type scheme along a
dense open immersion gives the normalizations of the reduced components of that open.
Source: Stacks Project, Varieties, Tag 0GK5, first paragraph; Morphisms, Tags 035K and 0CDV.
(blueprint: lem-weil-pbc-normalization-dense-open-components)

Proof: for each component take its pullback along the open immersion. Its projection to the
component is a nonempty open immersion: a dense open in a Noetherian scheme contains every
component generic point. The pullback is therefore integral, and its projection to the open
scheme is closed. Its support is the inverse image of the old component. These inverse images
are exactly the irreducible components of the open, without repetitions: closure of their
images recovers the old components. Normalize each pullback. Normalization commutes with
restriction to opens, since integral closure commutes with localization in the unchanged
function field. The resulting map to the old normalization is an open immersion. It contains
the generic point of that integral normalization, so has dense nonempty image. The comparison
of normalization maps over the old component gives the stated commutative square. -/
theorem exists_normalization_dense_open_components
    (k : Type u) [Field k] (T : Scheme.{u}) (f : T ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (X : Scheme.{u}) (a : X ⟶ T) [IsOpenImmersion a] (ha : DenseRange a)
    (n : ℕ) (C : Fin n → Scheme.{u}) [hC : ∀ i, IsIntegral (C i)]
    (c : ∀ i, C i ⟶ T) [∀ i, IsClosedImmersion (c i)]
    (hi : Function.Injective (fun i ↦ Set.range (c i)))
    (hc : ∀ Z : Set T, Z ∈ irreducibleComponents T ↔ ∃ i, Set.range (c i) = Z) :
    ∃ (D : Fin n → Scheme.{u}) (hD : ∀ i, IsIntegral (D i))
      (d : ∀ i, D i ⟶ X)
      (j : ∀ i, @Scheme.normalization (D i) (hD i) ⟶ (C i).normalization),
      (∀ i, IsClosedImmersion (d i) ∧ Set.range (d i) ∈ irreducibleComponents X) ∧
      Function.Injective (fun i ↦ Set.range (d i)) ∧
      (∀ Z ∈ irreducibleComponents X, ∃ i, Set.range (d i) = Z) ∧
      ∀ i, IsOpenImmersion (j i) ∧ DenseRange (j i) ∧
        Nonempty (@Scheme.normalization (D i) (hD i)) ∧
        @Scheme.fromNormalization (D i) (hD i) ≫ d i ≫ a =
          j i ≫ (C i).fromNormalization ≫ c i := by
  classical
  have hfinite : (irreducibleComponents T).Finite := by
    have he : irreducibleComponents T = Set.range (fun i ↦ Set.range (c i)) := by
      ext Z
      exact hc Z
    rw [he]
    exact Set.finite_range _
  have hcomp (i) : Set.range (c i) ∈ irreducibleComponents T := (hc _).mpr ⟨i, rfl⟩
  have hmeet (i) : (Set.range (c i) ∩ Set.range a).Nonempty := by
    let W : Set T := (⋃₀ (irreducibleComponents T \ {Set.range (c i)}))ᶜ
    have hwcl : closure W = Set.range (c i) :=
      closure_sUnion_irreducibleComponents_sdiff_singleton hfinite _ (hcomp i)
    have hwo : IsOpen W := by
      have hclosed : IsClosed (⋃₀ (irreducibleComponents T \ {Set.range (c i)})) := by
        simpa only [Set.sUnion_eq_biUnion] using
          hfinite.sdiff.isClosed_biUnion
            (fun Z hZ ↦ isClosed_of_mem_irreducibleComponents Z hZ.1)
      exact hclosed.isOpen_compl
    have hwne : W.Nonempty := by
      by_contra h
      have : Set.range (c i) = ∅ := by rw [← hwcl, Set.not_nonempty_iff_eq_empty.mp h,
        closure_empty]
      exact (hcomp i).1.nonempty.ne_empty this
    obtain ⟨x, hx⟩ := ha.exists_mem_open hwo hwne
    exact ⟨a x, hwcl ▸ subset_closure hx, Set.mem_range_self x⟩
  let D : Fin n → Scheme.{u} := fun i ↦ pullback (c i) a
  let d : ∀ i, D i ⟶ X := fun i ↦ pullback.snd (c i) a
  let r : ∀ i, D i ⟶ C i := fun i ↦ pullback.fst (c i) a
  have hDne (i) : Nonempty (D i) := by
    obtain ⟨t, ⟨z, hz⟩, x, hx⟩ := hmeet i
    obtain ⟨y, _, _⟩ := Scheme.Pullback.exists_preimage_pullback z x (hz.trans hx.symm)
    exact ⟨y⟩
  have hD (i) : IsIntegral (D i) := by
    have : Nonempty (D i) := hDne i
    exact isIntegral_of_isOpenImmersion (r i)
  have hrange (i) : Set.range (d i) = a ⁻¹' Set.range (c i) :=
    Scheme.Pullback.range_snd (c i) a
  have hcomponents (i) : Set.range (d i) ∈ irreducibleComponents X := by
    rw [hrange]
    exact preimage_mem_irreducibleComponents (hcomp i) a.isOpenEmbedding (hmeet i)
  have hclosure (i) : closure (a '' Set.range (d i)) = Set.range (c i) := by
    rw [hrange]
    exact closure_image_preimage_of_isPreirreducible a a.isOpenEmbedding.isOpenMap _
      (by simpa [← hrange] using Set.range_nonempty (d i)) (hcomp i).1.2
      (isClosed_of_mem_irreducibleComponents _ (hcomp i))
  have : ∀ i, IsIntegral (D i) := hD
  choose j hj using fun i ↦ exists_integral_normalization_open k (C i) (D i)
    (c i ≫ f) (r i)
  refine ⟨D, hD, d, j, (fun i ↦ ⟨inferInstance, hcomponents i⟩), ?_, ?_, ?_⟩
  · intro i l hil
    apply hi
    change Set.range (c i) = Set.range (c l)
    change Set.range (d i) = Set.range (d l) at hil
    rw [← hclosure i, ← hclosure l, hil]
  · intro Z hZ
    obtain ⟨W, hW, hZW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      (closure (a '' Z)) ((hZ.1.image a a.continuous.continuousOn).closure)
    obtain ⟨i, rfl⟩ := (hc W).mp hW
    have hsub : Z ⊆ Set.range (d i) := by
      rw [hrange]
      exact fun x hx ↦ hZW (subset_closure (Set.mem_image_of_mem a hx))
    exact ⟨i, Set.Subset.antisymm (hZ.2 (hcomponents i).1 hsub) hsub⟩
  · intro i
    have : Nonempty (D i).normalization := inferInstance
    refine ⟨(hj i).1, (hj i).2.1, inferInstance, ?_⟩
    calc
      _ = (D i).fromNormalization ≫ r i ≫ c i := by
        rw [show d i ≫ a = r i ≫ c i from (pullback.condition).symm]
      _ = _ := by
        simpa only [Category.assoc] using
          congrArg (fun t ↦ t ≫ c i) (hj i).2.2.symm

end AlgebraicGeometry
