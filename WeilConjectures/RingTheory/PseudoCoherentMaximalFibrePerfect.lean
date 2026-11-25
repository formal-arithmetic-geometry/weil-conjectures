/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.RingTheory.RingPseudoCoherent
import WeilConjectures.Algebra.Homology.FreeComplexResidueTensorExact
import WeilConjectures.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect

/-!
# Perfectness detected by uniformly bounded maximal residue fibres

A pseudo-coherent complex whose derived fibres at all maximal ideals have cohomology in a fixed
interval `[a, b]` is perfect, with tor amplitude in `[a, b]`.

## Implementation details

The derived tensor is the existing monoidal structure on the module derived category.
For a maximal ideal, its quotient ring is regarded as an R-module in degree zero.
Vanishing of the underlying R-module cohomology is equivalent to vanishing of the
residue-field cohomology of derived scalar extension.

A bounded-above finite-free model `P` is K-flat, so derived tensors are computed termwise. Outside
`[a, b]`, degree cancellation on a principal neighbourhood of each maximal ideal makes every
module tensor exact, and exactness descends along the principal cover. This gives the tor
amplitude, and `isPerfect_of_pseudoCoherent_finiteTorAmplitude` gives perfectness.

## References

* [Stacks, Tag 068V] ((3) implies (1))
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace DerivedCategory

/-- A pseudo-coherent complex with maximal residue fibres concentrated in the fixed interval
is perfect, and its derived tensor with every module has cohomology in that same interval. -/
theorem isPerfect_and_tensor_homology_vanish_of_maximal_fibres
    {R : Type u} [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    (C : DerivedCategory (ModuleCat.{u} R)) (hC : C.IsPseudoCoherent)
    (a b : ℤ) (hab : a ≤ b)
    (hfibres : ∀ (m : Ideal R), m.IsMaximal → ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((homologyFunctor (ModuleCat.{u} R) i).obj
        (C ⊗ (singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R (R ⧸ m))))) :
    C.IsPerfect ∧ ∀ (M : ModuleCat.{u} R) (i : ℤ), (i < a ∨ b < i) →
      IsZero ((homologyFunctor (ModuleCat.{u} R) i).obj
        (C ⊗ (singleFunctor (ModuleCat.{u} R) 0).obj M)) := by
  obtain ⟨P, c, hPc, hP, ⟨e⟩⟩ := hC
  have : P.IsStrictlyLE c := hPc
  have hPk := CochainComplex.kFlat_of_isStrictlyLE_of_flat P c fun j ↦ by
    have := (hP j).1
    exact (ModuleCat.flat_iff_flat _).2 inferInstance
  let eH (M : ModuleCat.{u} R) (i : ℤ) :
      (homologyFunctor (ModuleCat.{u} R) i).obj
          (C ⊗ (singleFunctor (ModuleCat.{u} R) 0).obj M) ≅
        (((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P).homology i :=
    (homologyFunctor (ModuleCat.{u} R) i).mapIso
      (whiskerRightIso e.symm _ ≪≫ QObjTensorSingleFunctorObjIso P hPk M) ≪≫
      (homologyFunctorFactors _ i).app _
  have htensor (M : ModuleCat.{u} R) (i : ℤ) (hi : i < a ∨ b < i) :
      IsZero ((homologyFunctor (ModuleCat.{u} R) i).obj
        (C ⊗ (singleFunctor (ModuleCat.{u} R) 0).obj M)) := by
    apply IsZero.of_iso _ (eH M i)
    apply CochainComplex.isZero_homology_tensor_of_residue P
      (fun j ↦ (hP j).1) (fun j ↦ (hP j).2) i
    intro m hm
    exact (hfibres m hm i hi).of_iso (eH (ModuleCat.of R (R ⧸ m)) i).symm
  have hTor : torAmplitudeIn (ModuleCat.{u} R) a b C := by
    intro M
    constructor
    · change (C ⊗ (singleFunctor (ModuleCat.{u} R) 0).obj M).IsGE a
      rw [isGE_iff]
      exact fun i hi ↦ htensor M i (Or.inl hi)
    · change (C ⊗ (singleFunctor (ModuleCat.{u} R) 0).obj M).IsLE b
      rw [isLE_iff]
      exact fun i hi ↦ htensor M i (Or.inr hi)
  obtain ⟨T, ⟨l, r, hT⟩, hfin, hproj, ⟨eT⟩⟩ :=
    isPerfect_of_pseudoCoherent_finiteTorAmplitude C
      ⟨P, c, hPc, hP, ⟨e⟩⟩ ⟨a, b, hab, hTor⟩
  refine ⟨⟨T, l, r, ?_, ?_, fun i ↦ ⟨hproj i, hfin i⟩, ⟨eT.symm⟩⟩, htensor⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi ↦ hT i (Or.inl hi)
  · rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi ↦ hT i (Or.inr hi)

end DerivedCategory
