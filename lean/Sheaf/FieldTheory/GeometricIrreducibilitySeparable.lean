/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q74
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.FieldTheory.AlgebraicClosure
import Sheaf.FieldTheory.SeparableTensorAlgebraicClosure
import Sheaf.AlgebraicGeometry.GeometricallyIrreducibleAlgebraClosure
import Sheaf.FieldTheory.FieldExtensionGeometricallyIrreducible
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra

/-!
# Geometric irreducibility and separable elements

Source: Stacks Project, Algebra, Tag 0G33 (lemma-geometrically-irreducible-separable-elements),
equivalence of (1) and (2) (blueprint: lem-zl-geometric-irreducibility-separable).
-/

@[expose] public section

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

private theorem subsingleton_of_irreducible_pi
    (ι Ω : Type u) [Field Ω] [IrreducibleSpace (PrimeSpectrum (ι → Ω))] :
    Subsingleton ι := by
  classical
  refine ⟨fun i j ↦ by
    by_contra hij
    let e : ι → Ω := fun a ↦ if a = i then 1 else 0
    have hp := (PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical (R := ι → Ω)).mp
      inferInstance
    have hz : e * (1 - e) = 0 := by
      ext a
      by_cases ha : a = i <;> simp [e, ha]
    rcases hp.mem_or_mem (hz ▸ (nilradical (ι → Ω)).zero_mem) with he | he
    · have hh := (mem_nilradical.mp he).map (Pi.evalRingHom _ i)
      simp [e] at hh
    · have hh := (mem_nilradical.mp he).map (Pi.evalRingHom _ j)
      simp [e, Ne.symm hij] at hh⟩

/-- A field extension is geometrically irreducible exactly when its separably algebraic
elements over the base field already lie in the base field.
Source: Stacks Project, Algebra, Tag 0G33 (lemma-geometrically-irreducible-separable-elements),
equivalence of (1) and (2) (blueprint: lem-zl-geometric-irreducibility-separable).

Proof:
1. For a separable element α, the simple intermediate field E = k(α) is finite and
   separable by Mathlib's simple-adjoin lemmas. Geometric irreducibility descends from K
   to E along the injective inclusion by
   `lem-zl-geometric-irreducibility-subalgebra-colimit`.
2. Apply `lem-pc-separable-tensor-algebraic-closure` over Ω = AlgebraicClosure E.
   Every intermediate field of E is separable over k and hence separably generated:
   choose a transcendence basis and use separability up the tower. The tensor product
   E ⊗[k] Ω has irreducible spectrum and is a product indexed by the k-embeddings E → Ω.
   If two indices differ, their characteristic idempotent and its complement multiply
   to zero, but neither is nilpotent, contradicting primality of the nilradical.
   Thus there is at most one embedding. Mathlib's embedding criterion makes E/k purely
   inseparable; its separability then makes k → E surjective, so α belongs to k.
3. Conversely, let A be the algebraic closure of k in K. Transitivity of integrality
   shows that every element of K algebraic over A belongs to A. Apply
   `lem-zl-field-extension-algebraically-closed-geometric` to obtain geometric
   irreducibility of K/A.
4. Every element of A is integral over k, and separability maps along A → K. The
   hypothesis therefore puts each separable element of A in k. Mathlib's defining
   criterion `isPurelyInseparable_iff` makes A/k purely inseparable.
5. The proved instance `Algebra.IsUniversalHomeomorphism.of_isPurelyInseparable`
   makes Spec A → Spec k a universal homeomorphism. After any field base change its
   source is homeomorphic to the one-point spectrum of that field, hence irreducible.
6. Compose the geometrically irreducible morphisms Spec K → Spec A and Spec A → Spec k
   using Mathlib's `GeometricallyIrreducible.comp`. The field-tower identity identifies
   their composite with Spec K → Spec k.
-/
theorem geometricallyIrreducible_iff_separableElements_mem
    (k K : Type u) [Field k] [Field K] [Algebra k K] :
    GeometricallyIrreducible
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) ↔
      ∀ α : K, IsSeparable k α → α ∈ Set.range (algebraMap k K) := by
  classical
  constructor
  · intro h α hα
    let E := IntermediateField.adjoin k {α}
    have hEsep : Algebra.IsSeparable k E :=
      (IntermediateField.isSeparable_adjoin_iff_isSeparable k K).mpr (by
        intro x hx
        simpa only [Set.mem_singleton_iff.mp hx] using hα)
    let := hEsep
    let : FiniteDimensional k E :=
      IntermediateField.adjoin.finiteDimensional hα.isIntegral
    have hE : GeometricallyIrreducible
        (Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
      geometricallyIrreducible_spec_of_injective E.val E.val.injective h
    have hsep : Algebra.IsSeparableExtension k E := by
      intro F _
      let : Algebra.IsSeparable k F := Algebra.IsSeparable.of_algHom k E F.val
      obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k F
      exact ⟨s, hs, inferInstance⟩
    let Ω := AlgebraicClosure E
    let : Algebra Ω (TensorProduct k E Ω) := Algebra.TensorProduct.rightAlgebra
    obtain ⟨⟨e⟩, _⟩ := Algebra.separable_tensor_algebraicallyClosed_equiv_pi k E Ω hsep
    have hpb := pullback_of_geometrically hE.geometrically_irreducibleSpace Ω
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
    have ht : IrreducibleSpace (Spec (CommRingCat.of (TensorProduct k E Ω))) :=
      (pullbackSpecIso k E Ω).hom.homeomorph.irreducibleSpace_iff.mp hpb
    let : IrreducibleSpace (PrimeSpectrum ((E →ₐ[k] Ω) → Ω)) :=
      (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).irreducibleSpace_iff.mp ht
    let : Subsingleton (Field.Emb k E) := subsingleton_of_irreducible_pi _ Ω
    let : IsPurelyInseparable k E :=
      (isPurelyInseparable_iff_subsingleton_emb k E).mpr inferInstance
    obtain ⟨a, ha⟩ := IsPurelyInseparable.surjective_algebraMap_of_isSeparable k E
      ⟨α, IntermediateField.subset_adjoin k {α} (by simp)⟩
    exact ⟨a, congrArg (algebraMap E K) ha⟩
  · intro h
    let A := algebraicClosure k K
    have hKA : GeometricallyIrreducible
        (Spec.map (CommRingCat.ofHom (algebraMap A K))) := by
      apply geometricallyIrreducible_of_isAlgebraic_mem
      intro x hx
      have hxk : _root_.IsIntegral k x := isIntegral_trans x hx.isIntegral
      exact ⟨⟨x, mem_algebraicClosure_iff'.mpr hxk⟩, rfl⟩
    let : IsPurelyInseparable k A := isPurelyInseparable_iff.mpr fun x ↦
      ⟨Algebra.IsIntegral.isIntegral x, fun hx ↦ by
        obtain ⟨a, ha⟩ := h x.1 (IsSeparable.map A.val A.val.injective hx)
        exact ⟨a, Subtype.ext ha⟩⟩
    have hA : GeometricallyIrreducible
        (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
      refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun L _ g ↦ ?_⟩
      exact (IsUniversalHomeomorphism.homeomorph (Limits.pullback.snd _ g)).irreducibleSpace_iff.mpr
        inferInstance
    let := hKA
    let := hA
    have hc := GeometricallyIrreducible.comp
      (Spec.map (CommRingCat.ofHom (algebraMap A K)))
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))
    simpa only [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      IsScalarTower.algebraMap_eq k A K] using hc

end AlgebraicGeometry
