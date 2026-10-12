/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.Topology.Algebra.Group.Basic
import Sheaf.FieldTheory.OpenSubgroupFixedField

/-!
# Finite separable extensions and finite continuous Galois sets

Source: Stacks Project, Tags 03SF and 03QR (blueprint: lem-exc-etale-field-galois-classification).
-/

@[expose] public section

universe u v w w' z

open scoped IntermediateField

namespace FieldTheory

/-!
The affine description of `Hom_K(Spec K^sep, Spec L)` is the type of `K`-algebra
maps `L →ₐ[K] K^sep`.  The action below is postcomposition by `Gal(K^sep/K)`.
-/

/-- Finite separable extensions of a field are classified by finite continuous Galois sets.

Source: Stacks Project, Tags 03SF and 03QR (blueprint: lem-exc-etale-field-galois-classification).
The proof first identifies geometric points with algebra embeddings. Embeddings exist by
extension to the separable closure and are finite because their values on a finite basis
are roots of minimal polynomials. Extend an isomorphism between two images to an
endomorphism of the separable closure; algebraicity makes it invertible, proving
transitivity. Stabilizers are fixing subgroups, which are open for finite subextensions.
For a nonempty transitive continuous discrete action, the stabilizer of a point is open;
its fixed field is finite separable and its embedding action has the same homogeneous
G-set. Finally, an equivariant map is determined by one embedding. The fixed-field
identity factors its image through that embedding and gives the unique field map.
-/
theorem finite_separable_extension_galois_classification
    (K : Type u) (Ksep : Type v) [Field K] [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep]
    (L : Type w) (L' : Type w') [Field L] [Field L'] [Algebra K L] [Algebra K L']
    [FiniteDimensional K L] [FiniteDimensional K L']
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K L'] :
    (Nonempty (L →ₐ[K] Ksep) ∧ Finite (L →ₐ[K] Ksep) ∧
      (∀ σ τ : L →ₐ[K] Ksep, ∃ g : Gal(Ksep / K),
        g.toAlgHom.comp σ = τ) ∧
      (∀ σ : L →ₐ[K] Ksep,
        {g : Gal(Ksep / K) | g.toAlgHom.comp σ = σ} =
          (IntermediateField.map σ ⊤).fixingSubgroup) ∧
      (∀ σ : L →ₐ[K] Ksep,
        IsOpen {g : Gal(Ksep / K) | g.toAlgHom.comp σ = σ})) ∧
    (∀ (Y : Type z) [Finite Y] [MulAction (Gal(Ksep / K)) Y],
      Nonempty Y →
      MulAction.IsPretransitive (Gal(Ksep / K)) Y →
      (∀ y : Y, IsOpen {g : Gal(Ksep / K) | g • y = y}) →
        ∃ E : IntermediateField K Ksep,
          FiniteDimensional K E ∧ Algebra.IsSeparable K E ∧
            ∃ e : Y ≃ (E →ₐ[K] Ksep),
              ∀ (g : Gal(Ksep / K)) (y : Y),
                e (g • y) = g.toAlgHom.comp (e y)) ∧
    Function.Bijective
      (fun (f : L' →ₐ[K] L) =>
        (⟨fun (σ : L →ₐ[K] Ksep) => σ.comp f,
          by
            intro g σ
            rfl⟩ :
          {φ : (L →ₐ[K] Ksep) → (L' →ₐ[K] Ksep) //
            ∀ (g : Gal(Ksep / K)) (σ : L →ₐ[K] Ksep),
              φ (g.toAlgHom.comp σ) = g.toAlgHom.comp (φ σ)}))
  := by
  sorry

end FieldTheory
