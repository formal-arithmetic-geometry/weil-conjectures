/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
import WeilConjectures.AlgebraicGeometry.DescendQCOpenFGSubalgebra

/-!
# Quasi-compact opens under Galois base change

## References

* [Stacks, Tag 04KU], [Stacks, Tag 0388]
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem specAlgEquivOver_mul {k L : Type u} [Field k] [Field L]
    [Algebra k L] (σ τ : L ≃ₐ[k] L) :
    specAlgEquivOver (σ * τ) = specAlgEquivOver σ ≫ specAlgEquivOver τ := by
  apply Over.OverMorphism.ext
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1

private theorem specAlgEquivOver_one {k L : Type u} [Field k] [Field L]
    [Algebra k L] : specAlgEquivOver (1 : L ≃ₐ[k] L) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (RingHom.id L)) = 𝟙 _
  exact Spec.map_id _

/-- A quasi-compact open descends to a finite intermediate field and is invariant under
all automorphisms fixing that field (Stacks, Tag 04KU). -/
theorem galois_baseChange_qc_open_descends (k L : Type u) [Field k] [Field L]
    [Algebra k L] [IsGalois k L] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (V : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L)))).Opens)
    (hV : IsCompact V.1) :
    let σX := fun σ : L ≃ₐ[k] L ↦ baseChangeMap f (specAlgEquivOver σ)
    (∀ σ : L ≃ₐ[k] L, IsIso (σX σ)) ∧
    (∀ σ τ : L ≃ₐ[k] L, σX (σ * τ) = σX σ ≫ σX τ) ∧
    ∃ K : IntermediateField k L, FiniteDimensional k K ∧
      ∃ V' : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Opens,
        IsCompact V'.1 ∧
        ∃ p : pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⟶
            pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))),
          p = baseChangeMap f
            (Over.homMk (Spec.map (CommRingCat.ofHom K.toSubalgebra.val))
              (by
                change Spec.map (CommRingCat.ofHom K.toSubalgebra.val) ≫
                    Spec.map (CommRingCat.ofHom (algebraMap k K)) =
                  Spec.map (CommRingCat.ofHom (algebraMap k L))
                rw [← Spec.map_comp]
                congr 1) :
              Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L))) ⟶
                Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
          V = p ⁻¹ᵁ V' ∧
          ∀ σ : L ≃ₐ[k] L, (∀ x : K, σ (x : L) = (x : L)) →
            (σX σ) '' V.1 = V.1 := by
  dsimp only
  have hmul (σ τ : L ≃ₐ[k] L) :
      baseChangeMap f (specAlgEquivOver (σ * τ)) =
        baseChangeMap f (specAlgEquivOver σ) ≫ baseChangeMap f (specAlgEquivOver τ) := by
    rw [specAlgEquivOver_mul, baseChangeMap_comp]
  have hone : baseChangeMap f (specAlgEquivOver (1 : L ≃ₐ[k] L)) = 𝟙 _ := by
    rw [specAlgEquivOver_one, baseChangeMap_id]
  have hiso (σ : L ≃ₐ[k] L) : IsIso (baseChangeMap f (specAlgEquivOver σ)) := by
    exact ⟨⟨baseChangeMap f (specAlgEquivOver σ⁻¹),
      by rw [← hmul, mul_inv_cancel, hone],
      by rw [← hmul, inv_mul_cancel, hone]⟩⟩
  refine ⟨hiso, hmul, ?_⟩
  obtain ⟨A, hA, V', hV', p, hp, hVp⟩ := descend_qc_open_fg_subalgebra k X f L V hV
  have hfin : FiniteDimensional k A := by
    obtain ⟨s, hs⟩ := hA
    have hf := Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet
      (fun x _ ↦ (Algebra.IsAlgebraic.isAlgebraic (R := k) x).isIntegral)
    rw [hs] at hf
    exact hf
  let K : IntermediateField k L := A.toIntermediateField' (by
    let := fieldOfFiniteDimensional k A
    exact Field.toIsField A)
  refine ⟨K, hfin, V', hV', p, hp, hVp, ?_⟩
  intro σ hσ
  have hcomm : baseChangeMap f (specAlgEquivOver σ) ≫ p = p := by
    rw [hp, ← baseChangeMap_comp]
    congr 1
    apply Over.OverMorphism.ext
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext x
    exact hσ x
  have hpre : (baseChangeMap f (specAlgEquivOver σ)) ⁻¹' V.1 = V.1 := by
    rw [hVp]
    change (baseChangeMap f (specAlgEquivOver σ) ≫ p) ⁻¹' V'.1 = p ⁻¹' V'.1
    rw [hcomm]
    rfl
  have hs : Function.Surjective (baseChangeMap f (specAlgEquivOver σ)) := by
    have := hiso σ
    exact (Scheme.Hom.homeomorph (baseChangeMap f (specAlgEquivOver σ))).surjective
  calc
    (baseChangeMap f (specAlgEquivOver σ)) '' V.1 =
        (baseChangeMap f (specAlgEquivOver σ)) ''
          ((baseChangeMap f (specAlgEquivOver σ)) ⁻¹' V.1) := congrArg _ hpre.symm
    _ = V.1 := Set.image_preimage_eq _ hs

end AlgebraicGeometry
