/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns

/-! # Injective terms in finite-diagonal totals

Source: Stacks Project, Derived Categories, Tag 015X.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false

/-- Finite diagonals of a first-quadrant bicomplex of injectives are injective.
Source: Stacks Project, Tags 0133 and 015J.
(blueprint: lem-sp-ce-total-injective-terms).

Proof. In degree n only horizontal indices s in [0,n] occur, with resolution index
n-s. The CoreHasTotal colimit identifies the diagonal with the finite coproduct on
these indices. Each summand is an extension-by-zero component of an injective
term. Finite biproducts of injectives are injective. Below zero every summand is
zero, so the total is strictly concentrated in degrees >= 0. -/
theorem cartanEilenberg_total_injective_terms
    {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (hzero : ∀ p : ℤ, p < 0 → IsZero (I.X p))
    (hterms : ∀ (p : ℤ) (r : ℕ), Injective ((I.X p).X r)) :
    let J := ((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip
    CochainComplex.IsStrictlyGE (J.total (ComplexShape.up ℤ)) 0 ∧
      (∀ n, Injective ((J.total (ComplexShape.up ℤ)).X n)) := by
  classical
  let J := ((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip
  have hz (r s : ℤ) (h : r < 0 ∨ s < 0) : IsZero ((J.X r).X s) := by
    rcases h with h | h
    · exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat r
        (fun m hm ↦ by change (m : ℤ) = r at hm; omega)
    · exact (HomologicalComplex.eval A (ComplexShape.up ℤ) r).map_isZero
        ((ComplexShape.embeddingUpNat.extendFunctor A).map_isZero (hzero s h))
  constructor
  · rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    rw [IsZero.iff_id_eq_zero]
    apply HomologicalComplex₂.total.hom_ext (ComplexShape.up ℤ) (K := J)
    intro r s hrs
    have hsum : r + s = n := hrs
    exact (hz r s (by omega)).eq_of_src _ _
  · intro n
    let κ : J.CoreHasTotal (ComplexShape.up ℤ) n :=
      { J := { s : ℤ // s ∈ Finset.Icc 0 n }
        φ₁ := fun s ↦ n - s
        φ₂ := fun s ↦ s
        π_φ := fun s ↦ by dsimp [ComplexShape.π]; omega
        hφ := by
          intro s t h
          apply Subtype.ext
          exact congrArg (fun x : ℤ × ℤ ↦ x.2) h
        isZero := by
          intro r s h hrs
          have hbounds : 0 ≤ r ∧ 0 ≤ s := by
            constructor <;> by_contra hbad
            · exact hrs (hz r s (Or.inl (by omega)))
            · exact hrs (hz r s (Or.inr (by omega)))
          refine ⟨⟨s, Finset.mem_Icc.mpr ⟨hbounds.2, ?_⟩⟩, ?_, rfl⟩
          · dsimp [ComplexShape.π] at h; omega
          · dsimp [ComplexShape.π] at h; dsimp; omega }
    let : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts
    let : Finite κ.J := by dsimp [κ]; infer_instance
    let T : κ.J → A := fun s ↦ (J.X (κ.φ₁ s)).X (κ.φ₂ s)
    have hi (s : κ.J) : Injective (T s) := by
      have hr : 0 ≤ n - (s : ℤ) := by
        have := (Finset.mem_Icc.mp s.property).2
        omega
      let r := (n - (s : ℤ)).toNat
      have he : (r : ℤ) = n - (s : ℤ) := Int.toNat_of_nonneg hr
      exact Injective.of_iso
        (HomologicalComplex.extendXIso
          (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X s))
          ComplexShape.embeddingUpNat (i := r) (i' := n - (s : ℤ)) he).symm
        (hterms s r)
    let e : (∐ T) ≅ (J.total (ComplexShape.up ℤ)).X n :=
      κ.isColimit.coconePointUniqueUpToIso
        (J.toGradedObject.isColimitCofanMapObj
          (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n)
    exact Injective.of_iso (biproduct.isoCoproduct T ≪≫ e) inferInstance

end CategoryTheory
