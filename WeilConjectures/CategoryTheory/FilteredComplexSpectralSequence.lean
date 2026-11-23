/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
import WeilConjectures.CategoryTheory.FilteredComplexPositivePages
import WeilConjectures.CategoryTheory.FilteredComplexGradedHomology

/-!
# Spectral sequence of a filtered complex

Source: Stacks Project, Homology, Definition 12.18.1 and Remark 12.18.2 (Tag 012K).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The spectral sequence of a cochain complex `K` with a decreasing filtration `F` by
subcomplexes (a `DecreasingFiltration` of `K` in the abelian category of cochain
complexes): a cohomological spectral sequence starting at page zero, whose page-`r`
differential has bidegree `(r, 1 - r)`, whose page-zero term at `(p, q)` is identified
with `gr^p K^{p+q} = (F.gradedPiece p).X (p + q)`, and whose page-zero differential is,
under these identifications, the differential of the graded complex `gr^p K` induced by `d`;
for `r ≥ 1` its page-`r` term at `(p, q)` is `Z_r / B_r` for the cycle and boundary
subobjects `F.complexCycles p (p + q) r` and `F.complexBoundaries p (p + q) r` of
`gr^p K^{p+q}`, as in Definition 12.18.1.

Source: Stacks Project, Homology, Definition 12.18.1, Remark 12.18.2 (Tag 012K). -/
theorem filteredComplex_associated_spectralSequence
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) :
    ∃ (E : CohomologicalSpectralSequence C 0)
      (e : ∀ p q : ℤ, (E.page 0).X (p, q) ≅ (F.gradedPiece p).X (p + q)),
      (∀ p q : ℤ, (E.page 0).d (p, q) (p, q + 1) ≫ (e p (q + 1)).hom =
        (e p q).hom ≫ (F.gradedPiece p).d (p + q) (p + (q + 1))) ∧
      ∀ (p q r : ℤ) (hr : 1 ≤ r),
        ∃ hBZ : F.complexBoundaries p (p + q) r ≤ F.complexCycles p (p + q) r,
          Nonempty ((E.page r).X (p, q) ≅ cokernel (Subobject.ofLE _ _ hBZ)) := by
  classical
  let P : HomologicalComplex C (ComplexShape.up' (⟨0, 1⟩ : ℤ × ℤ)) :=
    { X := fun a ↦ (F.gradedPiece a.1).X (a.1 + a.2)
      d := fun a b ↦ if h : a.1 = b.1 then
        (F.gradedPiece a.1).d (a.1 + a.2) (a.1 + b.2) ≫
          eqToHom (by rw [h]) else 0
      shape := by
        rintro ⟨p, q⟩ ⟨p', q'⟩ h
        dsimp
        split_ifs with hp
        · subst p'
          simp only [eqToHom_refl, Category.comp_id]
          apply HomologicalComplex.shape
          intro hd
          apply h
          change (p, q) + (0, 1) = (p, q')
          change p + q + 1 = p + q' at hd
          ext <;> dsimp <;> omega
        · rfl
      d_comp_d' := by
        rintro ⟨p, q⟩ ⟨p', q'⟩ ⟨p'', q''⟩ h h'
        change (p, q) + (0, 1) = (p', q') at h
        change (p', q') + (0, 1) = (p'', q'') at h'
        have hp : p = p' := by simpa using congrArg _root_.Prod.fst h
        have hp' : p' = p'' := by simpa using congrArg _root_.Prod.fst h'
        subst p'
        subst p''
        simp }
  let e : ∀ p q : ℤ, P.X (p, q) ≅ (F.gradedPiece p).X (p + q) :=
    fun _ _ ↦ Iso.refl _
  have hd : ∀ p q : ℤ, P.d (p, q) (p, q + 1) ≫ (e p (q + 1)).hom =
      (e p q).hom ≫ (F.gradedPiece p).d (p + q) (p + (q + 1)) := by
    intro p q
    simp [P, e]
  obtain ⟨E₁, hE₁⟩ := filteredComplex_positive_spectralSequence K F
  have h01 : ∀ a : ℤ × ℤ, Nonempty (P.homology a ≅ (E₁.page 1).X a) := by
    rintro ⟨p, q⟩
    obtain ⟨hBZ, ⟨h⟩⟩ := filteredComplex_graded_homology K F P e hd p q
    obtain ⟨hBZ', ⟨h'⟩⟩ := hE₁ p q 1 (by omega)
    exact ⟨h ≪≫ h'.symm⟩
  let E : CohomologicalSpectralSequence C 0 :=
    { page := fun r hr ↦ if h : r = 0 then h ▸ P else E₁.page r (by omega)
      iso := by
        intro r r' a hrr' hr
        by_cases h : r = 0
        · subst r
          have h' : r' = 1 := by omega
          subst r'
          simpa using (h01 a).some
        · have hr1 : 1 ≤ r := by omega
          have h' : r' ≠ 0 := by omega
          simpa [h, h'] using E₁.iso r r' a hrr' hr1 }
  refine ⟨E, e, ?_, ?_⟩
  · simpa [E] using hd
  · intro p q r hr
    have h : r ≠ 0 := by omega
    simpa [E, h] using hE₁ p q r hr

end CategoryTheory
