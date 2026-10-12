/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Sheaf.CategoryTheory.ExactCoupleConvergence
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The cohomology cocone of a finite filtered complex

Source: Stacks Project, Homology, Lemma 12.24.11, finite-filtration abutment argument.
(blueprint: lem-sp-filtered-cohomology-diagonal-colimit).
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

omit [Abelian C] in
private theorem diagonalCocone_isColimit
    (D : ℤ → C) (d : ∀ p : ℤ, D (p + 1) ⟶ D p)
    (T : C) (ι : ∀ p : ℤ, D p ⟶ T)
    (hι : ∀ p, d p ≫ ι p = ι (p + 1))
    (a : ℤ) (hiso : ∀ p : ℤ, p ≤ a → IsIso (ι p)) :
    ∀ (V : C) (f : ∀ p : ℤ, D p ⟶ V),
      (∀ p, d p ≫ f p = f (p + 1)) →
      ∃! h : T ⟶ V, ∀ p, ι p ≫ h = f p := by
  intro V f hf
  let := hiso a le_rfl
  let h : T ⟶ V := inv (ι a) ≫ f a
  have hh (p : ℤ) : ι p ≫ h = f p := by
    refine Int.inductionOn' (motive := fun p ↦ ι p ≫ h = f p) p a ?_ ?_ ?_
    · simp [h]
    · intro p _ ih
      rw [← hι p, Category.assoc, ih, hf p]
    · intro p hp ih
      have ih' : ι (p - 1 + 1) ≫ h = f (p - 1 + 1) := by
        rw [show p - 1 + 1 = p by omega]
        exact ih
      let := hiso (p - 1) (by omega)
      let := hiso (p - 1 + 1) (by omega)
      have hi : IsIso (d (p - 1) ≫ ι (p - 1)) := hι (p - 1) ▸ inferInstance
      let := (isIso_comp_right_iff (d (p - 1)) (ι (p - 1))).mp hi
      apply (cancel_epi (d (p - 1))).mp
      rw [← Category.assoc, hι, ih', hf]
  refine ⟨h, hh, ?_⟩
  intro k hk
  apply (cancel_epi (ι a)).mp
  exact (hk a).trans (hh a).symm

/-- The diagonal cohomology inclusion, with the exact-couple indexing transported.
Source: Stacks Homology Lemma 12.24.11
(blueprint: lem-sp-filtered-cohomology-diagonal-colimit). -/
noncomputable def filteredCohomologyDiagonalMap
    (U : FilteredObject (CochainComplex C ℤ)) (X : BigradedExactCouple C 0)
    (eD : ∀ P Q : ℤ, X.D P Q ≅
      (U.filtration.step (-Q) : CochainComplex C ℤ).homology (P + Q)) (n P : ℤ) :
    X.D P (n - P) ⟶ U.obj.homology n :=
  (eD P (n - P)).hom ≫ eqToHom (by
    rw [show -(n - P) = P - n by omega, show P + (n - P) = n by omega]) ≫
      HomologicalComplex.homologyMap (U.filtration.step (P - n)).arrow n

/-- These inclusions exhibit cohomology as the colimit of the alpha diagonal.
Source: Stacks Homology Lemma 12.24.11; step 1 of the bounded abutment proof.
(blueprint: lem-sp-filtered-cohomology-diagonal-colimit).

Proof: The alpha comparison, functoriality of homology, and the equation that the
inclusion of one subobject followed by its arrow is the smaller subobject's arrow
give the cocone equation, including the degree transports. Choose a whole step a.
For P <= a+n, the inclusion F^(P-n) -> U is an isomorphism, so the cocone map is
an isomorphism. Given a compatible cocone f, define its factorization at one such
index P by the inverse inclusion followed by f(P). Compatibility shows the same
formula at every lower index. For a higher index, iterate the consecutive alpha
arrows down to P; their composite commutes with both cocones, proving the required
factorization there. Uniqueness follows by cancelling the isomorphism at P.
This proves the universal property without choosing an arbitrary colimit object. -/
theorem filteredCohomologyDiagonal_isColimit
    (U : FilteredObject (CochainComplex C ℤ)) (hU : U.filtration.IsFinite)
    (X : BigradedExactCouple C 0)
    (eD : ∀ P Q : ℤ, X.D P Q ≅
      (U.filtration.step (-Q) : CochainComplex C ℤ).homology (P + Q))
    (hα : ∀ P Q : ℤ,
      X.alpha P Q ≫ (eD (P - 1) (Q + 1)).hom =
        (eD P Q).hom ≫ HomologicalComplex.homologyMap
          (Subobject.ofLE (U.filtration.step (-Q)) (U.filtration.step (-(Q + 1)))
            (U.filtration.antitone_step (by omega))) (P + Q) ≫
          eqToHom (by rw [show P - 1 + (Q + 1) = P + Q by omega])) :
    (∀ n P : ℤ, X.alphaDiagonal n P ≫ filteredCohomologyDiagonalMap U X eD n P =
      filteredCohomologyDiagonalMap U X eD n (P + 1)) ∧
    (∀ (n : ℤ) (T : C) (f : ∀ P : ℤ, X.D P (n - P) ⟶ T),
      (∀ P, X.alphaDiagonal n P ≫ f P = f (P + 1)) →
      ∃! h : U.obj.homology n ⟶ T,
        ∀ P, filteredCohomologyDiagonalMap U X eD n P ≫ h = f P) := by
  have hc : ∀ n P : ℤ,
      X.alphaDiagonal n P ≫ filteredCohomologyDiagonalMap U X eD n P =
        filteredCohomologyDiagonalMap U X eD n (P + 1) := by
    intro n P
    simp only [BigradedExactCouple.alphaDiagonal, filteredCohomologyDiagonalMap]
    simp only [Category.assoc]
    have h := hα (P + 1) (n - (P + 1))
    have hd := eqToHom_iso_hom_naturality
      (fun z : ℤ × ℤ ↦ eD z.1 z.2)
      (show (P + 1 - 1, n - (P + 1) + 1) = (P, n - P) by ext <;> omega)
    dsimp only [Prod.fst, Prod.snd] at hd
    rw [← reassoc_of% hd, reassoc_of% h]
    rw [eqToHom_trans_assoc, eqToHom_trans_assoc]
    apply (cancel_epi (eD (P + 1) (n - (P + 1))).hom).mpr
    have ht := eqToHom_naturality
      (fun z : ℤ × ℤ ↦ HomologicalComplex.homologyMap (U.filtration.step z.1).arrow z.2)
      (show (-(n - (P + 1) + 1), P + 1 + (n - (P + 1))) = (P - n, n) by
        ext <;> omega)
    have hs := eqToHom_naturality
      (fun z : ℤ × ℤ ↦ HomologicalComplex.homologyMap (U.filtration.step z.1).arrow z.2)
      (show (-(n - (P + 1)), P + 1 + (n - (P + 1))) = (P + 1 - n, n) by
        ext <;> omega)
    dsimp only [Prod.fst, Prod.snd] at ht hs
    rw [← ht, ← hs, ← HomologicalComplex.homologyMap_comp_assoc, Subobject.ofLE_arrow]
  refine ⟨hc, ?_⟩
  intro n
  obtain ⟨a, b, ha, hb⟩ := hU
  apply diagonalCocone_isColimit (fun P ↦ X.D P (n - P)) (X.alphaDiagonal n)
    (U.obj.homology n) (filteredCohomologyDiagonalMap U X eD n) (hc n) (a + n)
  intro P hP
  have he : U.filtration.step (P - n) = ⊤ :=
    top_le_iff.mp (ha ▸ U.filtration.antitone_step (by omega))
  let : IsIso (U.filtration.step (P - n)).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).mpr he
  let : IsIso (HomologicalComplex.homologyMap (U.filtration.step (P - n)).arrow n) :=
    (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n).map_isIso _
  dsimp [filteredCohomologyDiagonalMap]
  infer_instance

end CategoryTheory
