/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.Algebra.Homology.FiniteStripConeFiltration
import WeilConjectures.CategoryTheory.DegreewiseFilteredAcyclic
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Augmentation of a double complex supported in a finite horizontal strip

## References

* Stacks Project, Homology, Lemma 12.25.4, as used in Tag 08C1
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace HomologicalComplex₂

/-- Exact augmented horizontal rows imply that the total augmentation is a
quasi-isomorphism, without a bound in the vertical direction.
-/
theorem quasiIso_of_finite_strip_row_augmentation
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)] (r : ℕ)
    (hsupport : ∀ p : ℤ, p < 0 ∨ (r : ℤ) ≤ p → IsZero (K.X p))
    (A : CochainComplex C ℤ)
    (a : ∀ n : ℤ, A.X n ⟶ (K.X 0).X n)
    (b : A ⟶ K.total (ComplexShape.up ℤ))
    (hb : ∀ n : ℤ, b.f n =
      a n ≫ K.ιTotal (ComplexShape.up ℤ) 0 n n (Int.zero_add n))
    (hrows : ∀ n : ℤ, ∃ f :
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (A.X n) ⟶ K.flip.X n,
      f.f 0 = (HomologicalComplex.singleObjXSelf
        (ComplexShape.up ℤ) 0 (A.X n)).hom ≫ a n ∧ QuasiIso f) :
    QuasiIso b := by
  classical
  choose f hf hq using hrows
  obtain ⟨F, _, hfinite, hgraded⟩ := finite_strip_cone_filtration K r hsupport A a b hb f hf
  apply (CochainComplex.mappingCone.quasiIso_iff_acyclic b).mpr
  apply degreewiseFiltered_acyclic _ F
  · intro n
    exact ⟨n - (r : ℤ), n + 2, hfinite n⟩
  · intro p n
    obtain ⟨e⟩ := hgraded p n
    have hcone := (CochainComplex.mappingCone.quasiIso_iff_acyclic (f p)).mp (hq p)
    apply ((F.gradedPiece p).exactAt_iff_isZero_homology n).mpr
    exact e.isZero_iff.mpr (((CochainComplex.mappingCone (f p)).exactAt_iff_isZero_homology
      (n - p)).mp (hcone (n - p)))

end HomologicalComplex₂
