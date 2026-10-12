/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Polynomial

/-- Finite monic factorization data modulo the union of compatible ideals descends to
one stage. No henselian hypothesis is needed.
Source: Stacks Project, More on Algebra, Lemma 0FWT, second paragraph of the proof.
(blueprint: lem-weil-pbc-filtered-colimit-factorization-descent)

Proof: every colimit element has a stage representative. Finitely many representatives
can be moved to one common stage. If a stage element maps into I, express its image as
the image of an element of some J j; equality in a filtered colimit holds at a later
stage, where compatibility puts the original element into the stage ideal. The same
holds simultaneously for finitely many elements.
If A/I is nonzero, write f and its two monic factors as powers of X plus lower terms.
Choose representatives in A of the lower coefficients of the factors and of two Bezout
polynomials witnessing coprimality. Descend these and the lower coefficients of f to
one stage, keeping the leading coefficients exactly 1. The coefficients of F-GH and
1-GG'-HH' map into I; move further until all lie in the stage ideal. Reduction there
gives the required factorization and Bezout relation. Mapping back gives the prescribed
factors. If A/I is zero, first move to a stage where 1 belongs to J (using the preceding
membership argument applied to 1); descend f monically and take G=H=1. The stage quotient
and A/I are zero rings, so all factorization, coprimality and image requirements hold.
If A itself is zero, f=0 and one can take F=1 at the chosen stage. -/
theorem filteredColimit_factorization_descent
    {Λ : Type u} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Nonempty Λ]
    (F : Λ ⥤ CommRingCat.{u}) [HasColimit F]
    (J : ∀ i : Λ, Ideal (F.obj i))
    (hJ : ∀ {i j : Λ} (f : i ⟶ j), Ideal.map (F.map f).hom (J i) ≤ J j)
    (I : Ideal (colimit F : CommRingCat.{u}))
    (hI : ∀ x, x ∈ I ↔
      ∃ (i : Λ) (a : F.obj i), (colimit.ι F i).hom a = x ∧ a ∈ J i)
    (f : (colimit F : CommRingCat.{u})[X]) (hf : f.Monic)
    (g₀ h₀ : ((colimit F : CommRingCat.{u}) ⧸ I)[X])
    (hg₀ : g₀.Monic) (hh₀ : h₀.Monic) (hcop : IsCoprime g₀ h₀)
    (hfact : f.map (Ideal.Quotient.mk I) = g₀ * h₀) :
    ∃ (i : Λ) (fᵢ gᵢ hᵢ : (F.obj i)[X]),
      fᵢ.Monic ∧ gᵢ.Monic ∧ hᵢ.Monic ∧ fᵢ.map (colimit.ι F i).hom = f ∧
      IsCoprime (gᵢ.map (Ideal.Quotient.mk (J i))) (hᵢ.map (Ideal.Quotient.mk (J i))) ∧
      fᵢ.map (Ideal.Quotient.mk (J i)) =
        gᵢ.map (Ideal.Quotient.mk (J i)) * hᵢ.map (Ideal.Quotient.mk (J i)) ∧
      (gᵢ.map (colimit.ι F i).hom).map (Ideal.Quotient.mk I) = g₀ ∧
      (hᵢ.map (colimit.ι F i).hom).map (Ideal.Quotient.mk I) = h₀ := by
  sorry
