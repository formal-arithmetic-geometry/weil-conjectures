/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import WeilConjectures.CategoryTheory.CartanEilenbergRowsExists
import WeilConjectures.CategoryTheory.CartanEilenbergRowsIdentifications

/-! # Existence of Cartan--Eilenberg injective resolutions

Source: Stacks Project, derived.tex, Definition 015H and Lemma 015I.

The resolution index is natural, equivalently extending by zero in negative degrees.
The augmentation is a morphism of bicomplexes from the complex placed in vertical
degree zero. Kernels, images and homology in the category of vertical complexes
are computed degreewise. Quasi-isomorphisms from these single-degree complexes,
together with injectivity of every target term, express injective resolutions
using exactly the data of `CategoryTheory.InjectiveResolution`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe u v

/-- Existence of a Cartan--Eilenberg resolution, with all induced augmentations.
Source: Stacks Project, derived.tex, Definition 015H and Lemma 015I. -/
theorem exists_cartanEilenberg_resolution
    (B : Type u) [Category.{v} B] [Abelian B] [EnoughInjectives B]
    (K : CochainComplex B ℤ)
    (hK : ∀ p : ℤ, p < 0 → IsZero (K.X p)) :
    ∃ (I : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ))
      (e : ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
        ⟶ I),
      (∀ p : ℤ, p < 0 → IsZero (I.X p)) ∧
      (∀ p : ℤ, QuasiIso (e.f p)) ∧
      (∀ (p : ℤ) (q : ℕ), Injective ((I.X p).X q)) ∧
      (∀ (p : ℤ) (q : ℕ),
        Injective ((I.cycles p).X q) ∧
        Injective ((image (I.d (p - 1) p)).X q) ∧
        Injective ((I.homology p).X q)) ∧
      (∀ p : ℤ,
        QuasiIso (HomologicalComplex.cyclesMap e p) ∧
        QuasiIso
          (image.map (Arrow.homMk' (e.f (p - 1)) (e.f p) (e.comm (p - 1) p))) ∧
        QuasiIso (HomologicalComplex.homologyMap e p)) := by
  obtain ⟨R, hneg, hqi, hinj⟩ := exists_cartanEilenberg_rows B K hK
  obtain ⟨z, d, h, hz, hd, hh⟩ := cartanEilenberg_rows_identifications R
  refine ⟨R.complex, R.augmentation, hneg, ?_, ?_, ?_, ?_⟩
  · intro p
    exact (hqi p).1
  · intro p q
    exact (hinj p q).1
  · intro p q
    refine ⟨?_, ?_, ?_⟩
    · exact Injective.of_iso
        ((HomologicalComplex.eval B (ComplexShape.up ℕ) q).mapIso (z p)).symm
        (hinj p q).2.1
    · exact Injective.of_iso
        ((HomologicalComplex.eval B (ComplexShape.up ℕ) q).mapIso (d p)).symm
        (hinj p q).2.2.1
    · exact Injective.of_iso
        ((HomologicalComplex.eval B (ComplexShape.up ℕ) q).mapIso (h p)).symm
        (hinj p q).2.2.2
  · intro p
    refine ⟨?_, ?_, ?_⟩
    · have : QuasiIso
          (HomologicalComplex.cyclesMap R.augmentation p ≫ (z p).hom) := by
        rw [hz p]
        exact (hqi p).2.1
      exact quasiIso_of_comp_right _ (z p).hom
    · have : QuasiIso
          (image.map (Arrow.homMk' (R.augmentation.f (p - 1))
            (R.augmentation.f p) (R.augmentation.comm (p - 1) p)) ≫ (d p).hom) := by
        rw [hd p]
        exact (hqi p).2.2.1
      exact quasiIso_of_comp_right _ (d p).hom
    · have : QuasiIso
          (HomologicalComplex.homologyMap R.augmentation p ≫ (h p).hom) := by
        rw [hh p]
        exact (hqi p).2.2.2
      exact quasiIso_of_comp_right _ (h p).hom

end CategoryTheory
