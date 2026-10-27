/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.Paper.LisseLatticeHeartLiftData
import Sheaf.Paper.LisseLatticeNormalizedRealizations
import Sheaf.Paper.LisseLatticeChoiceExistence
import Sheaf.Paper.LisseLatticeSingleComparisons
import Sheaf.Paper.LisseLatticeRealizationFaithful
import Sheaf.Paper.LisseLatticeLisseDescent
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Constructible lattices and unique specified local rational lifts

Source: Bhatt--Scholze, Section 6.8, especially 6.8.11(3) and 6.8.14(2)
(blueprint: lem-tw-lisse-lattice-heart-lift).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme TensorProduct
namespace WeilConjectures.LisseLattice
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem unique_specified_lift
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) [F.Full] [F.Faithful] {K P : C} {A B : D}
    (s : F.obj K ⟶ A) [IsIso s] (t : F.obj P ⟶ B) [IsIso t] (g : A ≅ B) :
    ∃! e : K ≅ P,
      F.map e.hom ≫ t = s ≫ g.hom ∧ F.map e.inv ≫ s = t ≫ g.inv := by
  let e := F.preimageIso (asIso s ≪≫ g ≪≫ (asIso t).symm)
  refine ⟨e, ?_, ?_⟩
  · constructor
    · simp [e, Functor.preimageIso, Category.assoc]
    · simp [e, Functor.preimageIso, Category.assoc]
  · intro e' he'
    apply Iso.ext
    apply F.map_injective
    apply (cancel_mono t).mp
    exact he'.1.trans (by simp [e, Functor.preimageIso, Category.assoc])

private theorem single_rational_heart (X : Scheme.{u}) (N : integralTowerModules l E X)
    (hN : sfIntegralConstructible l E X ((DerivedCategory.singleFunctor _ 0).obj N)) :
    sfRationalHeartProperty l E X ((sfRationalConstructibleLocalization l E X).obj
      ⟨(DerivedCategory.singleFunctor _ 0).obj N, hN⟩) := by
  constructor
  · refine ⟨⟨_, hN⟩, ?_, ⟨Iso.refl _⟩⟩
    intro i hi
    exact DerivedCategory.isZero_of_isLE _ 0 i hi
  · refine ⟨⟨_, hN⟩, ?_, ⟨Iso.refl _⟩⟩
    intro i hi
    exact DerivedCategory.isZero_of_isGE _ 0 i hi

/-- A constructible integral heart lattice exists, and every chosen lattice has the
unique specified local lifts. Normalized realization data exist, and the assertion is
independent of their presentation. There is no separation assumption on X.

Source: BS Lemmas 6.8.2, 6.8.13; Proposition 6.8.4(6), Definitions 6.8.3 and 6.8.10,
Propositions 6.8.11(3) and 6.8.14(2)
(blueprint: lem-tw-lisse-lattice-heart-lift).

Proof: normalized scalar presentations and balanced restriction are supplied by
normalized_realizations. The two lattice existence theorems, transported through these
presentations and refined to quasi-compact charts, supply lattice_choice_exists.
lattice_single_comparisons gives integral membership and the actual degree-zero comparison
isomorphisms for every choice. Degree-zero cohomological vanishing proves the rational
heart condition directly. On each chart, normalized_realization_fully_faithful and
unique_specified_lift lift the conjugated specified sheaf isomorphism, prove the displayed
forward and inverse equations, and prove uniqueness by cancellation and faithfulness.
lattice_lisse_of_local_isomorphisms applies to these lifted isomorphisms and gives the
pro-etale finite-free pullback witnesses. The last step retains completed pullback to
possibly non-noetherian charts. -/
theorem lisse_lattice_heart_lift (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) :
    Nonempty (Realizations l E) ∧
      ∀ (a : Realizations l E) (X : LisseRealization.Base D l hl)
        (L : RationalModules l E X.scheme), L.IsFiniteLocallyFree →
        Nonempty (Choice l E a X.scheme L) ∧
          ∀ c : Choice l E a X.scheme L, c.Assertions l E := by
  refine ⟨normalized_realizations l E, ?_⟩
  intro a X L hL
  refine ⟨lattice_choice_exists l E D hl a X L hL, ?_⟩
  intro c
  obtain ⟨hN, hNiso, hcharts⟩ := lattice_single_comparisons l E D hl a X L c
  have hlifts : ∀ i : c.I,
      ∃ hNi : sfIntegralConstructible l E (c.Y i).left
          ((DerivedCategory.singleFunctor _ 0).obj ((integralPull l E (c.Y i).hom).obj c.N)),
      ∃ hMi : sfIntegralConstructible l E (c.Y i).left
          ((DerivedCategory.singleFunctor _ 0).obj (c.M i)),
        IsIso ((a.realization (c.Y i).left).singleComparison l E
          ((integralPull l E (c.Y i).hom).obj c.N) hNi) ∧
        IsIso ((a.realization (c.Y i).left).singleComparison l E (c.M i) hMi) ∧
        ∃! e : (sfRationalConstructibleLocalization l E (c.Y i).left).obj
            ⟨(DerivedCategory.singleFunctor _ 0).obj
              ((integralPull l E (c.Y i).hom).obj c.N), hNi⟩ ≅
          (sfRationalConstructibleLocalization l E (c.Y i).left).obj
            ⟨(DerivedCategory.singleFunctor _ 0).obj (c.M i), hMi⟩,
          (a.realization (c.Y i).left).J.map e.hom ≫
              (a.realization (c.Y i).left).singleComparison l E (c.M i) hMi =
            (a.realization (c.Y i).left).singleComparison l E
                ((integralPull l E (c.Y i).hom).obj c.N) hNi ≫
              (DerivedCategory.singleFunctor _ 0).map (c.specified l E i).hom ∧
          (a.realization (c.Y i).left).J.map e.inv ≫
              (a.realization (c.Y i).left).singleComparison l E
                ((integralPull l E (c.Y i).hom).obj c.N) hNi =
            (a.realization (c.Y i).left).singleComparison l E (c.M i) hMi ≫
              (DerivedCategory.singleFunctor _ 0).map (c.specified l E i).inv := by
    intro i
    obtain ⟨hNi, hMi, hs, ht⟩ := hcharts i
    have : QuasiCompact (c.Y i).hom := c.quasiCompact i
    let Y : LisseRealization.Base D l hl :=
      { scheme := (c.Y i).left
        over := ⟨(c.Y i).hom ≫ (X.scheme ↘ Spec (.of D.k))⟩
        finiteType := by
          change LocallyOfFiniteType ((c.Y i).hom ≫ (X.scheme ↘ Spec (.of D.k)))
          infer_instance
        quasiCompact := by
          change QuasiCompact ((c.Y i).hom ≫ (X.scheme ↘ Spec (.of D.k)))
          infer_instance }
    obtain ⟨hfull, hfaithful⟩ :=
      normalized_realization_fully_faithful l E D hl Y (a.realization (c.Y i).left)
    have := hfull
    have := hfaithful
    have := hs
    have := ht
    refine ⟨hNi, hMi, hs, ht, ?_⟩
    exact unique_specified_lift (a.realization (c.Y i).left).J
      ((a.realization (c.Y i).left).singleComparison l E
        ((integralPull l E (c.Y i).hom).obj c.N) hNi)
      ((a.realization (c.Y i).left).singleComparison l E (c.M i) hMi)
      ((DerivedCategory.singleFunctor _ 0).mapIso (c.specified l E i))
  refine ⟨hN, single_rational_heart l E X.scheme c.N hN, hNiso, hlifts, ?_⟩
  apply lattice_lisse_of_local_isomorphisms l E D hl a X L c hN
  intro i
  obtain ⟨hNi, hMi, _, _, e, _, _⟩ := hlifts i
  exact ⟨hNi, hMi, ⟨e⟩⟩

end WeilConjectures.LisseLattice
