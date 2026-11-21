/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import WeilConjectures.Algebra.Homology.FlatCoverFunctor
import WeilConjectures.Algebra.Homology.CyclePullbackResolution
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Refinements
public import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# Functorial bounded-above flat replacements on a ringed site

## References

* Stacks Project, Cohomology on Sites, Lemma 06YS, via Lemma 077J and 06XX
* Stacks Project, Derived Categories, Lemma 05T7 (1) (cycle-pullback construction)
* Stacks Project, Modules on Sites, Lemma 03EW (3), (4) (canonical flat covers)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Bounded-above complexes on a ringed site have functorial termwise epimorphic
quasi-isomorphisms from flat complexes with the same upper bound.
The full subcategory below consists of complexes whose terms vanish above `N`.
Epimorphisms here are epimorphisms of sheaves, hence locally surjective maps. -/
theorem exists_functorial_boundedAbove_flat_replacement
    {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) (N : ℤ) :
    let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
    let P : ObjectProperty (CochainComplex A ℤ) :=
      fun F => ∀ (i : ℤ), N < i → IsZero (F.X i)
    ∃ Q : P.FullSubcategory ⥤ CochainComplex A ℤ,
      ∃ ε : Q ⟶ P.ι,
        ∀ F : P.FullSubcategory,
          (∀ (i : ℤ), SheafOfModules.IsFlat ((Q.obj F).X i)) ∧
          (∀ (i : ℤ), N < i → IsZero ((Q.obj F).X i)) ∧
          (∀ (i : ℤ), Epi ((ε.app F).f i)) ∧ QuasiIso (ε.app F) := by
  let A := SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  obtain ⟨T, π, hT⟩ := SheafOfModules.exists_functorial_flat_cover J R
  have hzero (X : A) (hX : IsZero X) : SheafOfModules.IsFlat X := by
    let := SheafOfModules.monoidalCategory R
    let := SheafOfModules.symmetricCategory R
    obtain ⟨⟨hpre⟩, _, _⟩ := SheafOfModules.tensorClosed R
    let := hpre
    exact (ObjectProperty.flat_of_isZero hX).2
  obtain ⟨Q, ε, hQ⟩ := exists_functorial_cyclePullback_construction
    (fun X : A ↦ SheafOfModules.IsFlat X) hzero T π
    (fun X ↦ (hT X).1) (fun X ↦ (hT X).2) N
  refine ⟨Q, ε, fun F ↦ ⟨(hQ F).1, (hQ F).2.1, ?_, ?_⟩⟩
  · intro i
    rw [epi_iff_surjective_up_to_refinements]
    intro B y
    -- First lift the cycle d(y), then lift the resulting compatible pair.
    obtain ⟨B₁, p₁, hp₁, x₁, hx₁, hd₁⟩ :=
      (hQ F).2.2 (i + 1) B 0 (y ≫ F.obj.d i (i + 1)) (by simp)
        (by simp)
    have hx : x₁ ≫ (ε.app F).f (i + 1) =
        (p₁ ≫ y) ≫ F.obj.d i (i + 1) := by
      simpa only [Category.assoc] using hx₁
    obtain ⟨B₂, p₂, hp₂, x₂, hx₂, _⟩ :=
      (hQ F).2.2 i B₁ x₁ (p₁ ≫ y) (by simpa using hd₁) hx
    exact ⟨B₂, p₂ ≫ p₁, inferInstance, x₂, by simpa [Category.assoc] using hx₂.symm⟩
  · rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap, isIso_iff_mono_and_epi]
    constructor
    · rw [HomologicalComplex.mono_homologyMap_iff_up_to_refinements
        (ε.app F) (i - 1) i (i + 1) (by simp) (by simp)]
      intro B x hx y hy
      have hlift := (hQ F).2.2 (i - 1)
      rw [show i - 1 + 1 = i by omega] at hlift
      obtain ⟨B', p, hp, z, _, hz⟩ := hlift B x y hx hy
      exact ⟨B', p, hp, z, by simpa using hz.symm⟩
    · rw [HomologicalComplex.epi_homologyMap_iff_up_to_refinements
        (ε.app F) (i - 1) i (i + 1) (by simp) (by simp)]
      intro B y hy
      obtain ⟨B', p, hp, z, hz, hd⟩ :=
        (hQ F).2.2 i B 0 y (by simp) (by simpa using hy.symm)
      exact ⟨B', p, hp, z, by simpa using hd, 0, by simpa using hz.symm⟩

end CochainComplex
