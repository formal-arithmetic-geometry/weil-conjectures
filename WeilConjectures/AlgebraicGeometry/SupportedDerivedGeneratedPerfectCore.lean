/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSums
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.AlgebraicGeometry.SupportedCompactDetectorModel
import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
import WeilConjectures.CategoryTheory.GeneratorTowerNormalize

/-! # Telescope construction for a given supported compact detector

## References

* [Stacks Project, Tag 0E4G](https://stacks.math.columbia.edu/tag/0E4G)
* [Stacks Project, Tag 09SN](https://stacks.math.columbia.edu/tag/09SN)
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry

/-- A given compact supported detector builds each supported quasi-coherent object. -/
theorem supported_derived_generated_perfect_core (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (V : Y.Opens) (E Q : schemeDerivedQCohCategory Y)
    (htri : ObjectProperty.IsTriangulated (fun K : schemeDerivedCategory Y ↦
      schemeDerivedQCohProperty Y K ∧
        ∀ (k : ℤ) (y : Y), y ∉ (V : Set Y)ᶜ →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj K).val.presheaf y))))
    (hcompact :
      letI : HasCoproducts.{u} (schemeDerivedQCohCategory Y) := derivedQCohDirectSums Y
      IsCompactObject E)
    (hsupport : ∀ (k : ℤ) (y : Y), y ∉ (V : Set Y)ᶜ →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj E.obj).val.presheaf y)))
    (hgen : ∀ K : schemeDerivedQCohCategory Y,
      (∀ (k : ℤ) (y : Y), y ∉ (V : Set Y)ᶜ →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj K.obj).val.presheaf y))) →
      (IsZero K.obj ↔ ∀ n : ℤ, Subsingleton (E.obj⟦n⟧ ⟶ K.obj))) :
    (∀ (k : ℤ) (y : Y), y ∉ (V : Set Y)ᶜ →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj Q.obj).val.presheaf y))) →
      ∃ (X : ℕ → schemeDerivedQCohCategory Y)
        (t : ∀ n : ℕ, (X n).obj ⟶ (X (n + 1)).obj),
        IsZero (X 0).obj ∧
        (∀ n : ℕ, ∃ (I : Type u) (m : I → ℤ)
          (C : Cofan (fun i : I ↦ E.obj⟦m i⟧)), Nonempty (IsColimit C) ∧
          ∃ (a : (X (n + 1)).obj ⟶ C.pt)
            (b : C.pt ⟶ (X n).obj⟦(1 : ℤ)⟧),
            Triangle.mk (t n) a b ∈ distTriang (schemeDerivedCategory Y)) ∧
        ∃ (S : Cofan (fun n : ℕ ↦ (X n).obj)), Nonempty (IsColimit S) ∧
          ∃ (s : S.pt ⟶ S.pt) (q : S.pt ⟶ Q.obj)
            (r : Q.obj ⟶ S.pt⟦(1 : ℤ)⟧),
            (∀ n : ℕ, S.inj n ≫ s = t n ≫ S.inj (n + 1)) ∧
            Triangle.mk (𝟙 S.pt - s) q r ∈ distTriang (schemeDerivedCategory Y) := by
  intro hQ
  obtain ⟨C, cat, z, shift, add, shiftAdd, pretri, tri, sums, F, comm,
    htriF, haddF, hsumF, hqcF, e, q, ⟨he⟩, ⟨hq⟩, hecompact, hegen⟩ :=
    supported_compact_detector_model Y V E Q htri hcompact hsupport hgen hQ
  let := cat
  let := z
  let := shift
  let := add
  let := shiftAdd
  let := pretri
  let := tri
  let := sums
  let := comm
  let := htriF
  let := haddF
  obtain ⟨A, t, hstart, hsteps, qA, rA, htel⟩ :=
    compactGenerators_buildObjects.{u, u} (fun _ : ULift.{u} Unit ↦ e)
      (fun _ ↦ hecompact) hegen q
  have hstart' : ∃ (J : Type u) (m : J → ℤ),
      Nonempty (A 0 ≅ ∐ fun j : J ↦ e⟦m j⟧) := by
    obtain ⟨J, _, m, h⟩ := hstart
    exact ⟨J, m, h⟩
  have hsteps' : ∃ (Z : ℕ → C) (a : ∀ n : ℕ, Z n ⟶ A n)
      (b : ∀ n : ℕ, A (n + 1) ⟶ (Z n)⟦(1 : ℤ)⟧),
      (∀ n : ℕ, ∃ (J : Type u) (m : J → ℤ),
        Nonempty (Z n ≅ ∐ fun j : J ↦ e⟦m j⟧)) ∧
      ∀ n : ℕ, Triangle.mk (a n) (t n) (b n) ∈ distTriang C := by
    obtain ⟨Z, a, b, hZ, hdist⟩ := hsteps
    refine ⟨Z, a, b, ?_, hdist⟩
    intro n
    obtain ⟨J, _, m, h⟩ := hZ n
    exact ⟨J, m, h⟩
  obtain ⟨X, tX, hzero, htrans, hcolim⟩ :=
    generator_tower_normalize F hsumF e q E.obj Q.obj he hq
      A t hstart' hsteps' qA rA htel
  exact ⟨fun n ↦ ⟨F.obj (X n), hqcF (X n)⟩, tX, hzero, htrans, hcolim⟩

end AlgebraicGeometry
