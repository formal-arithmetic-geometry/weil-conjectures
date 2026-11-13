/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Topology.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.SupportedPerfectDetectorAffine
import WeilConjectures.AlgebraicGeometry.SupportedPerfectDetectorGluing
import WeilConjectures.AlgebraicGeometry.SupportedQCohTriangulated

/-! # Perfect generators with support

Support on `T` is the stalkwise form of the existing support statements: every cohomology
sheaf has zero stalk at every point outside `T`. `D_QCoh,T(O_X)` is the full subcategory
of `D(O_X)` on objects with quasi-coherent cohomology supported on `T`. The weak generator
condition is expressed by the shifted-Hom vanishing criterion, as in
`AlgebraicGeometry.perfect_generator_pullback`; Hom groups and shifts of the full
subcategory are those of the ambient derived category.

## References

* [Stacks Project, Tag 0A9A](https://stacks.math.columbia.edu/tag/0A9A)
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The full subcategory of quasi-coherent derived objects supported on a closed subset
with quasi-compact complement is triangulated and has a single perfect weak generator
supported on that subset. -/
theorem supported_perfect_generator (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ) :
    ObjectProperty.IsTriangulated (fun K : schemeDerivedCategory X ↦
      schemeDerivedQCohProperty X K ∧
        ∀ (n : ℤ) (x : X), x ∉ T →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K).val.presheaf x))) ∧
    ∃ E : schemeDerivedQCohCategory X, Scheme.IsPerfect X E.obj ∧
      (∀ (n : ℤ) (x : X), x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E.obj).val.presheaf x))) ∧
      ∀ K : schemeDerivedQCohCategory X,
        (∀ (n : ℤ) (x : X), x ∉ T →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K.obj).val.presheaf x))) →
        (IsZero K.obj ↔ ∀ n : ℤ, Subsingleton (E.obj⟦n⟧ ⟶ K.obj)) := by
  classical
  refine ⟨supported_qcoh_isTriangulated X T, ?_⟩
  have detectors : ∀ (m : ℕ) (Y : Scheme.{u}) [CompactSpace Y] [QuasiSeparatedSpace Y]
      [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
      [∀ U : Y.Opens,
        HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
      (s : Finset Y.affineOpens), s.card = m →
      (⨆ U ∈ s, (U : Y.Opens)) = ⊤ →
      ∀ (S : Set Y), IsClosed S → IsCompact Sᶜ →
        ∃ E : schemeDerivedQCohCategory Y, Scheme.IsPerfect Y E.obj ∧
          (∀ (n : ℤ) (x : Y), x ∉ S →
            Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj E.obj).val.presheaf x))) ∧
          ∀ K : schemeDerivedQCohCategory Y,
            (∀ (n : ℤ) (x : Y), x ∉ S →
              Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj K.obj).val.presheaf x))) →
            (∀ n : ℤ, Subsingleton (E.obj⟦n⟧ ⟶ K.obj)) → IsZero K.obj := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro Y _ _ _ _ s hm hcover S hS hSc
      by_cases hsmall : s.card ≤ 1
      · exact supported_perfect_detector_affine Y s hcover hsmall S hS hSc
      · refine supported_perfect_detector_gluing Y s hcover (by omega) ?_ S hS hSc
        intro Z _ _ _ _ t ht htcover R hR hRc
        exact ih t.card (hm ▸ ht) Z t rfl htcover R hR hRc
  obtain ⟨s, hs, hcover⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (X := X) (U := ⊤)).mp
      (by simpa using (isCompact_univ : IsCompact (Set.univ : Set X)))
  obtain ⟨E, hE, hET, hdetect⟩ :=
    detectors hs.toFinset.card X hs.toFinset rfl (by simpa using hcover.symm) T hT hTc
  refine ⟨E, hE, hET, ?_⟩
  intro K hKT
  refine ⟨?_, hdetect K hKT⟩
  intro hK n
  exact ⟨fun f g ↦ hK.eq_of_tgt f g⟩

end AlgebraicGeometry
