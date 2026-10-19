/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Sheaf.RingTheory.DerivedCompleteModuleComplex
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingClassicalGenerator
import Sheaf.RingTheory.ModuleLocalizationTowerVanishing
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Triangulated.Orthogonal

/-!
# Perfect complexes over a derived-complete ring

Source: Stacks Project, More on Algebra, Tags 091S and 0ATI
(blueprint: lem-sf-perfect-over-derived-complete-ring).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- If the degree-zero complex of a commutative ring is derived complete for an ideal,
then every perfect complex over that ring is derived complete for the ideal.

Source: Stacks Project, More on Algebra, Tags 091S and 0ATI
(blueprint: lem-sf-perfect-over-derived-complete-ring).

Proof: Fix `f ∈ I`. By the localization-tower vanishing criterion, completeness
of the ring implies that every map from any shift of `A[1/f][0]` to the ring is zero.
The right orthogonal to the shift closure of this localization is triangulated by
Mathlib. It is closed under retracts: compose a map with the split inclusion, use
orthogonality, and then compose with the retraction. Thus its triangulated envelope
contains every perfect object by the classical-generator theorem. Apply the
localization-tower criterion again to each derived limit of the multiplication tower.
Countable products exist because products of modules are exact.
-/
theorem perfect_of_derivedComplete
    {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (I : Ideal A)
    (hA : IsDerivedComplete I
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))) :
    ∀ (P : DerivedCategory (ModuleCat.{u} A)),
      IsPerfectRingComplex P → IsDerivedComplete I P := by
  classical
  let : HasCountableProducts (DerivedCategory (ModuleCat.{u} A)) :=
    derivedCategory_hasCountableProducts (ModuleCat.{u} A)
  intro P hP f hf _ T hT
  let L := (singleFunctor (ModuleCat.{u} A) 0).obj
    (ModuleCat.of A (ULift.{0} (Localization.Away f)))
  let S := (ObjectProperty.singleton L).shiftClosure ℤ
  let Q := S.rightOrthogonal
  have : Q.IsStableUnderRetracts := by
    constructor
    intro X Y r hY Z g hZ
    have hz := hY (g ≫ r.i) hZ
    simpa only [Category.assoc, r.retract, Category.comp_id, zero_comp] using
      congrArg (fun a ↦ a ≫ r.r) hz
  have hgen : Q ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) := by
    let R := (singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
    obtain ⟨T', p, δ, hT'⟩ := Pretriangulated.distinguished_cocone_triangle₁
      (towerTransitionEndomorphism (K := fun _ : ℕ ↦ R) (fun _ ↦ f • 𝟙 R))
    have hall := (module_localization_tower_vanishing_iff.{u, 0, w} f R T'
      ⟨p, δ, hT'⟩).mp (hA f hf T' ⟨p, δ, hT'⟩)
    intro X g hX
    obtain ⟨Y, q, e, hY⟩ := hX
    obtain rfl := (ObjectProperty.singleton_iff L Y).mp hY
    apply (cancel_epi e.inv).mp
    simpa only [comp_zero] using hall q (e.inv ≫ g)
  have hle : (ObjectProperty.singleton
      ((singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))).triangEnvelope ≤ Q :=
    (ObjectProperty.triangEnvelope_le_iff _).mpr
      (ObjectProperty.singleton_le_iff.mpr hgen)
  have hQP : Q P := hle P ((isPerfectRingComplex_eq_triangEnvelope_singleton A) ▸ hP)
  apply (module_localization_tower_vanishing_iff.{u, 0, w} f P T hT).mpr
  intro q g
  exact hQP g ⟨L, q, Iso.refl _, ObjectProperty.ofObj_apply _ ()⟩

end DerivedCategory
