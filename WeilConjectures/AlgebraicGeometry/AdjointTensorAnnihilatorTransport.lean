/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.DerivedTensorPrecompositionOpen
import WeilConjectures.AlgebraicGeometry.DerivedTensorPrecompositionProjection
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive

/-! # Transporting a tensor annihilator across a direct-image adjunction

Source: Stacks Project, Tag 0E4G, projection-formula paragraph.
-/

@[expose] public section

universe u wX wY

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- A perfect tensor annihilator for the adjoint of beta gives a precomposition killing
beta which becomes invertible over the inverse image open (Stacks, Tag 0E4G). -/
theorem adjoint_tensor_annihilator_transport
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ W : X.Opens,
      HasDerivedCategory.{wX} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    [∀ W : Y.Opens,
      HasDerivedCategory.{wY} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))]
    (F : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Y)
    (hF : F ⋙ ObjectProperty.ι (schemeDerivedQCohProperty Y) ≅
      ObjectProperty.ι (schemeDerivedQCohProperty X) ⋙ schemeDerivedDirectImage f)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X) (adj : F ⊣ a)
    (V : Y.Opens) (P : schemeDerivedQCohCategory X) (Q : schemeDerivedQCohCategory Y)
    (β : P ⟶ a.obj Q) (I : schemeDerivedCategory Y)
    (hI : Scheme.IsPerfect Y I) (i : I ⟶ 𝟙_ (schemeDerivedCategory Y))
    (hi : IsIso ((SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace)
      V).mapDerivedCategory.map i))
    (hkill : i ▷ (F.obj P).obj ≫ (λ_ (F.obj P).obj).hom ≫
      ((adj.homEquiv P Q).symm β).hom = 0) :
    ∃ (R : schemeDerivedCategory X) (j : R ⟶ P.obj),
      IsIso ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
        (f ⁻¹ᵁ V)).mapDerivedCategory.map j) ∧ j ≫ β.hom = 0 := by
  obtain ⟨e, hR, hj⟩ := exists_derivedTensor_precomposition_open f V P I hI i hi
  let R : schemeDerivedQCohCategory X :=
    ⟨(derivedPullbackAcrossUniverses f).obj I ⊗ P.obj, hR⟩
  let j : R ⟶ P := ObjectProperty.homMk
    ((derivedPullbackAcrossUniverses f).map i ▷ P.obj ≫
      e.hom ▷ P.obj ≫ (λ_ P.obj).hom)
  obtain ⟨t, ht⟩ := exists_derivedTensor_precomposition_projection f F hF P I hI i e hR
  have hzero : F.map j ≫ (adj.homEquiv P Q).symm β = 0 := by
    apply ObjectProperty.hom_ext
    change (F.map j).hom ≫ ((adj.homEquiv P Q).symm β).hom = 0
    rw [show (F.map j).hom = t ≫ i ▷ (F.obj P).obj ≫
      (λ_ (F.obj P).obj).hom from ht]
    simp only [Category.assoc, hkill, Limits.comp_zero]
  have hcomp : j ≫ β = 0 := by
    have : (F ⋙ ObjectProperty.ι (schemeDerivedQCohProperty Y)).Additive :=
      Functor.additive_of_iso hF.symm
    have : F.Additive :=
      Functor.additive_of_comp_faithful F (ObjectProperty.ι (schemeDerivedQCohProperty Y))
    rw [← Equiv.apply_symm_apply (adj.homEquiv P Q) β,
      ← adj.homEquiv_naturality_left, hzero, adj.homAddEquiv_zero]
  exact ⟨R.obj, j.hom, hj, congrArg InducedCategory.Hom.hom hcomp⟩

end AlgebraicGeometry
