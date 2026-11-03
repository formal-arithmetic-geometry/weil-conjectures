/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.PerfectReductionRoos.PerfectReductionRoosData
import WeilConjectures.SmoothPurity.SheafRingCoefficientOrdinaryAdjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Normalized coefficient units and exact derived restriction

Source: Bhatt--Scholze, Lemma 3.5.5, perfect-complex comparison a.
(blueprint: lem-sp-perfect-reduction-coefficient-units).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r wR wA a b w
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules SheafOfModules.RegularQuotientCone SheafOfModules.TotalTensorSigns
open scoped ChangeOfRings

namespace CategoryTheory.PerfectReductionRoos

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [HasSheafify J CommRingCat.{r}]
  (R : Sheaf J CommRingCat.{r})
  (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)


variable [HasDerivedCategory.{wR} (RegularQuotientCone.Modules R)]
  [∀ m, HasDerivedCategory.{wA} (RegularQuotientCone.Modules (powerRing R t m))]

/-- Ordinary coefficient units and their exact derived restriction functors.
Source: Stacks Tags 03D7 and 03DA
(blueprint: lem-sp-perfect-reduction-coefficient-units). -/
structure CoefficientUnits
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m)) where
  ρ : ∀ m, 𝟭 (CochainComplex (RegularQuotientCone.Modules R) ℤ) ⟶
    (d m).E.mapHomologicalComplex (.up ℤ) ⋙
      (restriction (powerProjection R t m)).mapHomologicalComplex (.up ℤ)
  V : ∀ m, DerivedCategory (RegularQuotientCone.Modules (powerRing R t m)) ⥤
    DerivedCategory (RegularQuotientCone.Modules R)
  v : ∀ m, DerivedCategory.Q ⋙ V m ≅
    (restriction (powerProjection R t m)).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  ρ_sections : ∀ m Z i (U : Cᵒᵖ) (x : (Z.X i).val.obj U),
      (eqToHom ((d m).obj_eq (Z.X i))).val.app U ((((ρ m).app Z).f i).val.app U x) =
        (toSheafify J (changeOfRingsPresheaf (powerProjection R t m) (Z.X i)).presheaf).app U
          ((1 : (powerRing R t m).obj.obj U) ⊗ₜ[R.obj.obj U,
            ((powerProjection R t m).hom.app U).hom] x)

/-- Normalized units on every complex, without a regularity assumption.
Source: Stacks Tags 03D7 and 03DA
(blueprint: lem-sp-perfect-reduction-coefficient-units).

Proof: The normalized ordinary extension/restriction adjunction exists for the
specified ordinary models. Apply its unit termwise to a complex. Naturality for
the differential gives a cochain map, and naturality for chain maps gives the
natural transformation. The normalized Hom equivalence at the identity is exactly
the section formula 1 tensor x. Restriction preserves finite limits and colimits;
its canonical exact derived functor and localization factorization supply V and v.
No multiplication-by-t injectivity or flatness is used. -/
theorem nonempty_coefficientUnits
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m)) :
    Nonempty (CoefficientUnits R t d) := by
  classical
  have h (m : ℕ) := sheafRingCoefficientOrdinaryAdjunction (powerProjection R t m)
  choose hlim hcol ho using h
  choose adj hadj using fun m ↦ ho m (d m).E (d m).obj_eq (d m).map_eq
  let ρ (m : ℕ) : 𝟭 (CochainComplex (RegularQuotientCone.Modules R) ℤ) ⟶
      (d m).E.mapHomologicalComplex (.up ℤ) ⋙
        (restriction (powerProjection R t m)).mapHomologicalComplex (.up ℤ) :=
    { app := fun Z ↦
        { f := fun i ↦ (adj m).unit.app (Z.X i)
          comm' := fun i j _ ↦ ((adj m).unit.naturality (Z.d i j)).symm }
      naturality := fun Z W f ↦ by
        ext i : 1
        exact (adj m).unit.naturality (f.f i) }
  let (m : ℕ) : PreservesFiniteLimits (restriction (powerProjection R t m)) := hlim m
  let (m : ℕ) : PreservesFiniteColimits (restriction (powerProjection R t m)) := hcol m
  refine ⟨{ ρ := ρ
            V := fun m ↦ (restriction (powerProjection R t m)).mapDerivedCategory
            v := fun m ↦ (restriction (powerProjection R t m)).mapDerivedCategoryFactors
            ρ_sections := ?_ }⟩
  intro m Z i U x
  have hx := hadj m (Z.X i) (changeOfRings (powerProjection R t m) (Z.X i))
    (𝟙 _) U x
  simp only [Category.comp_id, Adjunction.homEquiv_unit] at hx
  exact hx

end CategoryTheory.PerfectReductionRoos
