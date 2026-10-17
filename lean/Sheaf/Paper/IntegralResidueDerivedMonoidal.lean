/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Sheaf.Paper.IntegralResidueComparisonInterface
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit

/-! # Strong monoidality of exact derived pullback

Source: derivation of the tensor comparison on flat resolutions; compare the proved
Etale.Derived.UpperStarMonoidal construction in the source library.
(blueprint: new-integral-residue-derived-monoidal)
-/

@[expose] public section

universe u u₁ u₂
open CategoryTheory Abelian Limits MonoidalCategory DerivedCategory
open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasFunctorialFlatResolution C]
  {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]

omit [HasFunctorialFlatResolution D] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [F.Monoidal] in
theorem residue_exists_kFlatMap_iso (X : DerivedCategory C) :
    ∃ P, F.kFlatMap P ∧ Nonempty (Qh.obj P ≅ X) := by
  have := Localization.essSurj (Qh (C := C)) (HomotopyCategory.quasiIso _ (.up ℤ))
  obtain ⟨R⟩ := LocalizerMorphism.IsLeftDerivabilityStructure.hasLeftResolutions
    (Φ := HomotopyCategory.quasiIsoLocalizerMorphism F.kFlatMap) (Qh.objPreimage X)
  have : IsIso (Qh.map R.w) := Localization.inverts Qh (HomotopyCategory.quasiIso _ _) _ R.hw
  exact ⟨R.X₁.obj, R.X₁.property, ⟨asIso (Qh.map R.w) ≪≫ Qh.objObjPreimageIso X⟩⟩

@[instance_reducible] noncomputable def residueDerivedOplax : F.leftDerivedFunctor.OplaxMonoidal :=
  haveI := DerivedCategory.isIso_ε_Qh D
  OplaxMonoidal.ofLaxSquare (Q₁ := Qh) (Q₂ := Qh)
    (F := F.mapHomotopyCategory (.up ℤ)) F.leftDerivedTensorComparison
    (fun a ↦ F.leftDerivedFunctorCounit.app a)
    (fun _ _ f ↦ F.leftDerivedFunctorCounit.naturality f)
    (F.leftDerivedTensorComparison_app_app_comp_tensorHom)
    F.kFlatMap (residue_exists_kFlatMap_iso F)
    (fun x _ hb ↦ isIso_μNatTrans_Qh_app_app_of_kFlat x _ hb)

theorem residueDerivedOplax_isIso_δ (X Y : DerivedCategory C) :
    letI := residueDerivedOplax F
    IsIso (OplaxMonoidal.δ F.leftDerivedFunctor X Y) :=
  inferInstanceAs (IsIso ((F.leftDerivedTensorComparison.app X).app Y))

theorem residueDerivedOplax_isIso_η :
    letI := residueDerivedOplax F
    IsIso (OplaxMonoidal.η F.leftDerivedFunctor) := by
  have := DerivedCategory.isIso_ε_Qh C
  have := DerivedCategory.isIso_ε_Qh D
  have : IsIso (OplaxMonoidal.η (F.mapHomotopyCategory (.up ℤ))) := by
    rw [mapHomotopyCategory_η]
    infer_instance
  exact inferInstanceAs (IsIso (F.leftDerivedFunctor.map (LaxMonoidal.ε Qh) ≫
    F.leftDerivedFunctorCounit.app (𝟙_ _) ≫
      Qh.map (OplaxMonoidal.η (F.mapHomotopyCategory (.up ℤ))) ≫
        CategoryTheory.inv (LaxMonoidal.ε Qh)))

/-- The canonical strong monoidal structure obtained by deriving the ordinary
strong monoidal comparison. All coherence laws are descended on flat resolutions. -/
@[no_expose, irreducible] noncomputable def residueDerivedMonoidal :
    F.leftDerivedFunctor.Monoidal := by
  letI := residueDerivedOplax F
  haveI := residueDerivedOplax_isIso_δ F
  haveI := residueDerivedOplax_isIso_η F
  exact (CoreMonoidal.ofOplaxMonoidal _).toMonoidal


/-- The tensor component of the cached derived monoidal structure is the canonical
left-derived tensor comparison.
Source: the defining left-derived tensor comparison.
(blueprint: new-integral-residue-derived-monoidal)
Proof. Unfold the generic construction and its tensor component is definitionally the
canonical comparison. -/
theorem residueDerivedMonoidal_δ (M N : DerivedCategory C) :
    letI := residueDerivedMonoidal F
    OplaxMonoidal.δ F.leftDerivedFunctor M N =
      (F.leftDerivedTensorComparison.app M).app N := by
  unfold residueDerivedMonoidal
  rfl

end CategoryTheory.Functor

universe v

open scoped CategoryTheory.Obj

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- A named copy of the existing integral derived monoidal structure.
This keeps repeated occurrences of the large internal-module instance compact;
its data are exactly the existing derived monoidal instance. -/
@[instance_reducible] noncomputable def residueExchangeIntegralDerivedMonoidal (T : Scheme.{u}) :
    MonoidalCategory (residueExchangeDerived (integralCoeff ℓ E) T) :=
  inferInstance

/-- The actual derived module pullback with the strong monoidal structure induced
from an ordinary pullback structure and preservation of flat modules. -/
@[no_expose, irreducible] noncomputable def residueExchangePullMonoidal
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (m : (f)^*⟦integralCoeff ℓ E⟧.Monoidal)
    (hFlat : (f)^*⟦integralCoeff ℓ E⟧.PreservesFlat) :
    (residueExchangeUpperStar (integralCoeff ℓ E) f).Monoidal := by
  letI := m
  letI := hFlat
  unfold residueExchangeUpperStar
  exact (f)^*⟦integralCoeff ℓ E⟧.residueDerivedMonoidal


/-- The cached pullback structure is the canonical generic derived structure.
Source: the defining derived monoidal construction.
(blueprint: new-integral-residue-derived-monoidal)
Proof. Unfold the typed pullback wrapper; the two constructions are identical. -/
theorem residueExchangePullMonoidal_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (m : (f)^*⟦integralCoeff ℓ E⟧.Monoidal)
    (hFlat : (f)^*⟦integralCoeff ℓ E⟧.PreservesFlat) :
    letI := m
    letI := hFlat
    residueExchangePullMonoidal ℓ E f m hFlat =
      (by
        unfold residueExchangeUpperStar
        exact Functor.residueDerivedMonoidal (f)^*⟦integralCoeff ℓ E⟧) := by
  unfold residueExchangePullMonoidal
  rfl


end AlgebraicGeometry.ProEtale.CondensedRing
