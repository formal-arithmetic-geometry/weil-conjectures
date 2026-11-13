/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalDerivedReductionExists
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalReductionCompletion
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalKummerReduction

/-! # Existence of the normalized strict diagonal cycle system
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u uA vA
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

private theorem single_scalar_mono {A : Type uA} [Category.{vA} A] [Abelian A]
    (n : ℕ) (M : A) (hm : Mono (n • 𝟙 M)) (i : ℤ) :
    Mono (n • 𝟙 (((HomologicalComplex.single A (.up ℤ) 0).obj M).X i)) := by
  classical
  by_cases hi : i = 0
  · subst i
    let e := eqToIso (HomologicalComplex.single_obj_X_self (.up ℤ) 0 M)
    have he : (n • 𝟙 (((HomologicalComplex.single A (.up ℤ) 0).obj M).X 0)) ≫ e.hom =
        e.hom ≫ (n • 𝟙 M) := by
      simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
        Category.id_comp, Category.comp_id]
    exact mono_of_mono_fac he
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi).mono _

private theorem constant_scalar_mono (W : Scheme.{u}) (n : ℕ) (hn : n ≠ 0) :
    Mono (n • 𝟙 ((constantSheaf (Scheme.ProEt.topology W)
      AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) := by
  have : Mono (n • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} ℤ))) := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro x y h
    change n • x = n • y at h
    exact ULift.ext (nsmul_right_injective hn (congrArg ULift.down h))
  have : Mono ((Functor.const W.ProEtᵒᵖ).map
      (n • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) := NatTrans.mono_of_mono_app _
  have : Mono ((presheafToSheaf (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1}).map
      ((Functor.const W.ProEtᵒᵖ).map
        (n • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} ℤ))))) := inferInstance
  simpa only [constantSheaf, Functor.comp_obj, CategoryTheory.Functor.map_nsmul,
    CategoryTheory.Functor.map_id] using this

private theorem source_mono (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u}) (n : ℕ) :
    Mono (ℓ ^ (n + 1) • 𝟙 (diagonalIntegralSource Y)) := by
  have hm := constant_scalar_mono (ProjectiveLine Y) (ℓ ^ (n + 1))
    (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero)
  have := (lowerStar AddCommGrpCat.{u + 1} (diagonalImmersion Y)).map_mono
    (ℓ ^ (n + 1) • 𝟙 ((constantSheaf (Scheme.ProEt.topology (ProjectiveLine Y))
      AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))))
  simpa only [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id] using this

private theorem source_counit_iso (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (hc : ∀ P : CochainComplex (DiagonalAb (diagonalSurface Y)) ℤ,
      (∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) → IsIso (D.ε.app P)) :
    IsIso (diagonalDerivedSingleCounit ℓ
      (diagonalScalarExtension ℓ (diagonalSurface Y)) D (diagonalIntegralSource Y)) := by
  have := hc ((HomologicalComplex.single _ (.up ℤ) 0).obj (diagonalIntegralSource Y))
    (fun n i ↦ single_scalar_mono _ _ (source_mono ℓ Y n) i)
  unfold diagonalDerivedSingleCounit
  infer_instance

/-- The diagonal torsion classes form one morphism in the derived category of
strict inverse systems, obtained by simultaneous derived reduction of the positive
integral Cartier roof. No noetherian, finiteness or nonemptiness assumption is imposed
on Y. The displayed typeclasses only choose the localization and Ext size conventions.

Source: Stacks Project, Tags 099M and 09AD. -/
theorem exists_diagonalTowerSystem (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))] :
    ∃ D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)),
      DiagonalCompletionSpec ℓ (diagonalSurface Y) D ∧ DiagonalCycleSystemSpec ℓ Y hY D := by
  classical
  obtain ⟨D, _I, hD, _hI⟩ := exists_diagonalDerivedReduction ℓ (diagonalSurface Y)
  have := source_counit_iso ℓ Y D hD
  let a := asIso (diagonalDerivedSingleCounit ℓ
    (diagonalScalarExtension ℓ (diagonalSurface Y)) D (diagonalIntegralSource Y))
  refine ⟨D, diagonal_reduction_completion ℓ (diagonalSurface Y) D, a, rfl, ?_⟩
  exact diagonal_kummer_reduction ℓ Y hY D a rfl

end AlgebraicGeometry.ProEtale
