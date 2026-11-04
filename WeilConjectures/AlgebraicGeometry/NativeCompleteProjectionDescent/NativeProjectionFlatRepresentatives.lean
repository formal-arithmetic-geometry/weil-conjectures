/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeCompleteProjectionDescent.NativeProjectionDescentMaps
import all WeilConjectures.AlgebraicGeometry.ProEtaleInternalPullbackKFlat
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalTensorCounit

/-! # Flat K-flat representatives of native integral complexes

Source: blueprint (3) (blueprint: def-sp-projection-reduction-presentation).

Every object of the native integral derived category is represented by a complex of flat
modules which is K-flat, and this class of representatives is stable under the ordinary
inverse image.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures WeilConjectures.SemilinearSections
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NativeCompleteProjectionDescent

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The section-presentation flat representative class is internal K-flatness together
with internal termwise flatness. Source: Stacks 06YN, 00YV (auxiliary; not a blueprint node). -/
theorem flatRepresentative_iff (T : Scheme.{u}) (P : CochainComplex (Modules l E T) ℤ) :
    FlatRepresentative l E T P ↔ (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P ∧
      ∀ n, ObjectProperty.flat (P.X n) := by
  refine and_congr (CondensedRing.section_kflat_iff T _ P).symm (forall_congr' fun n ↦ ?_)
  exact (InternalAbelianSheafModule.flat_iff_sectionModule _ _ (P.X n)).symm

theorem exists_flatRepresentative (T : Scheme.{u}) (A : Integral l E T) :
    ∃ P : CochainComplex (Modules l E T) ℤ, FlatRepresentative l E T P ∧
      Nonempty (DerivedCategory.Q.obj P ≅ A) := by
  obtain ⟨P, π, hπ, hflat, hk⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (DerivedCategory.Q.objPreimage A)
  have : QuasiIso π := hπ
  exact ⟨P, (flatRepresentative_iff l E T P).2 ⟨hk, hflat⟩,
    ⟨asIso (DerivedCategory.Q.map π) ≪≫ DerivedCategory.Q.objObjPreimageIso A⟩⟩

theorem flatRepresentative_pull {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (Modules l E Y) ℤ) (hP : FlatRepresentative l E Y P) :
    FlatRepresentative l E X (((ordinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj P) := by
  obtain ⟨hk, hflat⟩ := (flatRepresentative_iff l E Y P).1 hP
  exact (flatRepresentative_iff l E X _).2
    ⟨CondensedRing.kFlat_upperStar_mapHomologicalComplex_obj _ f hk,
      fun n ↦ (CondensedRing.upperStar_preservesFlat _ f).flat_obj (hflat n)⟩

end AlgebraicGeometry.ProEtale.NativeCompleteProjectionDescent
