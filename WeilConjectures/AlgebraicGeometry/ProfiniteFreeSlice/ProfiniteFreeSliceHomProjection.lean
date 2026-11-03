/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.CondensedAction.InternalBar.CondensedInternalBarResolution
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! # The surviving factor of a degree-zero source Hom complex

Source: Stacks Project Tags 08FI, 08J7; HRS Section 3.
(blueprint: new-f3-profinite-free-slice-hom-projection).

For the actual single complex in degree zero, all other factors of the Hom
complex vanish. The surviving projection is invertible and commutes with the
Hom differential, giving the component calculation used by the chain comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u

-- Avoid the universe-mismatched global instance exposed by newer imports.
attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ProfiniteFreeSlice
open ModuleObjectRingedComparison WeilConjectures
attribute [local instance 1000001] sectionRingHasSheafCompose sectionModulesGrothendieck
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (P : Profinite.{u})

/-- Projection to the degree-zero source factor of the free Hom complex is invertible.
Source: Stacks Project Tag 08J7, product Hom from a complex in one degree
(blueprint: new-f3-profinite-free-slice-hom-projection).

Proof: every source term away from degree zero is zero, so its internal Hom
into any module is zero. The product fan is therefore determined by its zero
factor. Define the inverse by inserting the identity at zero and zero maps at
other indices. Product extensionality proves the inverse identities. This
argument uses the existing canonical product projections, and works in the
independent site and coefficient universes. -/
theorem freeHomComponent_isIso (J : CochainComplex (Internal Λ X) ℤ) (n : ℤ) :
    IsIso (coefficientHomComponent.{u, u + 1, u} (Scheme.ProEt.topology X)
      (ring Λ X) (sectionFreeComplex Λ X P) ((complexForward Λ X).obj J)
      n 0 n (zero_add n)) := by
  classical
  let L := sectionFreeComplex Λ X P
  let M := (complexForward Λ X).obj J
  let H := homComplex (R := ring Λ X) L M
  let Q := fun p : ℤ ↦ SheafOfModules.homObj (R := ring Λ X) (L.X p) (M.X (p + n))
  let π := fun p : ℤ ↦ homComplexπ (R := ring Λ X) L M n p (p + n) rfl
  have hc : IsLimit (Fan.mk (H.X n) π) := homComplexIsLimit L M n
  have hz (p : ℤ) (hp : p ≠ 0) : IsZero (Q p) := by
    have hL : IsZero (L.X p) :=
      (equivalence Λ X).functor.map_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (pulledFree Λ X P) p hp)
    rw [IsZero.iff_id_eq_zero,
      ← SheafOfModules.homObjMap_id (R := ring Λ X), hL.eq_of_src (𝟙 (L.X p)) 0]
    apply SheafOfModules.hom_ext
    ext U φ : 3
    change (PresheafOfModules.restrictOver (ring Λ X).obj U.unop).map 0 ≫ φ ≫
      (PresheafOfModules.restrictOver (ring Λ X).obj U.unop).map
        (𝟙 (M.X (p + n)) : M.X (p + n) ⟶ M.X (p + n)).val = 0
    ext W x
    change ((φ.app W).hom) 0 = 0
    exact map_zero _
  let v : Q 0 ⟶ H.X n := Fan.IsLimit.lift hc
    (fun p ↦ if hp : p = 0 then eqToHom (congrArg Q hp.symm) else 0)
  have hv : v ≫ π 0 = 𝟙 (Q 0) := by
    change Fan.IsLimit.lift hc _ ≫ (Fan.mk (H.X n) π).proj 0 = _
    rw [Fan.IsLimit.fac]
    simp
  have hπ : π 0 ≫ v = 𝟙 (H.X n) := by
    apply Fan.IsLimit.hom_ext hc
    intro p
    change (π 0 ≫ v) ≫ π p = 𝟙 (H.X n) ≫ π p
    by_cases hp : p = 0
    · subst p
      rw [Category.assoc, hv, Category.comp_id, Category.id_comp]
    · exact (hz p hp).eq_of_tgt _ _
  have hi : IsIso (π 0) := (Iso.mk (π 0) v hπ hv).isIso_hom
  have hi' (q : ℤ) (hq : 0 + n = q) : IsIso (homComplexπ L M n 0 q hq) := by
    subst q
    exact hi
  exact hi' n (zero_add n)

private lemma homMap_zero_source
    (E F N : Modules Λ X) :
    SheafOfModules.homObjMap (R := ring Λ X) (0 : E ⟶ F) (𝟙 N) = 0 := by
  apply SheafOfModules.hom_ext
  ext U φ : 3
  change (PresheafOfModules.restrictOver (ring Λ X).obj U.unop).map 0 ≫ φ ≫
    (PresheafOfModules.restrictOver (ring Λ X).obj U.unop).map (𝟙 N : N ⟶ N).val = 0
  ext W x
  change ((φ.app W).hom) 0 = 0
  exact map_zero _

/-- The surviving Hom projection intertwines the differential with postcomposition.
Source: Stacks Project Tag 08J7 (blueprint: new-f3-profinite-free-slice-hom-projection).
Proof: the product Hom differential formula has a postcomposition term and a
precomposition term. All differentials of the source single complex are zero;
linearity makes its precomposition term zero. The first term is the assertion. -/
theorem freeHomComponent_d (J : CochainComplex (Internal Λ X) ℤ)
    (n m : ℤ) (h : n + 1 = m) :
    (homComplex (R := ring Λ X) (sectionFreeComplex Λ X P)
      ((complexForward Λ X).obj J)).d n m ≫
        coefficientHomComponent.{u, u + 1, u} (Scheme.ProEt.topology X)
          (ring Λ X) (sectionFreeComplex Λ X P) ((complexForward Λ X).obj J)
          m 0 m (zero_add m) =
    coefficientHomComponent.{u, u + 1, u} (Scheme.ProEt.topology X)
      (ring Λ X) (sectionFreeComplex Λ X P) ((complexForward Λ X).obj J)
      n 0 n (zero_add n) ≫
        SheafOfModules.homObjMap (R := ring Λ X) (𝟙 _)
          (((complexForward Λ X).obj J).d n m) := by
  have hd := homComplex_d_π (R := ring Λ X) (sectionFreeComplex Λ X P)
    ((complexForward Λ X).obj J) n m 0 m n (m - n) h (zero_add m) (zero_add n)
      (by omega)
  have hz : (sectionFreeComplex Λ X P).d 0 (m - n) = 0 := by
    change (sectionForward Λ X).map ((freeComplex Λ X P).d 0 (m - n)) = 0
    rw [HomologicalComplex.single_obj_d, Functor.map_zero]
  rw [hz, homMap_zero_source, comp_zero, smul_zero, sub_zero] at hd
  exact hd

end AlgebraicGeometry.ProEtale.ProfiniteFreeSlice
