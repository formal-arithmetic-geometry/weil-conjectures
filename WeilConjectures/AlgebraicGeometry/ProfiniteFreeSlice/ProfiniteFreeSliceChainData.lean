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
import WeilConjectures.AlgebraicGeometry.ProfiniteFreeSlice.ProfiniteFreeSliceUnderivedData
import WeilConjectures.AlgebraicGeometry.ProfiniteFreeSlice.ProfiniteFreeSliceHomProjection

/-! # The natural profinite free chain model

Source: Stacks Project Tags 08FI, 08J7; HRS Section 3.
(blueprint: new-f3-profinite-free-slice-chain-data).

The chain comparison uses the degree-zero Hom projection and the underived
comparison. Its evaluation field retains the chosen free-generator map in every
degree, and its chain-map equation is obtained from naturality in the differential.
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

/-- The underived free-generator chain isomorphism, natural in its target.
Source: Stacks Project Tag 08J7 (blueprint: new-f3-profinite-free-slice-chain-data). -/
structure ChainComparisonData (freeIso : pulledFree Λ X P ≅ freeOnTest Λ X P) where
  representative : ∀ (J : CochainComplex (Internal Λ X) ℤ),
    homComplex (R := ring Λ X) (sectionFreeComplex Λ X P) ((complexForward Λ X).obj J) ≅
      (complexForward Λ X).obj ((sliceComplex Λ X P).obj J)
  evaluation : ∀ (J : CochainComplex (Internal Λ X) ℤ)
      (n : ℤ) (V : X.ProEt)
      (φ : ((homComplex (R := ring Λ X) (sectionFreeComplex Λ X P)
        ((complexForward Λ X).obj J)).X n).val.obj (op V)),
    (((representative J).hom.f n).val.app (op V)) φ =
      (sectionToSlice Λ X P (J.X n) V).hom
        (evaluateHomSection Λ X P freeIso J n V φ)
  naturality : ∀ {J J' : CochainComplex (Internal Λ X) ℤ} (a : J ⟶ J'),
    (((homComplexFunctor (R := ring Λ X)).obj (op (sectionFreeComplex Λ X P))).map
      ((complexForward Λ X).map a)) ≫ (representative J').hom =
        (representative J).hom ≫ (complexForward Λ X).map ((sliceComplex Λ X P).map a)

/-- Evaluation on the relative representable gives a natural chain isomorphism.
Source: Stacks Project Tag 08J7; HRS Section 3
(blueprint: new-f3-profinite-free-slice-chain-data).

Proof: use exists_underived_comparison_data for the natural module-level
free-generator evaluation. In degree n, project the product Hom complex onto
its (0,n) factor by freeHomComponent_isIso, and compose with that evaluation
at J.X n. The differential identity freeHomComponent_d leaves only
postcomposition by d_J. Naturality of the underived isomorphism with respect
to d_J is therefore exactly the chain condition. Assemble the degreewise
isomorphisms by HomologicalComplex.Hom.isoOfComponents. The evaluation field
is the underived evaluation applied to the projected section. The product
Hom map formula followed by naturality with respect to a.f n proves the
naturality field. These arguments use no boundedness or K-injectivity. -/
theorem exists_chain_comparison_data
    (freeIso : pulledFree Λ X P ≅ freeOnTest Λ X P) :
    Nonempty (ChainComparisonData Λ X P freeIso) := by
  obtain ⟨d⟩ := exists_underived_comparison_data Λ X P freeIso
  have hπ (J : CochainComplex (Internal Λ X) ℤ) (n : ℤ) :=
    freeHomComponent_isIso Λ X P J n
  let π := fun (J : CochainComplex (Internal Λ X) ℤ) (n : ℤ) ↦
    coefficientHomComponent.{u, u + 1, u} (Scheme.ProEt.topology X) (ring Λ X)
      (sectionFreeComplex Λ X P) ((complexForward Λ X).obj J) n 0 n (zero_add n)
  let e (J : CochainComplex (Internal Λ X) ℤ) :
      homComplex (R := ring Λ X) (sectionFreeComplex Λ X P) ((complexForward Λ X).obj J) ≅
        (complexForward Λ X).obj ((sliceComplex Λ X P).obj J) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ asIso (π J n) ≪≫ d.iso.app (J.X n)) (by
        intro n m h
        change (π J n ≫ d.iso.hom.app (J.X n)) ≫
          ((restriction Λ X P ⋙ directImage Λ X P) ⋙ (equivalence Λ X).functor).map
            (J.d n m) = _
        rw [Category.assoc, ← d.iso.hom.naturality (J.d n m), ← Category.assoc]
        have hd :
            (homComplex (R := ring Λ X) (sectionFreeComplex Λ X P)
              ((complexForward Λ X).obj J)).d n m ≫ π J m =
            π J n ≫ ((equivalence Λ X).functor ⋙
              (SheafOfModules.homFunctor (ring Λ X)).obj
                (op ((sectionFreeComplex Λ X P).X 0))).map (J.d n m) :=
          freeHomComponent_d Λ X P J n m h
        rw [← hd]
        rfl)
  refine ⟨{ representative := e, evaluation := ?_, naturality := ?_ }⟩
  · intro J n V φ
    exact d.evaluation (J.X n) V ((π J n).val.app (op V) φ)
  · intro J J' a
    ext n : 1
    change (((homComplexFunctor (R := ring Λ X)).obj
      (op (sectionFreeComplex Λ X P))).map ((complexForward Λ X).map a)).f n ≫
        (π J' n ≫ d.iso.hom.app (J'.X n)) =
      (π J n ≫ d.iso.hom.app (J.X n)) ≫
        ((restriction Λ X P ⋙ directImage Λ X P) ⋙ (equivalence Λ X).functor).map (a.f n)
    have ha :
        (((homComplexFunctor (R := ring Λ X)).obj
          (op (sectionFreeComplex Λ X P))).map ((complexForward Λ X).map a)).f n ≫
            π J' n = π J n ≫ ((equivalence Λ X).functor ⋙
              (SheafOfModules.homFunctor (ring Λ X)).obj
                (op ((sectionFreeComplex Λ X P).X 0))).map (a.f n) :=
      homComplexFunctor_obj_map_f_π ((complexForward Λ X).map a) n 0 n (zero_add n)
    rw [← Category.assoc, ha, Category.assoc, d.iso.hom.naturality (a.f n),
      ← Category.assoc]

end AlgebraicGeometry.ProEtale.ProfiniteFreeSlice
