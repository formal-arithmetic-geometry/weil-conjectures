/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.NativeL2MiddleImage
public import WeilConjectures.AlgebraicGeometry.CurveMiddleExtension
public import WeilConjectures.AlgebraicGeometry.CurvePerverseHeartStatement.CurvePerverseHeartStatement
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import WeilConjectures.AlgebraicGeometry.CondensedCurveIntermediateExtension.CondensedCurveBoundarySupport
import WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-! # The ordinary sheaf comparison for a minimal extension -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open scoped CategoryTheory.Obj
open WeilConjectures
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CurvePerverseHeartStatement
namespace AlgebraicGeometry.ProEtale.CondensedCurveIntermediateExtension

set_option maxHeartbeats 2000000 in
-- Geometric instance synthesis and derived comparisons require a larger elaboration budget.
set_option synthInstance.maxHeartbeats 200000 in
/-- The ordinary adjoint comparison is invertible once its punctual obstruction vanishes.
Source: rem-dl-a1-conventions, intermediate-extension argument, step 6.
Proof: the open counit makes the pullback of the adjoint comparison invertible.
Exact pullback and Serre closure make its kernel and cokernel constructible and
killed by restriction, hence punctual. The source has no punctual subobject, so
its kernel is zero. The resulting short exact sequence has zero connecting map
by hypothesis. Exactness of Hom into its distinguished triangle gives a section
of the cokernel projection. Thus the cokernel is a punctual subobject of the
target, so is zero as well. In an abelian category a mono and epi is invertible.
(blueprint: lem-dl-a1-condensed-curve-minimal-sheaf-comparison). -/
theorem boundary_minimal_sheaf_comparison
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (c : Scheme.MiddleExtensionCurve D) [GeometricallyConnected c.C.hom]
    (F : StrictWeilCondensed.WeilModule (coeff ell) (frobU D c))
    (M : Modules D ell (geomC D c))
    (hM : IsConstructibleModuleObject (condensedRingObj (coeff ell) (geomC D c)) M)
    (hA : IsConstructibleModuleObject (condensedRingObj (coeff ell) (geomC D c))
      (image D ell c F))
    (hNoM : NoPunctualSubobject (Punctual ell (geomC D c)) M)
    (hNoA : NoPunctualSubobject (Punctual ell (geomC D c)) (image D ell c F))
    (α : (CondensedRing.upperStar (coeff ell) (geomJ D c)).obj M ≅ F.carrier)
    (hδ : ∀ B : Modules D ell (geomC D c), Punctual ell (geomC D c) B →
      IsZero ((CondensedRing.upperStar (coeff ell) (geomJ D c)).obj B) →
      ∀ δ : (DerivedCategory.singleFunctor _ 0).obj B ⟶
        ((shiftFunctor _ (1 : ℤ)).obj ((DerivedCategory.singleFunctor _ 0).obj M)), δ = 0)
    (hCounit : IsIso ((CondensedRing.upperStarLowerStarAdjunction
      (coeff ell) (geomJ D c)).counit.app F.carrier)) :
    IsIso ((CondensedRing.upperStarLowerStarAdjunction (coeff ell) (geomJ D c)).homEquiv
      M F.carrier α.hom) := by
  classical
  let L := CondensedRing.upperStar (coeff ell) (geomJ D c)
  let adj := CondensedRing.upperStarLowerStarAdjunction (coeff ell) (geomJ D c)
  let f := adj.homEquiv M F.carrier α.hom
  have hf : L.map f ≫ adj.counit.app F.carrier = α.hom := by
    exact (adj.homEquiv M F.carrier).symm_apply_apply α.hom
  have : IsIso (L.map f ≫ adj.counit.app F.carrier) := hf ▸ inferInstance
  have : IsIso (L.map f) := IsIso.of_isIso_comp_right (L.map f)
    (adj.counit.app F.carrier)
  have hK : IsZero (L.obj (kernel f)) :=
    (isZero_kernel_of_mono (L.map f)).of_iso (PreservesKernel.iso L f)
  have hC : IsZero (L.obj (cokernel f)) :=
    (isZero_cokernel_of_epi (L.map f)).of_iso (PreservesCokernel.iso L f)
  have : IsLocallyNoetherian c.C.left := LocallyOfFiniteType.isLocallyNoetherian c.C.hom
  let a := Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  have : LocallyOfFiniteType (D.geometricFiber c.C).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd c.C.hom a))
  have : QuasiCompact (D.geometricFiber c.C).hom :=
    inferInstanceAs (QuasiCompact (pullback.snd c.C.hom a))
  have : IsLocallyNoetherian (geomC D c) :=
    LocallyOfFiniteType.isLocallyNoetherian (D.geometricFiber c.C).hom
  have : IsNoetherian (geomC D c) := ⟨⟩
  obtain ⟨hKc, hCc⟩ := (isConstructibleModuleObject_serre_padicAlgCl
    (geomC D c) ell).1 M (image D ell c F) f hM hA
  have hKp := boundary_support_punctual D ell c (kernel f) hKc hK
  have hCp := boundary_support_punctual D ell c (cokernel f) hCc hC
  have hzK := hNoM (kernel f) (kernel.ι f) inferInstance hKp
  have : Mono f := Preadditive.mono_of_isZero_kernel f hzK
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
  have hzδ : hS.singleδ = 0 := hδ (cokernel f) hCp hC hS.singleδ
  obtain ⟨s, hs⟩ := hS.singleTriangle.coyoneda_exact₃ hS.singleTriangle_distinguished
    (𝟙 _) (by simpa using hzδ)
  let σ := (DerivedCategory.singleFunctor (Modules D ell (geomC D c)) 0).preimage s
  have hσ : σ ≫ cokernel.π f = 𝟙 _ := by
    apply (DerivedCategory.singleFunctor (Modules D ell (geomC D c)) 0).map_injective
    change (DerivedCategory.singleFunctor (Modules D ell (geomC D c)) 0).map
      ((DerivedCategory.singleFunctor (Modules D ell (geomC D c)) 0).preimage s ≫ S.g) = _
    rw [Functor.map_comp, Functor.map_preimage, CategoryTheory.Functor.map_id]
    exact hs.symm
  have : Mono σ := ⟨fun g h he ↦ by
    have := congrArg (fun t ↦ t ≫ cokernel.π f) he
    simpa only [Category.assoc, hσ, Category.comp_id] using this⟩
  have hzC := hNoA (cokernel f) σ inferInstance hCp
  have : Epi f := Preadditive.epi_of_isZero_cokernel f hzC
  exact isIso_of_mono_of_epi f

end AlgebraicGeometry.ProEtale.CondensedCurveIntermediateExtension
