/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.PoincareFiniteReduction.PoincareFiniteReductionData
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

/-! # Native site-perfect complexes under scalar extension

Source: latest blueprint lem-fix-operation-reduction.proof.md, local projective models
(blueprint: lem-pod-native-scalar-site-perfect).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace WeilConjectures.PoincareFiniteReduction

set_option maxHeartbeats 2000000 in
-- Native projective models retain large derived and coefficient instances.
/-- Arbitrary native coefficient extension preserves site-perfect complexes.
Source: lem-fix-operation-reduction.proof.md, first paragraph
(blueprint: lem-pod-native-scalar-site-perfect).
Proof in words. Keep the model cover. On each chart extend the bounded complex
termwise. Every finite-projective term is a retract of a finite sum of regular
modules. Extension preserves its splitting and identifies the extended free sum
with the free sum over the target coefficient. The original projective terms are
dualizable and flat, so their bounded complex is K-flat. The universal derived
counit therefore identifies scalar extension with the termwise extension on this
model. The normalized scalar/pullback isomorphism and the original local model
isomorphism give the required local model for the extended complex. The original
bounds remain valid, including empty covers and rank-zero projectives. No flatness
of the coefficient map is required.
-/
theorem nativeScalarSitePerfect {A B : ScalarSixRing.{u}} (a : A ⟶ B)
    (X : Scheme.{u})
    (K : DerivedCategory (ModuleRingedComparison.internalModules A.X X))
    (hK : IsPerfectOnCoefficientSite A.X X K) :
    IsPerfectOnCoefficientSite B.X X ((scalarSixChange a X).obj K) := by
  obtain ⟨C, hC⟩ := hK
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨P, l, h, hl, hh, hp, ⟨eP⟩⟩ := hC i
  let := hl
  let := hh
  let φ := coefficientMap (Λ := A.X) (Λ' := B.X) a.hom.hom (C.X i)
  let F := Mod.extendScalars φ
  let P' := (F.mapHomologicalComplex (.up ℤ)).obj P
  have hfree (r : ℕ) : F.obj (Mod.finiteFree (condensedRingObj A.X (C.X i)) r) ≅
      Mod.finiteFree (condensedRingObj B.X (C.X i)) r :=
    F.mapBiproduct (fun _ : Fin r ↦ Mod.regular _) ≪≫
      biproduct.mapIso (fun _ ↦ Mod.regularExtensionIso φ)
  have hp' (q : ℤ) : IsFiniteProjectiveOnCoefficientSite B.X (C.X i) (P'.X q) := by
    obtain ⟨r, ⟨s⟩⟩ := hp q
    exact ⟨r, ⟨(s.map F).trans (Retract.ofIso (hfree r))⟩⟩
  have hflat (q : ℤ) : ObjectProperty.flat (P.X q) :=
    (CategoryTheory.finProj.isDualizable (hp q)).flat
  have hk := CochainComplex.kFlat_of_bounded_of_flat P l h hflat
  have := F.isIso_leftDerivedFunctorCounit_app_of_kFlat P hk
  let ed : (scalarSixChange a (C.X i)).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj P' :=
    F.leftDerivedFunctor.mapIso ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫
      asIso (F.leftDerivedFunctorCounit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≪≫
      (DerivedCategory.quotientCompQhIso _).app P'
  refine ⟨P', l, h, ?_, ?_, hp', ⟨?_⟩⟩
  · dsimp only [P']
    infer_instance
  · dsimp only [P']
    infer_instance
  · exact (scalarPullbackIso a (C.f i)).symm.app K ≪≫
      (scalarSixChange a (C.X i)).mapIso eP ≪≫ ed

end WeilConjectures.PoincareFiniteReduction
