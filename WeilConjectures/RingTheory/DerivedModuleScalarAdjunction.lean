/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic

/-! # Left adjoints to derived restriction of module scalars

Derived restriction of scalars along a map of commutative rings has a left adjoint on the
unbounded derived categories.

## Implementation details

No flatness or boundedness hypothesis is needed. First put rings and modules in the same
universe. Free modules give functorial flat resolutions, and scalar extension followed by
restriction is tensoring with `S` over `R`, so scalar extension preserves K-flat
quasi-isomorphisms. The general derived-adjunction theorem then applies to ordinary scalar
extension and restriction. For a larger module universe, replace `R` and `S` by their universe
lifts and transport the adjunction along the induced derived equivalences.

## References

* [Stacks, Tag 09T5] (derived adjoint functors)
* [Stacks, More on Algebra, tensor-hom adjunction]
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace ModuleCat

private theorem hasFunctorialFlatResolution_sameUniverse (R : Type u) [CommRing R] :
    Abelian.HasFunctorialFlatResolution (ModuleCat.{u} R) := by
  classical
  let F := ObjectProperty.lift ObjectProperty.flat
    (forget (ModuleCat.{u} R) ⋙ free R) (fun M ↦ by
      apply (flat_iff_flat _).2
      change Module.Flat R (M →₀ R)
      infer_instance)
  refine ⟨{ F := F, π := (adj R).counit, epi_π_app := ?_ }⟩
  intro M
  apply (epi_iff_surjective _).2
  intro x
  refine ⟨freeMk x, ?_⟩
  change freeDesc (𝟙 (forget (ModuleCat.{u} R)).obj M) (freeMk x) = x
  simp only [freeDesc_apply]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem derivedRestrictScalars_isRightAdjoint_sameUniverse
    {R S : Type u} [CommRing R] [CommRing S]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} S)] (φ : R →+* S) :
    (restrictScalars.{u} φ).mapDerivedCategory.IsRightAdjoint := by
  have := hasFunctorialFlatResolution_sameUniverse R
  let F := extendScalars φ
  have : F.Additive := (extendRestrictScalarsAdj φ).left_adjoint_additive
  let B : ModuleCat.{u} R := (restrictScalars φ).obj (of S S)
  let eobj (M : ModuleCat.{u} R) :
      (F ⋙ restrictScalars φ).obj M ≅ (tensorLeft B).obj M :=
    (AddEquiv.toLinearEquiv (M := ↑((F ⋙ restrictScalars φ).obj M))
      (M₂ := ↑((tensorLeft B).obj M)) (AddEquiv.refl _) (by
        intro r z
        induction z using TensorProduct.inductionOn with
        | tmul s m => rfl
        | add a b ha hb =>
            simpa only [map_add, smul_add] using congrArg₂ (· + ·) ha hb)).toModuleIso
  let e : F ⋙ restrictScalars φ ≅ tensorLeft B := NatIso.ofComponents eobj (by
    intro M N f
    ext z
    rfl)
  have : F.PreservesKFlatQuasiIso := by
    apply Functor.PreservesKFlatQuasiIso.mk' F
    intro K hK hKa
    have ht := CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa B
    have hl := ht.of_iso
      ((NatIso.mapHomologicalComplex
        (BraidedCategory.tensorLeftIsoTensorRight B) _).app K).symm
    have he : (((F ⋙ restrictScalars φ).mapHomologicalComplex _).obj K).Acyclic :=
      hl.of_iso ((NatIso.mapHomologicalComplex e _).app K).symm
    intro i
    exact (ShortComplex.exact_map_iff_of_faithful _ (restrictScalars φ)).1 (he i)
  have : AB5OfSize.{0, 0} (ModuleCat.{u} R) := AB5OfSize_of_univLE.{0, 0, u, u} _
  have : HasExactColimitsOfShape ℤ (ModuleCat.{u} R) := inferInstance
  exact ((extendRestrictScalarsAdj φ).derivedAdjunction.ofNatIsoRight
    (restrictScalars φ).rightDerivedFunctorIsoMapDerivedCategory).isRightAdjoint

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Exact derived restriction of scalars along a map of commutative rings has a left
adjoint on the unbounded derived categories, in any module universe at least that of
both rings. -/
theorem derivedRestrictScalars_isRightAdjoint
    {R S : Type u} [CommRing R] [CommRing S]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} S)] (φ : R →+* S) :
    (restrictScalars.{max u v} φ).mapDerivedCategory.IsRightAdjoint := by
  let := HasDerivedCategory.standard (ModuleCat.{max u v} (ULift.{v} R))
  let := HasDerivedCategory.standard (ModuleCat.{max u v} (ULift.{v} S))
  let r : R →+* ULift.{v} R := ULift.ringEquiv.symm.toRingHom
  let s : ULift.{v} S →+* S := ULift.ringEquiv.toRingHom
  let ψ : ULift.{v} R →+* ULift.{v} S := φ.ulift
  have : (restrictScalars.{max u v} r).mapDerivedCategory.IsRightAdjoint :=
    inferInstance
  have : (restrictScalars.{max u v} s).mapDerivedCategory.IsRightAdjoint :=
    inferInstance
  have : (restrictScalars ψ).mapDerivedCategory.IsRightAdjoint :=
    derivedRestrictScalars_isRightAdjoint_sameUniverse ψ
  let e : restrictScalars.{max u v} φ ≅
      (restrictScalars s ⋙ restrictScalars ψ) ⋙ restrictScalars r :=
    restrictScalarsComp' r (s.comp ψ) φ (RingHom.comp_ulift_eq.{v, v} φ).symm ≪≫
      Functor.isoWhiskerRight (restrictScalarsComp ψ s) (restrictScalars r)
  let ed : (restrictScalars φ).mapDerivedCategory ≅
      ((restrictScalars s).mapDerivedCategory ⋙
        (restrictScalars ψ).mapDerivedCategory) ⋙
        (restrictScalars r).mapDerivedCategory :=
    Functor.mapDerivedCategoryNatIso e ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso _ _).symm _
  exact Functor.isRightAdjoint_of_iso ed.symm

end ModuleCat
