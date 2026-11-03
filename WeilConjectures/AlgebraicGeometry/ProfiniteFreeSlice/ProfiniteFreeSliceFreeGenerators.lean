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
import WeilConjectures.AlgebraicGeometry.ProfiniteFreeSlice.ProfiniteFreeSliceRepresentable

/-! # Free modules and their normalized generators

Source: HRS Section 3; Stacks Tag 08J7
(blueprint: new-c1-profinite-free-slice-free-generators).

The free-module comparison is induced by the represented-parameter comparison.
The adjunction-unit equation fixes its image of the universal generator, so the
parent comparison uses a specified free isomorphism throughout the later steps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ProfiniteFreeSlice
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] (X : Scheme.{u})

set_option synthInstance.maxSize 4096 in
private def pulledFreeAdjunction :
    (Profinite.CondensedAction.InternalBar.free (Mon.mk Λ) ⋙ pointModulePullback Λ X) ⊣
      ((Mod.forget (condensedRingObj Λ X) ⋙
        sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})) ⋙
          (Scheme.proEtaleSheafDirectImage (toSpecZ X) (Type (u + 1)) ⋙
            profiniteToProEt.sheafPushforwardContinuous (Type (u + 1))
              (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ))) := by
  have hm : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      (abelianAdjunction X) Functor.Monoidal.toOplaxMonoidal _ := by
    unfold abelianAdjunction
    exact Adjunction.isMonoidal_comp _ _
  exact (Profinite.CondensedAction.InternalBar.freeAdjunction (Mon.mk Λ)).comp
    ((abelianAdjunction X).mapModAdjunction Λ)


variable (P : Profinite.{u})
/-- The pullback of the free condensed module is free on the relative test object,
with its unit generator fixed.
Source: HRS Section 3; Stacks Tag 08J7
(blueprint: new-c1-profinite-free-slice-free-generators).
Proof: compose the free condensed-module adjunction with the lifted monoidal
point inverse-image adjunction. Its right adjoint agrees definitionally with
that of set inverse image followed by the local free-module adjunction.
Uniqueness of left adjoints gives a natural isomorphism. Evaluate it on h_P
and compose with localFree applied to the represented-parameter comparison.
The unit equation for uniqueness of left adjoints identifies the transpose of
this composite with the local free unit after the set comparison. Naturality
of the local free unit and the proved set-generator equation give the displayed
identity-generator equation. This argument uses universal free sheaves, and
applies to empty P and to the zero coefficient ring. -/
theorem exists_free_comparison : ∃ e : pulledFree Λ X P ≅ freeOnTest Λ X P,
    ((((abelianAdjunction X).unit.app (freeParameter Λ P).X ≫
      (AlgebraicGeometry.ProEtale.lowerStar Ab.{u + 1} (toSpecZ X) ⋙ pointLowerStar).map
        e.hom.hom).hom.app (op P))
        (pointGenerator Λ P)) = testGenerator Λ X P (test X P) (𝟙 (test X P)) := by
  obtain ⟨e, he⟩ := exists_set_comparison X P
  let a := pulledFreeAdjunction Λ X
  let b := (setAdjunction X).comp (localFreeAdjunction Λ X)
  let d := a.leftAdjointUniq b
  let f : pulledFree Λ X P ≅ freeOnTest Λ X P :=
    d.app (parameter P) ≪≫ (localFree Λ X).mapIso e
  refine ⟨f, ?_⟩
  have h : a.homEquiv _ _ f.hom =
      b.homEquiv _ _ ((localFree Λ X).map e.hom) := by
    change a.homEquiv _ _ (d.hom.app (parameter P) ≫ (localFree Λ X).map e.hom) = _
    rw [a.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app a b]
    rfl
  change ((a.homEquiv _ _ f.hom).hom.app (op P)) (ULift.up (𝟙 P)) = _
  rw [h]
  change (((setAdjunction X).homEquiv _ _
    ((localFreeAdjunction Λ X).homEquiv _ _ ((localFree Λ X).map e.hom))).hom.app
      (op P)) (ULift.up (𝟙 P)) = _
  have hl : (localFreeAdjunction Λ X).homEquiv _ _ ((localFree Λ X).map e.hom) =
      e.hom ≫ (localFreeAdjunction Λ X).unit.app (represented X P) := by
    rw [← Category.comp_id ((localFree Λ X).map e.hom),
      Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_id]
  erw [hl, Adjunction.homEquiv_naturality_right]
  change (((localFreeAdjunction Λ X).unit.app (represented X P)).hom.app
    (op (test X P))) ((((setAdjunction X).homEquiv _ _ e.hom).hom.app
      (op P)) (ULift.up (𝟙 P))) = _
  exact congrArg (fun z ↦ (((localFreeAdjunction Λ X).unit.app
    (represented X P)).hom.app (op (test X P))) z) he

end AlgebraicGeometry.ProEtale.ProfiniteFreeSlice
