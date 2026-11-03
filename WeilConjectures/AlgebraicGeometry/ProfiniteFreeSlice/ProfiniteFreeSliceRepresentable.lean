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
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale.PullbackYoneda

/-! # The represented parameter comparison

Source: Stacks Project, Sites, Tag 04D3 and HRS Section 3.
(blueprint: new-c1-profinite-free-slice-representable).

The inverse image of the represented profinite parameter is identified with
the represented pro-etale test object. The adjunction-unit normalization is
proved at the identity parameter and fixes the later free-module generators.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w u₁ u₂
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.ProfiniteFreeSlice

private theorem representable_generator
    {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]
    {G : C ⥤ D} {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    [G.IsContinuous J K] [J.Subcanonical] [K.Subcanonical]
    {L : Sheaf J (Type (max v w)) ⥤ Sheaf K (Type (max v w))}
    (a : L ⊣ G.sheafPushforwardContinuous (Type (max v w)) J K) (c : C) :
    ((a.homEquiv _ _ ((a.uliftYonedaCompIso.app c).hom)).hom.app (op c))
      (ULift.up (𝟙 c)) = ULift.up (𝟙 (G.obj c)) := by
  have h := a.uliftYonedaEquiv_uliftYonedaCompHom_comp c
    ((a.uliftYonedaCompIso.app c).hom)
  have hid : a.uliftYonedaCompHom c ≫ (a.uliftYonedaCompIso.app c).hom = 𝟙 _ :=
    (a.uliftYonedaCompIso.app c).inv_hom_id
  rw [hid] at h
  exact h.symm

/-- Inverse image of the represented profinite parameter, with its unit generator fixed.
Source: Stacks Project Tag 04D3; HRS Section 3
(blueprint: new-c1-profinite-free-slice-representable).
Proof: apply the inverse-image Yoneda comparison first to profinite sets over Spec Z,
then to base change to X. The adjunct of each comparison sends the identity to the
identity, by the inverse identity for the Yoneda comparison. Naturality of each
adjunction identifies the adjunct of the composite with the composite of those
adjuncts, proving the required generator equation. -/
theorem exists_set_comparison (X : Scheme.{u}) (P : Profinite.{u}) :
    ∃ e : (profinitePointSetSchemeInverseImage X).obj (parameter P) ≅ represented X P,
      ((((setAdjunction X).unit.app (parameter P) ≫
        (Scheme.proEtaleSheafDirectImage (toSpecZ X) (Type (u + 1)) ⋙
          profiniteToProEt.sheafPushforwardContinuous (Type (u + 1))
            (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)).map
              e.hom).hom.app (op P)) (ULift.up (𝟙 P))) =
          ULift.up (𝟙 (test X P)) := by
  let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous profiniteToProEt
    (Type (u + 1)) (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)
  let b := Scheme.proEtaleSheafAdjunction (toSpecZ X) (Type (u + 1))
  let e₁ := a.uliftYonedaCompIso.{u + 1}.app P
  let e₂ := b.uliftYonedaCompIso.{u + 1}.app (profiniteToProEt.obj P)
  let e : (profinitePointSetSchemeInverseImage X).obj (parameter P) ≅ represented X P :=
    (Scheme.proEtaleSheafInverseImage (toSpecZ X) (Type (u + 1))).mapIso e₁ ≪≫ e₂
  refine ⟨e, ?_⟩
  change (((a.comp b).homEquiv _ _ e.hom).hom.app (op P))
    (ULift.up (𝟙 P)) = _
  rw [Adjunction.comp_homEquiv]
  change ((a.homEquiv _ _ (b.homEquiv _ _
    ((Scheme.proEtaleSheafInverseImage (toSpecZ X) (Type (u + 1))).map e₁.hom ≫
      e₂.hom))).hom.app (op P)) (ULift.up (𝟙 P)) = _
  rw [b.homEquiv_naturality_left, a.homEquiv_naturality_right]
  change ((b.homEquiv _ _ e₂.hom).hom.app (op (profiniteToProEt.obj P)))
    (((a.homEquiv _ _ e₁.hom).hom.app (op P)) (ULift.up (𝟙 P))) = _
  have h₁ := representable_generator.{u, u + 1, u + 1, u + 1} a P
  have h₂ := representable_generator.{u, u + 1, u + 1, u + 1} b
    (profiniteToProEt.obj P)
  exact (congrArg (fun z ↦ ((b.homEquiv _ _ e₂.hom).hom.app
    (op (profiniteToProEt.obj P))) z) h₁).trans h₂

end AlgebraicGeometry.ProEtale.ProfiniteFreeSlice
