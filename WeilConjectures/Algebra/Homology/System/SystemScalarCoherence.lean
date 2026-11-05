/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemScalarModel
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition

/-! # Coherent ordinary scalar extension

Source: Stacks 03D7 and 03EK; the uniqueness of the tensor/restriction adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [EssentiallySmall.{w} C]

/-- Restriction along a composite is successive restriction, with identity section maps.
Source: Stacks 03CZ (blueprint: lem-pur-system-scalar-coherence). -/
def systemScalarRestrictionComposition {R S T : Sheaf J CommRingCat.{w}}
    (φ : R ⟶ S) (ψ : S ⟶ T) (γ : R ⟶ T) (hγ : γ = φ ≫ ψ) :
    (restrictScalars.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map ψ)) ⋙ (restrictScalars.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ)) ≅ (restrictScalars.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map γ)) :=
  NatIso.ofComponents (fun M ↦ (fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (φ.hom.app U).hom (ψ.hom.app U).hom
        (γ.hom.app U).hom (congrArg (fun f ↦ (f.hom.app U).hom) hγ)
        (M.val.obj U)).symm) (by intros; ext x; rfl)))
    (by intros; ext U x; rfl)

/-- Restriction along an identity coefficient map is the identity on sections.
Source: Stacks 03CZ (blueprint: lem-pur-system-scalar-coherence). -/
def systemScalarRestrictionUnit {R : Sheaf J CommRingCat.{w}}
    (φ : R ⟶ R) (hφ : φ = 𝟙 R) :
    restrictScalars.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map φ) ≅
      𝟭 (ringedSiteModules.{w} (derivedChangeRingIndependentCoefficients J R)) :=
  NatIso.ofComponents (fun M ↦ (fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      ModuleCat.restrictScalarsId'App (φ.hom.app U).hom
        (congrArg (fun f ↦ (f.hom.app U).hom) hφ) (M.val.obj U))
      (by intros; ext x; rfl))) (by intros; ext U x; rfl)

end SheafOfModules
