/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage

/-! # Canonical coefficient isomorphism in section-ring coordinates

This isolates the adjunct-normalized coefficient construction from Tate-twist and
coefficient-tower machinery. Its complete proof is reused from CartesianCoefficientTwists.
Source: blueprint coefficient morphisms and proper base change proof (2).
(blueprint: def-pbc-canonical-coefficient-section-isomorphism)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj
namespace AlgebraicGeometry.ProEtale.CoefficientSection
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
attribute [local irreducible] abelianPullbackForgetIso ringPullbackForgetIso
  condensedPushforwardHom


/-- The ring-sheaf encoding of alpha is uniquely fixed by its abelian adjunct.
Source: blueprint coefficient compatibility, lem-sfb-alpha-iso
(blueprint: def-pbc-canonical-coefficient-section-isomorphism).
Proof: reconstruct section rings from the internal multiplication. The coefficient
adjunct is a ring homomorphism since condensedPullbackHom is monoidal. Lift the
abelian adjunction to ring objects. Its adjunct determines the map uniquely, and
alpha is invertible by lem-sfb-alpha-iso; forgetting reflects isomorphisms. -/
theorem existsUnique
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    ∃! c : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology Y)
          (condensedRingObj Λ Y)) ≅
        InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
          (condensedRingObj Λ X),
      ∀ (V : Y.ProEtᵒᵖ) (a : (condensedRingObj Λ Y).obj.obj V),
        (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _)
          c.hom).hom.app V a = (condensedPushforwardHom Λ f).hom.app V a := by
  apply sectionRingPullbackIso_ofMonHom f (condensedRingObj Λ Y)
    (condensedRingObj Λ X) (condensedPullbackHom Λ f) (condensedPushforwardHom Λ f)
  exact (abelianAdjunct_eq f _ _ _).trans (unitAlgHom_comp_map_condensedPullbackHom Λ f)

/-- Alpha, in commutative ring sheaves, selected by its unique adjunct normalization.
Source: blueprint coefficient compatibility
(blueprint: def-pbc-canonical-coefficient-section-isomorphism). -/
def iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :=
  Classical.choose (existsUnique f Λ)


end AlgebraicGeometry.ProEtale.CoefficientSection
