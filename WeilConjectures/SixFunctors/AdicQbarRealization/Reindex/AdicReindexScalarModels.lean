/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Reindex.AdicReindexScalarData
public import WeilConjectures.SixFunctors.AdicQbarRealization.Native.NativeAdicReindexingData

/-! # Ordinary models for the balanced scalar rectangle

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: def-sf-adic-reindex-scalar-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option Elab.async false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.podCompletedRingMap AlgebraicGeometry.ProEtale.inverseImageCompletedCoefficientMap

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.AdicQbarRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (i : E →ₐ[ℚ_[l]] L)

set_option maxHeartbeats 800000 in
-- Equality transport compares the ring isomorphisms without unfolding their inverses.
/-- Equality transport of the ordinary completed inverse-image models.
Source: BS 6.8.15 (blueprint: def-sf-adic-reindex-scalar-models). -/
@[irreducible] def completedReindexSheafModel {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    podCompletedModuleInverseImage l E g ≅ inverseImageIntegralModules l E g :=
  eqToIso (congrArg (fun (c : (isoSectionwiseInverseImage g RingCat.{u + 1}).obj
        (completedIntegralCoefficientSheafUnrestricted l E Y) ≅
          completedIntegralCoefficientSheafUnrestricted l E X) ↦
      isoSectionwiseModuleInverseImage.{u, u} g c.hom)
    (show asIso (podCompletedRingMap l E g) =
        asIso (inverseImageCompletedCoefficientMap l E g) from
      Iso.ext (completedRingReindex_eq l E g)))

private theorem reindex_transport_apply
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    {A : Sheaf (ProEt.topology Y) RingCat.{u + 1}}
    {D : Sheaf (ProEt.topology X) RingCat.{u + 1}}
    (c d : (isoSectionwiseInverseImage g RingCat.{u + 1}).obj A ≅ D)
    (h : c = d) (M : SheafOfModules.{u + 1} A) (U : X.ProEtᵒᵖ)
    (x : M.val.obj ((proEtaleIsoPostcompose g).op.obj U)) :
    ((eqToIso (congrArg
      (fun e ↦ isoSectionwiseModuleInverseImage.{u, u} g e.hom) h)).hom.app M).val.app U x =
        x ∧
    ((eqToIso (congrArg
      (fun e ↦ isoSectionwiseModuleInverseImage.{u, u} g e.hom) h)).inv.app M).val.app U x =
        x := by
  subst d
  exact ⟨rfl, rfl⟩

/-- The ordinary model comparison fixes every underlying section.
Source: equality transport, BS 6.8.15 (blueprint: def-sf-adic-reindex-scalar-models). -/
theorem completedReindexSheafModel_apply {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (M : integralTowerModules l E Y) (U : X.ProEtᵒᵖ)
    (x : M.val.obj ((proEtaleIsoPostcompose g).op.obj U)) :
    ((completedReindexSheafModel l E g).hom.app M).val.app U x = x ∧
      ((completedReindexSheafModel l E g).inv.app M).val.app U x = x := by
  unfold completedReindexSheafModel
  exact reindex_transport_apply g (asIso (podCompletedRingMap l E g))
    (asIso (inverseImageCompletedCoefficientMap l E g))
    (Iso.ext (completedRingReindex_eq l E g)) M U x

/-- Ordinary scalar reindexing with exactly the models used in completedScalarReindex.
Source: BS 6.8.14--6.8.15 (blueprint: def-sf-adic-reindex-scalar-models). -/
def completedScalarSheafReindex {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    podCompletedModuleInverseImage l E g ⋙ completedOrdinaryScalarExtension l E L i X ≅
      completedOrdinaryScalarExtension l E L i Y ⋙ podCompletedModuleInverseImage l L g :=
  Functor.isoWhiskerLeft _ (isomorphismScalarSheafModel l E L i X).symm ≪≫
    Functor.isoWhiskerRight (completedReindexSheafModel l E g) _ ≪≫
    isomorphismScalarTensor l E L i g ≪≫
    Functor.isoWhiskerLeft _ (completedReindexSheafModel l L g).symm ≪≫
    Functor.isoWhiskerRight (isomorphismScalarSheafModel l E L i Y) _

/-- Ordinary tensor flattening with the specified coefficient_scalar equality.
Source: BS 6.8.14; Stacks 03EK (blueprint: def-sf-adic-reindex-scalar-models). -/
def nativeScalarSheafAssociator (W : Scheme.{u})
    (R : LocallyFiniteAdicRealization.Realization l W)
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L) :
    completedOrdinaryScalarExtension l (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) L)
        (coefficientInclusion l (PadicAlgCl l) E L h) W ⋙
      pbcExtend (coefficientMap l W R L) ≅ pbcExtend (coefficientMap l W R E) :=
  Adjunction.leftAdjointCompIso
    (pbcScalarAdjunction (completedCoefficientMap l
      (Coefficient.{u} l (PadicAlgCl l) E) (Coefficient.{u} l (PadicAlgCl l) L)
      (coefficientInclusion l (PadicAlgCl l) E L h) W))
    (pbcScalarAdjunction (coefficientMap l W R L))
    (pbcScalarAdjunction (coefficientMap l W R E))
    (pbcRestrictComp _ _ _ (R.coefficient_scalar E L h))

end WeilConjectures.AdicQbarRealization
