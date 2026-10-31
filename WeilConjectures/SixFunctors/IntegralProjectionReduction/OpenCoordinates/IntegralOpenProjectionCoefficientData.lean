/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.ProperCoordinates.IntegralProperProjectionCoefficientData

/-! # Natural coefficient coordinates for an integral open extension

Source: prop-sf-pf-coherence.proof.md, compatibility with the open adjunction.
(blueprint: def-sf-integral-open-projection-coefficient-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralProjectionReduction.OpenCoordinates
open IntegralSystemRealization FixProjectionCompactification.Coordinates ProperCoordinates

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
  (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k))
  (o : Operations C.l E) (z : Realizations C.l E D o)

include hl

/-- The specified scalar mate is invertible on constructible inputs.
Source: open reconstruction effectivity and residue Tor
(blueprint: def-sf-integral-open-projection-coefficient-data). -/
theorem reduction_isIso {X Y : SixFunctorSpace D} (j : X ⟶ Y)
    (hj : IsOpenImmersion j.hom.left) [QuasiCompact j.hom.left]
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    IsIso ((z.realizationModel.openReduction C.l E j.hom.left).app K.obj) := by
  let := residueUnits hl X
  let := hj
  have hK : finiteTorConstructibleIntegral C.l E X.obj.left K.obj := by
    rw [← (integral_residue_tor D C.l C.different E X.obj.left).2]
    exact K.property
  exact (GeneratorReduction.openReconstructionEffectivity C.l E o z.realizationModel
    j.hom.left K.obj (Or.inl hK)).1

/-- Reduction of open extension, with the ordinary realization and inverse scalar mate.
The inverse is constructed componentwise, using its proved invertibility.
Source: the normalized open realization
(blueprint: def-sf-integral-open-projection-coefficient-data). -/
def extensionComparison {X Y : SixFunctorSpace D} (j : X ⟶ Y)
    (hj : IsOpenImmersion j.hom.left) [QuasiCompact j.hom.left] :
    S.higher.integral.openExtension j hj ⋙ reduce Y ≅
      reduce X ⋙ Operations.shriek C.l E o j.hom.left := by
  letI := hj
  let F := (sfIntegralConstructible C.l E X.obj.left).ι
  let R := (calculus C.l E Y.obj.left).reduction
  let α := Functor.whiskerLeft F
    (z.realizationModel.openReduction C.l E j.hom.left)
  have hα (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
      IsIso (α.app K) := reduction_isIso hl o z j hj K
  letI := hα
  letI : IsIso α := NatIso.isIso_of_isIso_app α
  exact Functor.isoWhiskerRight (S.integralNormalization.openRealization j hj) R ≪≫
    (asIso α).symm

/-- The component formula retains precisely the actual scalar mate.
Source: the preceding construction
(blueprint: def-sf-integral-open-projection-coefficient-data). -/
theorem extensionComparison_hom_app {X Y : SixFunctorSpace D} (j : X ⟶ Y)
    (hj : IsOpenImmersion j.hom.left) [QuasiCompact j.hom.left]
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    let := reduction_isIso hl o z j hj K
    (extensionComparison S hl o z j hj).hom.app K =
      (calculus C.l E Y.obj.left).reduction.map
        ((S.integralNormalization.openRealization j hj).hom.app K) ≫
      inv ((z.realizationModel.openReduction C.l E j.hom.left).app K.obj) := by
  simp only [extensionComparison, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Iso.symm_hom, asIso_inv,
    NatIso.isIso_inv_app, Functor.whiskerLeft_app, ObjectProperty.ι_obj]

end WeilConjectures.IntegralProjectionReduction.OpenCoordinates
