module

public import Sheaf.Paper.EtaleSystemDerivedTensorEvaluation

/-! # Tensor pullback on the actual strict étale systems

Source: Stacks 03EL, 07A4 and 0G7E
(blueprint: def-coef-etale-system-image-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.Etale.SystemCompactSupport
open SystemProjection

/-- The recorded additive inverse image, exposed for its representative model.
Source: Stacks 07A4 (blueprint: def-coef-etale-system-image-tensor). -/
instance imageInverseAdditive {X Y : Scheme.{u}} {g : X ⟶ Y}
    {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (d : Image g B) : d.inverse.Additive :=
  d.inverseAdditive

/-- The recorded left exact inverse image.
Source: Stacks 07A4 (blueprint: def-coef-etale-system-image-tensor). -/
instance imageInverseLimits {X Y : Scheme.{u}} {g : X ⟶ Y}
    {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (d : Image g B) :
    PreservesFiniteLimits d.inverse := d.inverseLimits

/-- The recorded right exact inverse image.
Source: Stacks 07A4 (blueprint: def-coef-etale-system-image-tensor). -/
instance imageInverseColimits {X Y : Scheme.{u}} {g : X ⟶ Y}
    {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (d : Image g B) :
    PreservesFiniteColimits d.inverse := d.inverseColimits

/-- Representative model of inverse image on the actual sequence sites.
Source: Stacks 07A4 (blueprint: def-coef-etale-system-image-tensor). -/
def imageTensorModel {X Y : Scheme.{u}} {g : X ⟶ Y}
    {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (d : Image g B)
    (AY : Calculus Y B) (AX : Calculus X B)
    (mu : AY.closed.tensor ⋙ d.P ≅ (d.P.prod d.P) ⋙ AX.closed.tensor) :=
  letI := d.inverseAdditive
  letI := d.inverseLimits
  letI := d.inverseColimits
  TensorComparisonModel.{u + 1, u, u + 1}
    (WeilConjectures.coefficientSequenceTopology Y.smallEtaleTopology)
    (WeilConjectures.coefficientSequenceTopology X.smallEtaleTopology)
    (rings Y B) (rings X B) d.inverse AY.closed AX.closed AY.tensorModels AX.tensorModels mu

/-- The canonical tensor pullback, fixed on unit-generated local pure tensors and
on every total-complex summand before deriving.
Source: Stacks 03EL and 07A4
(blueprint: def-coef-etale-system-image-tensor). -/
structure ImageTensor {X Y : Scheme.{u}} {g : X ⟶ Y}
    {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (d : Image g B)
    (AY : Calculus Y B) (AX : Calculus X B) where
  mu : AY.closed.tensor ⋙ d.P ≅ (d.P.prod d.P) ⋙ AX.closed.tensor
  model : imageTensorModel d AY AX mu
  pure : ∀ (M N : Modules Y B) (n : ℕ) (U : Y.Etaleᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) (y : N.val.obj (op (n, U.unop))),
    ((model.ordinary M N).hom.val.app
      (op (n, (MorphismProperty.Over.pullback @Etale ⊤ g).obj U.unop)))
        (((d.adjunction.unit.app (ordinaryTensor.{u + 1, u, u + 1}
          (WeilConjectures.coefficientSequenceTopology Y.smallEtaleTopology)
          (rings Y B) M N)).val.app (op (n, U.unop)))
            (tensorSection.{u + 1, u, u + 1}
              (WeilConjectures.coefficientSequenceTopology Y.smallEtaleTopology)
              (rings Y B) M N (op (n, U.unop)) x y)) =
      tensorSection.{u + 1, u, u + 1}
        (WeilConjectures.coefficientSequenceTopology X.smallEtaleTopology)
        (rings X B) (d.inverse.obj M) (d.inverse.obj N)
        (op (n, (MorphismProperty.Over.pullback @Etale ⊤ g).obj U.unop))
        (((d.adjunction.unit.app M).val.app (op (n, U.unop))) x)
        (((d.adjunction.unit.app N).val.app (op (n, U.unop))) y)

end AlgebraicGeometry.Etale.SystemCompactSupport
