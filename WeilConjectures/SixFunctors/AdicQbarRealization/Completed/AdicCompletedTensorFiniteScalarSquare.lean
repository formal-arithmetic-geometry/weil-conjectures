/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorStageComponent

/-! # Scalar square for normalized finite completed tensor components

Source: BS Remark 6.8.15; HRS Lemma 7.9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.AdicQbarRealization.ordinary

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
  (R : LocallyFiniteAdicRealization.Realization l X)
  [∀ x : X, Invertible (l : X.residueField x)]
  (closed : CoefficientClosedStructure (ambientHom l X R))
  (models : CoefficientTensorModels.{u + 1, u + 1, u}
    (ProEt.topology X) (ring l X R) closed)

/-- The scalar square for two objects of one rational coefficient stage.
Only the two finite models occur; no component at an arbitrary common-stage pair is used.
Source: BS Definition 3.4.10 and Remark 6.8.15; HRS Proposition 5.2 and Lemma 7.9.
(blueprint: lem-sf-adic-completed-tensor-finite-scalar-square).

Proof: choose flat-term K-flat integral representatives of K.obj and L.obj. The
finite-free completed scalar comparison identifies their extensions to F with the
recorded completed scalar extensions. Expand the representative equations of NE and
NF and the normalized completion comparisons. The scalar associator is the canonical
pbcReductionNormalization; R.coefficient_scalar identifies its direct coefficient map.
On a homogeneous pure section s tensor (x tensor y), the two balance_sections equations
and ordinary scalar associativity give the same generator, with factors s tensor x
and 1 tensor y. Balancing, sheafification, and the total coproduct inclusions extend
this equality to the complete chain maps. The completion coaugmentation has the
specified quotient coordinate and zero shifted coordinate, so the equality commutes
with the whole completion map. Pass to derived categories, cancel the invertible
K-flat counits and constructible completion comparisons, and transport along the
chosen representative isomorphisms. The common_field equations for R identify the
three boundary scalar comparisons with ordinary.map of isoToStage. The normalized
integral tensor scalar comparison, its rationalized component equation, and the
common-stage tensor representative formula identify the output boundary with the
common tensor of the two isoToStage maps. Finally, the normalization of stageTensor
identifies it with the natural commonInclusionTensorComparison used in the stage
components. This proves the square. The argument uses only two coefficient fields
and two integral representatives, retains the scalar unit when E = F, and uses no
nonzero object or faithful realization hypothesis. -/
theorem completedTensorStageComponent_scalar
    (E F : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) (h : E ≤ F)
    (NE : CompletedTensorFiniteModel l X R closed models E)
    (NF : CompletedTensorFiniteModel l X R closed models F)
    (K L : sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) :
    let I := GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := X) E
    let a := (GeneralAlgebraicallyClosedCoefficients.stageSystem l
      (PadicAlgCl l) X).isoToStage (I.obj K) h
    let b := (GeneralAlgebraicallyClosedCoefficients.stageSystem l
      (PadicAlgCl l) X).isoToStage (I.obj L) h
    (((ordinary l X R).prod (ordinary l X R)) ⋙ closed.tensor).map
        (Prod.mkHom a.hom b.hom) ≫
      (completedTensorStageComponent l X R closed models F NF
        ((I.obj K).toStage h) ((I.obj L).toStage h)).hom =
    (completedTensorStageComponent l X R closed models E NE K L).hom ≫
      (commonStageDerivedTensor l (PadicAlgCl l) X ⋙ ordinary l X R).map
        (Prod.mkHom a.hom b.hom) := by sorry

end WeilConjectures.AdicQbarRealization
