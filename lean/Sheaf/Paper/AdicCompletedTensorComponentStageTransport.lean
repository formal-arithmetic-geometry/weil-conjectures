/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.AdicCompletedTensorStageComponent

/-! # Naturality of the explicit completed tensor components

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

/-- The component computed at the compositum agrees with its computation at any
larger coefficient field, conjugated by the actual isoToStage maps.
Source: BS Definition 3.4.10 and Remark 6.8.15; HRS Proposition 5.2 and Lemma 7.9.
(blueprint: lem-sf-adic-completed-tensor-component-stage-transport).

Proof: let E be the compositum of the input fields and enlarge E to L. Choose good
K-flat representatives of the two integral objects at E. Expand the representative
clauses of the finite models at E and L, replacing their completion comparisons by
the normalized cochain completion maps. The scalar counits on these representatives
are invertible. Cancel them using the K-flat model normalization. In bidegree (p,q)
the balance_sections equations identify both scalar tensor comparisons on the pure
section s tensor (x tensor y): both send it to the tensor of s tensor x and 1 tensor y.
The coefficient_scalar equation identifies the composite coefficient maps. The tensor
universal property and sheafification give equality in each bidegree; the totalization
coproduct injections then give equality of complex maps. Pass to the derived category
and transport by the good representative isomorphisms. The common_field equation of
R identifies its boundary comparisons with ordinary.map of the actual isoToStage
maps. Naturality and tower compatibility of the integral scalar tensor comparison,
and the normalized formula of stageTensor, identify the output comparison. The
existing natural inclusion comparison has that same formula: expand its component,
use functoriality of mapIso and associativity of isomorphism composition, and apply
uniqueness in stageTensor_existsUnique. Thus its component is precisely stageTensor.
Pasting with the two endpoint isoToStage maps in the definition of the common component gives
the displayed equation. Reflexive extensions retain their normalized scalar unit;
no nonzero object, nonempty scheme, or faithful coefficient extension is required. -/
theorem completedTensorCommonComponent_stage_transport
    (symmetry : @SymmetricCategory _ _ closed.monoidal)
    (N : ∀ E, CompletedTensorFiniteModel l X R closed models E)
    (coherence : RingedDerivedTensorCoherence.{u + 1, u, u + 1}
      (ProEt.topology X) (ring l X R) closed models symmetry)
    (P Q : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) X)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (hP : P.stage ≤ E) (hQ : Q.stage ≤ E) :
    let a := (GeneralAlgebraicallyClosedCoefficients.stageSystem l
      (PadicAlgCl l) X).isoToStage P hP
    let b := (GeneralAlgebraicallyClosedCoefficients.stageSystem l
      (PadicAlgCl l) X).isoToStage Q hQ
    (completedTensorCommonComponent l X R closed models N P Q).hom =
      (((ordinary l X R).prod (ordinary l X R)) ⋙ closed.tensor).map
          (Prod.mkHom a.hom b.hom) ≫
        (completedTensorStageComponent l X R closed models E (N E)
          (P.toStage hP) (Q.toStage hQ)).hom ≫
        (commonStageDerivedTensor l (PadicAlgCl l) X ⋙ ordinary l X R).map
          (Prod.mkHom a.inv b.inv) := by sorry

end WeilConjectures.AdicQbarRealization
