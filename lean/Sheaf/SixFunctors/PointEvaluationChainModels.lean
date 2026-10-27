/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.SixFunctors.PointEvaluationTensorCoherence
public import Sheaf.SixFunctors.PointEvaluationScalarCoherence
/-! Normalized chain models for final-object evaluation.
(blueprint: lem-sf-point-evaluation-chain-models). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] SheafOfModules.monoidalCategory
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.CochainPullback
namespace AlgebraicGeometry.ProEtale.PointEvaluation
/-- Normalized tensor and scalar chain models.
Source: Stacks 03EL and 07A4, total-complex construction.
(blueprint: lem-sf-point-evaluation-chain-models).

Proof: Evaluation of sheafification at the final object is an isomorphism because
every covering sieve contains its identity. Its inverse identifies the sheaf tensor
with the tensor of sections, sending pure tensors to the sheafification unit.
The right adjoint lax monoidal structure therefore becomes strong monoidal.
Extend it to direct-sum total complexes. The comparison on each summand is the
module comparison, and the unit is the degree-zero identity. The standard total
associator and unitors give coherence; the braiding uses the same Koszul sign
on both sides. K-flatness follows by the ringed-point stalk criterion and flatness
of module inverse image. For a coefficient map, evaluating the sheafified scalar
extension gives ordinary scalar extension. Its tensor comparison is balanced:
(1 tensor x) tensor (1 tensor y) maps to 1 tensor (x tensor y). Extend this identity
by linearity and by the coproduct injections of every total degree. Scalar
extension preserves flat-term K-flat complexes by the ringed-pullback criterion. -/
theorem point_evaluation_chain_models (k : Type u) [Field k] [IsAlgClosed k] :
    ∃ T : ∀ B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1},
        TensorModel B,
      (∀ B, TensorCoherent B (T B) ∧
        ∀ [(pointModuleSections k B).PreservesZeroMorphisms],
          HEq (T B).unit
            ((HomologicalComplex.singleMapHomologicalComplex (W₁ := ModuleSheaves B)
              (W₂ := ModuleCat.{u + 1} (sectionRing k B)) (pointModuleSections k B)
              (.up ℤ) 0).app
              (SheafOfModules.unit.{u, u + 1, u + 1}
                ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
                  (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)) ≪≫
              (HomologicalComplex.single (ModuleCat.{u + 1} (sectionRing k B))
                (.up ℤ) 0).mapIso (T B).moduleUnit)) ∧
      ∀ (B B' : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{u + 1})
        (a : B ⟶ B'), ∃ S : ScalarModel a (T B) (T B'), ScalarCoherent a (T B) (T B') S := by
  sorry

end AlgebraicGeometry.ProEtale.PointEvaluation
