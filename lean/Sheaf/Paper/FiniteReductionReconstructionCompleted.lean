/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.Paper.IntrinsicCompletionCompleted
public import Sheaf.Paper.SequentialDerivedInverseLimitCompleted
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Sheaf.Paper.FiniteProjectiveTensorProducts
import Sheaf.Paper.CompletedReconstructionUnitComparison
import Sheaf.Paper.CompletedFiniteReductionTensorModel

/-! # Finite reduction of reconstruction over completed coefficients

Source: blueprint, proper base change, order 1249; Stacks Tags 099M and 091Z
(blueprint: lem-weil-pbc-finite-reduction-reconstruction).

Every tensor and product is in D(Mod(A_T)). The finite quotient-coefficient object
retains its quotient action for the scalar adjunction. A naturality square of limits
means a map compatible with their evaluations; no functorial triangle vertex is chosen.

## Main statements

* `finiteReductionReconstructionCompleted`: the specified counit is an isomorphism,
  naturally in complete objects, and finite reduction commutes with the Roos products.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
variable (d : ProEtaleAdicCoefficientDatum A)

/-- Evaluation of the derived limit in quotient coefficients, followed by the inverse
of the universal K-flat comparison. This specifies the map, including its scalar action.
Source: order 1249 (blueprint: lem-weil-pbc-finite-reduction-reconstruction). -/
def completedReconstructionEvaluation {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K)
    (L : CompletedSequentialDerivedLimit T d (adicDatumModelTower T d M)) (n : ℕ) :
    L.obj ⟶ (adicDatumReductionUnderlying T d n).obj K :=
  L.p ≫ Pi.π (fun a : ℕ ↦ (adicDatumModelTower T d M).obj (op a)) n ≫
    (adicDatumModelRestriction T d M n).hom ≫
    (adicDatumRestriction T (adicDatumProjection T d n)).map
      (adicDatumModelReductionIso T d M n).inv

/-- The specified derived counit is the adjunct of evaluation, rather than an
arbitrary isomorphism between its source and target.
Source: order 1249 (blueprint: lem-weil-pbc-finite-reduction-reconstruction). -/
def completedReconstructionCounit {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K)
    (L : CompletedSequentialDerivedLimit T d (adicDatumModelTower T d M)) (n : ℕ) :
    (adicDatumReduction T d n).obj L.obj ⟶ (adicDatumReduction T d n).obj K :=
  ((adicDatumAdjunction T (adicDatumProjection T d n)).homEquiv _ _).symm
    (completedReconstructionEvaluation T d M L n)

/-- Canonical comparison from tensor of the product to product of the tensors.
Both product vertices of the Roos triangle use precisely this comparison.
Source: order 1249 (blueprint: lem-weil-pbc-finite-reduction-reconstruction). -/
def completedReconstructionProductComparison {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (n : ℕ) :
    (adicDatumReductionUnderlying T d n).obj
      (∏ᶜ (fun a : ℕ ↦ (adicDatumModelTower T d M).obj (op a))) ⟶
      ∏ᶜ (fun a : ℕ ↦ (adicDatumReductionUnderlying T d n).obj
        ((adicDatumModelTower T d M).obj (op a))) :=
  Pi.lift (fun a ↦ (adicDatumReductionUnderlying T d n).map
    (Pi.π (fun b : ℕ ↦ (adicDatumModelTower T d M).obj (op b)) a))

/-- Finite reduction of reconstruction, with its canonical counit, its naturality,
and the common canonical comparison at the two Roos-product vertices.
The naturality clause quantifies over maps of derived limits compatible with evaluation,
which is the meaning of a morphism when the derived-limit notation is a Roos triple.

Source: order 1249; Stacks Tags 099M and 091Z
(blueprint: lem-weil-pbc-finite-reduction-reconstruction).

Proof:
1. Apply lem-weil-pbc-completed-constant-sheaf-reduction to identify the sheaf tensor
of A_T and P_a over constant A with the completed quotient. A finite-projective resolution over
A therefore gives a bounded complex of finite-projective A_T-modules representing it.
2. Apply prop-weil-pbc-koszul-reconstruction to identify intrinsic completion with strict
quotient-tower completion map. Completeness makes that map an isomorphism, and its
composite with every evaluation is the canonical finite reduction map.
3. Under the normalized derived scalar adjunction, the adjunct of that reduction map
is the identity of the finite reduction. Thus the displayed counit composed with the
reduced completion is the identity; it is the inverse of an isomorphism. Any Roos triple
is isomorphic to the representative computation compatibly with its product map, so the
conclusion holds for every L here. The adjunction hom equivalence and the universal
K-flat comparisons give the displayed naturality square.
4. Apply lem-weil-pbc-finite-projective-tensor-products to the bounded model in step 1:
its tensor commutes with countable products termwise. Exact products identify those
products with derived products, giving invertibility of the canonical comparison.
In prop-weil-pbc-roos-triangle, both vertices use that product comparison. Naturality in
the transitions identifies their middle map with one minus the tensor transition shift;
no assertion that the reduced tower is constant is used. -/
theorem finiteReductionReconstructionCompleted {K : adicDatumDerived T d}
    (M : AdicDatumModel T d K) (r : ℕ) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = d.ideal)
    (hcomplete : IsCompletedIntrinsicallyDerivedComplete T d r f hf
      M.complex M.realization)
    (L : CompletedSequentialDerivedLimit T d (adicDatumModelTower T d M)) (n : ℕ) :
    IsIso (completedReconstructionCounit T d M L n) ∧
    IsIso (completedReconstructionProductComparison T d M n) ∧
    ∀ {K' : adicDatumDerived T d} (N : AdicDatumModel T d K')
      (_hcomplete' : IsCompletedIntrinsicallyDerivedComplete T d r f hf
        N.complex N.realization)
      (L' : CompletedSequentialDerivedLimit T d (adicDatumModelTower T d N))
      (v : K ⟶ K') (w : L.obj ⟶ L'.obj),
      (∀ a : ℕ, completedReconstructionEvaluation T d M L a ≫
        (adicDatumReductionUnderlying T d a).map v =
          w ≫ completedReconstructionEvaluation T d N L' a) →
      completedReconstructionCounit T d M L n ≫ (adicDatumReduction T d n).map v =
        (adicDatumReduction T d n).map w ≫ completedReconstructionCounit T d N L' n := by
  obtain ⟨e, he⟩ := completedReconstructionUnitComparison T d M r f hf hcomplete L
  let adj := adicDatumAdjunction T (adicDatumProjection T d n)
  have hunit : e.hom ≫ completedReconstructionEvaluation T d M L n =
      adj.unit.app K := he n
  have hcomp : (adicDatumReduction T d n).map e.hom ≫
      completedReconstructionCounit T d M L n = 𝟙 _ := by
    unfold completedReconstructionCounit
    change (adicDatumExtension T (adicDatumProjection T d n)).map e.hom ≫
      (adj.homEquiv _ _).symm (completedReconstructionEvaluation T d M L n) = _
    calc
      _ = (adj.homEquiv _ _).symm
          (e.hom ≫ completedReconstructionEvaluation T d M L n) :=
        (adj.homEquiv_naturality_left_symm _ _).symm
      _ = (adj.homEquiv _ _).symm (adj.unit.app K) := congrArg _ hunit
      _ = 𝟙 _ := adj.homEquiv_symm_unit K
  have hCounit : IsIso (completedReconstructionCounit T d M L n) := by
    have : IsIso ((adicDatumReduction T d n).map e.hom) := inferInstance
    have : IsIso ((adicDatumReduction T d n).map e.hom ≫
        completedReconstructionCounit T d M L n) := by rw [hcomp]; infer_instance
    exact IsIso.of_isIso_comp_left ((adicDatumReduction T d n).map e.hom) _
  obtain ⟨P, hb, p, ⟨j⟩⟩ := completedFiniteReductionTensorModel T d n
  let C := fun a : ℕ ↦ (adicDatumModelTower T d M).obj (op a)
  have : IsIso (piComparison (finiteProjectiveTensorRight T d P hb p) C) :=
    (finiteProjectiveTensorProducts T d P hb p C).1
  have : PreservesLimit (Discrete.functor C) (finiteProjectiveTensorRight T d P hb p) :=
    PreservesProduct.of_iso_comparison _ _
  have : PreservesLimit (Discrete.functor C) (adicDatumReductionUnderlying T d n) :=
    preservesLimit_of_natIso _ j.symm
  have hProduct : IsIso (completedReconstructionProductComparison T d M n) := by
    change IsIso (piComparison (adicDatumReductionUnderlying T d n) C)
    infer_instance
  refine ⟨hCounit, hProduct, ?_⟩
  intro K' N hNcomplete L' v w hcompat
  let adj := adicDatumAdjunction T (adicDatumProjection T d n)
  unfold completedReconstructionCounit
  have hright := adj.homEquiv_naturality_right_symm
    (completedReconstructionEvaluation T d M L n)
    ((adicDatumReduction T d n).map v)
  have hleft := adj.homEquiv_naturality_left_symm w
    (completedReconstructionEvaluation T d N L' n)
  calc
    _ = (adj.homEquiv _ _).symm
        (completedReconstructionEvaluation T d M L n ≫
          (adicDatumRestriction T (adicDatumProjection T d n)).map
            ((adicDatumReduction T d n).map v)) := by
      exact hright.symm
    _ = (adj.homEquiv _ _).symm
        (w ≫ completedReconstructionEvaluation T d N L' n) := by
      exact congrArg (adj.homEquiv _ _).symm (hcompat n)
    _ = (adicDatumExtension T (adicDatumProjection T d n)).map w ≫
        (adj.homEquiv _ _).symm (completedReconstructionEvaluation T d N L' n) := hleft
    _ = _ := rfl

end AlgebraicGeometry.Scheme
