/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryRingedTensorUnderivedData
public import Submission.WeilConjectures.WeilSheaf.Native.Weil.Tensor.NativeWeilTensorRingedAssociatorChainData

import Submission.WeilConjectures.WeilSheaf.Ordinary.OrdinaryRingedTensorCoherenceData

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Normalization of the ordinary comparison on tensor complexes -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

attribute [local instance] Mod.monoidalCategoryCochainComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  (b : NativeWeilTensorRingedBridge k₀ l X)

/-- The normalized ordinary comparison for a native bridge.
Source: Stacks 06YU, 0FPT
(blueprint: new-sf-native-ordinary-ringed-tensor-chain-comparison). -/
abbrev NativeOrdinaryRingedTensorChainComparison
    (κ : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ,
      ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P Q ≅ Q ⊗ P)
    (d : NativeOrdinaryRingedTensorUnderivedData b) :=
  OrdinaryRingedTensorChainComparison l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
    b.K b.Q b.ordinary b.ordinaryHom κ d

set_option synthInstance.maxHeartbeats 200000 in
-- Compare the ordinary and ringed tensor instances through their APIs.
set_option maxHeartbeats 1200000 in
-- The concrete tensor constructions require large definitional equalities.
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The ordinary equivalence has its evaluation-normalized associative comparison
on unbounded tensor complexes.
Source: Stacks 06YS, 06YU and 0FPT
(blueprint: new-sf-native-ordinary-ringed-tensor-chain-comparison).

Proof: apply the ordinary coherence retained in the bridge to the supplied
balanced-summand normalization of `κ` and the specified underived mate `d`.
The bridge existence proof retains this property from the canonical section
model. This does not infer coherence from naturality of an arbitrary Hom map. -/
theorem native_ordinary_ringed_tensor_chain_comparison
    (κ : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ,
      ordinaryTensorTotal l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber P Q ≅ Q ⊗ P)
    (hκ : ∀ (P Q : CochainComplex (ProEtale.AdicSheaf l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ)
        (p q n : ℤ) (hpq : p + q = n) (hqp : q + p = n),
      Mod.tensorπ (Q.X q) (P.X p) ≫
          (HomologicalComplex.ιMapBifunctor P Q
            (ordinaryTensorBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
            (.up ℤ) p q n hpq).hom ≫ ((κ P Q).hom.f n).hom =
        (p * q).negOnePow • (Mod.tensorObjπ (Q.X q) (P.X p) ≫
          (HomologicalComplex.ιTensorObj Q P q p n hqp).hom))
    (d : NativeOrdinaryRingedTensorUnderivedData b) :
    Nonempty (NativeOrdinaryRingedTensorChainComparison b κ d) := by
  exact b.ordinary_coherence.2 κ hκ d

end AlgebraicGeometry.ProEtaleWeilSheaf
