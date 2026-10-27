/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.AlgebraicGeometry.CoherentGrothendieckSupport
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.RingTheory.KrullDimension.Basic
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.Modules.FiniteLocallyFreeTensorExact
import Mathlib.RingTheory.Length

/-! # Rank-zero vector-bundle operators lower coherent support dimension

Source: Stacks Project, Chow Homology, Tags 02S8 and 02S9; Homology, Tag 02MX;
the tensor-rank and coefficient-extension consequence spelled out in the DAG proof
(blueprint: lem-sfb-coherent-support-filtration-rank-action).
-/

@[expose] public section
set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

/-- Rank-zero tensor operators lower the dimension-support filtration integrally
and after extension to every commutative coefficient ring. Any finite linear
combination is nilpotent of exponent at most `d + 1`.

Source: Stacks, Chow Homology, 02S8 and 02S9; Homology, 02MX
(blueprint: lem-sfb-coherent-support-filtration-rank-action).

Proof:
1. Coherent modules on a locally Noetherian scheme are quasi-coherent of finite
   type (pqf-lem-coherent-ft-locnoeth), so their support is closed
   (lem-weil-pbc-finite-type-module-support-closed). Its dimension is bounded by
   that of X. Thus all generators belong to the top filtration step.
2. Local frames of a rank-n bundle identify its tensor with M locally with n
   copies of M. Coherence follows from locality and finite sums
   (lem-weil-pbc-coherent-modules-kernel-cokernel-sum). Tensor does not increase
   support and is exact (lem-sc-ext-tensor-exact), so induces a group operator.
3. At every k-dimensional generic point, the tensor stalk is n copies of the
   original stalk. Length additivity (lem-weil-pbc-length-additive-short-exact)
   makes its cycle n times the original cycle. The generic-cycle exact sequence
   (lem-sfb-coherent-support-cycle-exact-sequence) places the difference in the
   image of the group with support dimension at most k-1. These classes generate
   the filtration; this proves lowering, including k=0.
4. Extend the operator on pure tensors. Every element of the image filtration
   is a finite sum of tensors with integral factor in the integral filtration.
   Apply the integral inclusion term by term; no flatness is needed.
5. Each finite linear combination lowers the same B-submodule filtration.
   Inductively its r-th power sends the full group into step d-r. At r=d+1 this
   is the zero step. Distinct operators need not commute. Empty sums, rank zero,
   the empty scheme, d=0, the zero ring and integral torsion cause no exception. -/
theorem coherent_support_filtration_rank_action
    (F : Type u) [Field F] (X : Scheme.{u})
    [X.Over (Spec (.of F))] [LocallyOfFiniteType (X ↘ Spec (.of F))]
    [QuasiCompact (X ↘ Spec (.of F))] [IsLocallyNoetherian X] [CompactSpace X]
    (d : ℕ) (_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    coherentG0Filtration X (d : ℤ) = ⊤ ∧
    ∃ T : (E : X.Modules) → (n : ℕ) → E.IsFiniteLocallyFreeOfRank n →
        Module.End ℤ (CoherentG0 X),
      (∀ (E : X.Modules) (n : ℕ) (hE : E.IsFiniteLocallyFreeOfRank n)
        (M : CoherentObject X),
        ∃ h : RingedSpace.IsCoherent X.toRingedSpace (E ⊗ M.val),
          T E n hE (coherentG0Class M) = coherentG0Class ⟨E ⊗ M.val, h⟩) ∧
      (∀ (E : X.Modules) (n : ℕ) (hE : E.IsFiniteLocallyFreeOfRank n)
        (k : ℕ), k ≤ d → ∀ x : CoherentG0 X,
          x ∈ coherentG0Filtration X (k : ℤ) →
            (T E n hE - n • (LinearMap.id : Module.End ℤ (CoherentG0 X))) x ∈
              coherentG0Filtration X ((k : ℤ) - 1)) ∧
      (∀ (B : Type v) [CommRing B],
        (∀ (E : X.Modules) (n : ℕ) (hE : E.IsFiniteLocallyFreeOfRank n)
          (k : ℕ), k ≤ d → ∀ x : CoherentG0Scalars X B,
            x ∈ coherentG0ScalarFiltration X B (k : ℤ) →
              ((T E n hE).baseChange B -
                n • (LinearMap.id : Module.End B (CoherentG0Scalars X B))) x ∈
                coherentG0ScalarFiltration X B ((k : ℤ) - 1)) ∧
        (∀ (s : ℕ) (E : Fin s → X.Modules) (n : Fin s → ℕ)
          (hE : ∀ j : Fin s, (E j).IsFiniteLocallyFreeOfRank (n j)) (b : Fin s → B),
          (∑ j : Fin s, b j • ((T (E j) (n j) (hE j)).baseChange B -
            n j • (LinearMap.id : Module.End B (CoherentG0Scalars X B)))) ^ (d + 1) = 0)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
