module

public import Sheaf.Analysis.Calculus.OrientedSmoothVolume
public import Sheaf.Analysis.Calculus.SmoothDifferentialOperator
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Sheaf.Analysis.Calculus.CoordinateWeightedAdjoint
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Formal adjoints and their principal symbols

Source: Demailly, Complex Analytic and Differential Geometry, VI §1, (1.5)–(1.7),
printed pp.288–289 (blueprint: lem-sfb-differential-formal-adjoint-symbol).

The signed-adjoint symbol equality is expressed by its defining metric pairing, for
every local coefficient presentation of each operator. Thus it makes no choice of a
presentation or of an orthonormal frame. In orthonormal frames the equality says that
the degree-`d` coefficient matrices are the signed transposes. The covector ranges over
all coordinate covectors, equivalently all real cotangent vectors at the point.
-/

@[expose] public section

noncomputable section

universe u v w v₁ w₁

open Bundle MeasureTheory SmoothDifferentialOperator
open scoped ContDiff Manifold

namespace SmoothDifferentialOperator

variable {m : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (Fin m → ℝ) M]
  [MeasurableSpace M]
  {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : Type w} [NormedAddCommGroup K] [NormedSpace ℝ K]
  {G : M → Type v₁} {H : M → Type w₁}
  [TopologicalSpace (TotalSpace F G)] [TopologicalSpace (TotalSpace K H)]
  [∀ x, NormedAddCommGroup (G x)] [∀ x, InnerProductSpace ℝ (G x)]
  [∀ x, NormedAddCommGroup (H x)] [∀ x, InnerProductSpace ℝ (H x)]
  [FiberBundle F G] [VectorBundle ℝ F G] [FiberBundle K H] [VectorBundle ℝ K H]

/-- The formal-adjunction identity for smooth sections when either section has compact
topological support. Source: Demailly VI §1, (1.5), restricted to the compact-support cases
in the node (blueprint: lem-sfb-differential-formal-adjoint-symbol). -/
def IsFormalAdjointFor (μ : Measure M)
    (Q : ContMDiffSection (𝓘(ℝ, Fin m → ℝ)) F ∞ G →ₗ[ℝ]
      ContMDiffSection (𝓘(ℝ, Fin m → ℝ)) K ∞ H)
    (R : ContMDiffSection (𝓘(ℝ, Fin m → ℝ)) K ∞ H →ₗ[ℝ]
      ContMDiffSection (𝓘(ℝ, Fin m → ℝ)) F ∞ G) : Prop :=
  ∀ (v : ContMDiffSection (𝓘(ℝ, Fin m → ℝ)) F ∞ G)
    (w : ContMDiffSection (𝓘(ℝ, Fin m → ℝ)) K ∞ H),
    (IsCompact (closure {x : M | v x ≠ 0}) ∨
      IsCompact (closure {x : M | w x ≠ 0})) →
    (∫ x, inner ℝ ((Q v) x) (w x) ∂μ) = ∫ x, inner ℝ (v x) ((R w) x) ∂μ

/-- A smooth differential operator has a unique smooth differential formal adjoint of
the same order bound. Its degree-`d` symbol is `(-1)^d` times the fibrewise adjoint.
Source: Demailly VI §1, (1.5)–(1.7), pp.288–289
(blueprint: lem-sfb-differential-formal-adjoint-symbol).

Proof plan (the node's nine steps):
1. In an oriented chart with density ρ and Gram matrices M_G,M_H, construct
   Rw = (ρM_G)⁻¹ ∑ (-1)^|α| ∂^α(ρ b_αᵀ M_H w). The adjugate formula and
   `lem-sfb-smooth-nonzero-complex-reciprocal` give smooth inverses. Leibniz gives
   a real-linear differential expression of order at most d.
2. Specialize `lem-sfb-coordinate-weighted-adjoint` to one scalar derivative with
   unit density and metrics. Iterate integration by parts |α| times, and sum the
   components and multi-indices. Derivatives preserve the compact test support.
3. Subtract two local adjunction identities and test one component at a time.
   `lem-sfb-continuous-local-integrability`, `lem-sfb-smooth-test-ae-separation`,
   and `lem-sfb-continuous-ae-pointwise` give equality on compactly supported inputs.
4. Use `lem-sfb-euclidean-smooth-bump` to replace an arbitrary germ by a compact
   test equal near its base point. Locality gives uniqueness on every smooth germ.
5. Transform frames, metrics and densities on an overlap. Apply
   `lem-sfb-euclidean-jacobian-integral` to the pairings. Chain and product rules
   preserve the order bound; local uniqueness makes the candidates agree.
6. Glue these compatible smooth local outputs to a global real-linear operator.
7. Around the compact support choose finitely many charts and apply
   `lem-sfb-smooth-subordinate-partition` on their union. Decompose whichever
   input is compactly supported and sum the local identities. The integrands
   are integrable by `lem-sfb-continuous-compact-support-integrable`.
8. In Leibniz's formula only derivatives falling entirely on w contribute in
   degree d, giving (-1)^d M_G⁻¹ b_αᵀ M_H. This is the signed fibre adjoint,
   and becomes ordinary signed transpose in orthonormal frames.
9. Apply local uniqueness to any other global formal adjoint. The same formulas
   include d=0, actual order less than d, zero-rank bundles and the empty manifold.
   No compactness, completeness or finite-volume assumption on M is used.
-/
theorem exists_unique_formalAdjoint_symbol
    (hm : 1 ≤ m) [T2Space M] [SecondCountableTopology M] [BorelSpace M]
    [IsManifold (𝓘(ℝ, Fin m → ℝ)) ∞ M]
    [FiniteDimensional ℝ F] [FiniteDimensional ℝ K]
    [ContMDiffVectorBundle ∞ F G (𝓘(ℝ, Fin m → ℝ))]
    [ContMDiffVectorBundle ∞ K H (𝓘(ℝ, Fin m → ℝ))]
    [IsContMDiffRiemannianBundle (𝓘(ℝ, Fin m → ℝ)) ∞ F G]
    [IsContMDiffRiemannianBundle (𝓘(ℝ, Fin m → ℝ)) ∞ K H]
    (dV : Manifold.OrientedSmoothVolume (m := m) M) (d : ℕ)
    (Q : ContMDiffSection (𝓘(ℝ, Fin m → ℝ)) F ∞ G →ₗ[ℝ]
      ContMDiffSection (𝓘(ℝ, Fin m → ℝ)) K ∞ H)
    (hQ : IsSmoothDifferentialOperator d Q) :
    ∃ R : ContMDiffSection (𝓘(ℝ, Fin m → ℝ)) K ∞ H →ₗ[ℝ]
        ContMDiffSection (𝓘(ℝ, Fin m → ℝ)) F ∞ G,
      IsSmoothDifferentialOperator d R ∧ IsFormalAdjointFor (m := m) dV.measure Q R ∧
      (∀ (p : M) (U V : Set (Fin m → ℝ))
        (b : (Fin m → Fin (d + 1)) → (Fin m → ℝ) → F →L[ℝ] K)
        (c : (Fin m → Fin (d + 1)) → (Fin m → ℝ) → K →L[ℝ] F),
        IsLocalPresentation Q p U b → IsLocalPresentation R p V c →
        ∀ (ξ : Fin m → ℝ) (a : G p) (z : H p),
          inner ℝ a (presentationSymbol (G := H) (H := G) p c ξ z) =
            (-1 : ℝ) ^ d * inner ℝ (presentationSymbol (G := G) (H := H) p b ξ a) z) ∧
      ∀ S : ContMDiffSection (𝓘(ℝ, Fin m → ℝ)) K ∞ H →ₗ[ℝ]
          ContMDiffSection (𝓘(ℝ, Fin m → ℝ)) F ∞ G,
        IsSmoothDifferentialOperator d S →
          IsFormalAdjointFor (m := m) dV.measure Q S → S = R := by
  sorry

end SmoothDifferentialOperator
