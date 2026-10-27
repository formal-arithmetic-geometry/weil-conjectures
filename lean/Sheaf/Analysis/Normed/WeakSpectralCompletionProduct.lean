/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.RingTheory.Artinian.Module

/-!
# Completion of a weakly cartesian spectral extension

Source: BGR, Non-Archimedean Analysis, Proposition 3.6.2/3, completion criterion;
the agent-written Cauchy-sequence proof recorded in the DAG
(blueprint: lem-trf-weak-spectral-completion-product).

## Main definitions

* `SpectralNormedExtension`: the original extension with its spectral algebra norm.
* `SpectralNormedExtension.toCompletion`: the canonical algebra embedding into its completion.

## Main statements

* `exists_weak_spectral_completion_product`: the completion is a finite product of finite
  extensions of the completed base, with the maximum of their spectral norms.
-/

@[expose] public section

noncomputable section

universe u v

/-- The carrier of an extension, distinguished so that its incomplete-base spectral algebra
norm can be installed without assuming that this norm is multiplicative.
Source: `spectralAlgNorm`, Mathlib, Analysis/Normed/Unbundled/SpectralNorm.lean:663.
(blueprint: lem-trf-weak-spectral-completion-product) -/
def SpectralNormedExtension (_F : Type u) (E : Type v) : Type v := E

namespace SpectralNormedExtension

/-- The original field operations on the spectral-norm carrier.
Source: the Cauchy-sequence construction in the node, step 1.
(blueprint: lem-trf-weak-spectral-completion-product) -/
instance instField (F : Type u) (E : Type v) [Field E] :
    Field (SpectralNormedExtension F E) := inferInstanceAs (Field E)

/-- The original scalar action on the spectral-norm carrier.
Source: the Cauchy-sequence construction in the node, step 2.
(blueprint: lem-trf-weak-spectral-completion-product) -/
instance instAlgebra (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E] :
    Algebra F (SpectralNormedExtension F E) := inferInstanceAs (Algebra F E)

/-- The normed commutative ring structure induced by the spectral algebra norm, without a
completeness assumption on the base. Source: Mathlib `spectralAlgNorm` and
`RingNorm.toNormedRing`.
(blueprint: lem-trf-weak-spectral-completion-product) -/
instance instNormedCommRing (F : Type u) (E : Type v) [NormedField F] [Field E]
    [Algebra F E] [Algebra.IsAlgebraic F E] [IsUltrametricDist F] :
    NormedCommRing (SpectralNormedExtension F E) :=
  { (spectralAlgNorm F E).toRingNorm.toNormedRing, (inferInstance : CommRing E) with }

/-- Spectral scalar homogeneity gives the original extension its normed algebra structure.
Source: the `smul'` field of Mathlib `spectralAlgNorm`.
(blueprint: lem-trf-weak-spectral-completion-product) -/
instance instNormedAlgebra (F : Type u) (E : Type v) [NormedField F] [Field E]
    [Algebra F E] [Algebra.IsAlgebraic F E] [IsUltrametricDist F] :
    NormedAlgebra F (SpectralNormedExtension F E) where
  toAlgebra := instAlgebra F E
  norm_smul_le a x := le_of_eq ((spectralAlgNorm F E).smul' a x)

/-- Constant Cauchy classes as an algebra homomorphism. The completion operations are the
canonical operations of Mathlib's uniform ring completion.
Source: Mathlib `UniformSpace.Completion.coeRingHom` and `Completion.algebraMap_def`.
(blueprint: lem-trf-weak-spectral-completion-product) -/
def toCompletion (F : Type u) (E : Type v) [NormedField F] [Field E] [Algebra F E]
    [Algebra.IsAlgebraic F E] [IsUltrametricDist F] :
    SpectralNormedExtension F E →ₐ[F] UniformSpace.Completion (SpectralNormedExtension F E) where
  toRingHom := UniformSpace.Completion.coeRingHom
  commutes' a := (UniformSpace.Completion.algebraMap_def _ _ a).symm

end SpectralNormedExtension

/-- Completion of a finite weakly cartesian spectral extension is an isometric finite product.
Source: BGR, Non-Archimedean Analysis, Proposition 3.6.2/3, completion criterion;
the archival BGR document is absent, and the proof below is the agent argument in the DAG.
(blueprint: lem-trf-weak-spectral-completion-product)

Proof plan:
1. By `lem-trf-incomplete-spectral-algebra-norm`, spectral norms of equivalent Cauchy sequences
have the same limit. Boundedness and submultiplicativity make termwise products well-defined;
the ring identities hold termwise. Constant classes are isometric and dense.
2. By `lem-sfb-normed-field-completion`, the base completion is a complete normed field.
Termwise scalar products define its action. The lower coordinate bound makes every coordinate
of a spectral Cauchy sequence Cauchy; the upper bound gives the converse and identifies equivalent
sequences. Completion is thus linearly isomorphic to the n-fold product of the completed base,
so it has dimension n. The scalar map is the continuous extension of the original base map.
3. By `lem-trf-algebraic-spectral-norm-powers`, power multiplicativity passes to limits, so the
completion is reduced. It is Artinian by `lem-weil-pbc-finite-dim-algebra-artinian`.
Apply `lem-sfb-reduced-artinian-residue-product` to obtain the residue-field product, with
finite factors. Norm one of the identity excludes an empty product; dimensions add to n.
4. Each primitive product idempotent has norm one by power multiplicativity and definiteness.
The norm restricted to a single slot is an ultrametric, power-multiplicative algebra norm.
By `lem-trf-power-multiplicative-algebra-norm-unique`, it equals that factor's spectral norm.
5. The ultrametric inequality bounds the norm of the sum of the slots by their maximum.
Conversely multiplication by a norm-one idempotent bounds each slot norm by the total norm.
These two inequalities give the maximum formula. No separability or stability is used.
-/
theorem exists_weak_spectral_completion_product
    (F : Type u) (E : Type v) [NontriviallyNormedField F] [IsUltrametricDist F]
    [Field E] [Algebra F E] [FiniteDimensional F E]
    (n : ℕ) (hn : 0 < n) (w : Module.Basis (Fin n) F E)
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hw : ∀ a : Fin n → F,
      c * ‖a‖ ≤ spectralNorm F E (∑ i, a i • w i) ∧
      spectralNorm F E (∑ i, a i • w i) ≤ C * ‖a‖) :
    Isometry (SpectralNormedExtension.toCompletion F E) ∧
    DenseRange (SpectralNormedExtension.toCompletion F E) ∧
    ∃ (_ : Algebra (UniformSpace.Completion F)
        (UniformSpace.Completion (SpectralNormedExtension F E))),
      (∀ h : UniformSpace.Completion F,
        algebraMap (UniformSpace.Completion F)
            (UniformSpace.Completion (SpectralNormedExtension F E)) h =
          UniformSpace.Completion.extension
            (fun a : F ↦ ((algebraMap F (SpectralNormedExtension F E) a) :
              UniformSpace.Completion (SpectralNormedExtension F E))) h) ∧
      FiniteDimensional (UniformSpace.Completion F)
        (UniformSpace.Completion (SpectralNormedExtension F E)) ∧
      Module.finrank (UniformSpace.Completion F)
        (UniformSpace.Completion (SpectralNormedExtension F E)) = n ∧
      ∃ (r : ℕ) (_ : 0 < r) (L : Fin r → Type v) (_ : ∀ j, Field (L j))
          (_ : ∀ j, Algebra (UniformSpace.Completion F) (L j))
          (_ : ∀ j, FiniteDimensional (UniformSpace.Completion F) (L j))
          (θ : UniformSpace.Completion (SpectralNormedExtension F E) ≃ₐ[
            UniformSpace.Completion F] (∀ j, L j)),
        (∀ z : UniformSpace.Completion (SpectralNormedExtension F E),
          ‖z‖ = ⨆ j : Fin r, spectralNorm (UniformSpace.Completion F) (L j) (θ z j)) ∧
        (∑ j : Fin r, Module.finrank (UniformSpace.Completion F) (L j)) = n := by
  sorry
