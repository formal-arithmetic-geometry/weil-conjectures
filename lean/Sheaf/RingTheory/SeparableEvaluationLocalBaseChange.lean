/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.KrullDimension.Zero
import Sheaf.FieldTheory.FiniteSeparableTensorFieldReduced

/-!
# Local base change at a specified separable evaluation point

Source: Stacks Project, Varieties, Tags 0C4Y and 0C50
(blueprint: lem-trf-separable-evaluation-local-base-change).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra.SeparableEvaluation

variable {k : Type u} {S : Type v} {K : Type w}
variable [Field k] [CommRing S] [Field K] [Algebra k S] [Algebra k K]
variable (p : Ideal S) [p.IsMaximal] (ι : (S ⧸ p) →ₐ[k] K)

/-- Evaluation on the residue-field tensor product, sending `a ⊗ a` to `ι a * a`.
Source: Stacks Tags 0C4Y and 0C50
(blueprint: lem-trf-separable-evaluation-local-base-change). -/
noncomputable def residueEvaluation : (S ⧸ p) ⊗[k] K →ₐ[k] K :=
  Algebra.TensorProduct.productMap ι (AlgHom.id k K)

/-- Evaluation on the base-changed algebra, sending `s ⊗ a` to `ι (s mod p) * a`.
Source: Stacks Tag 0C4Y
(blueprint: lem-trf-separable-evaluation-local-base-change). -/
noncomputable def evaluation : S ⊗[k] K →ₐ[k] K :=
  Algebra.TensorProduct.productMap (ι.comp (Ideal.Quotient.mkₐ k p)) (AlgHom.id k K)

/-- The specified evaluation prime of the base-changed algebra.
Source: Stacks Tag 0C4Y
(blueprint: lem-trf-separable-evaluation-local-base-change). -/
noncomputable abbrev evaluationIdeal : Ideal (S ⊗[k] K) :=
  RingHom.ker (evaluation p ι)

/-- The evaluation prime in the residue-field tensor product.
Source: Stacks Tags 0C4Y and 0C50
(blueprint: lem-trf-separable-evaluation-local-base-change). -/
noncomputable abbrev residueEvaluationIdeal : Ideal ((S ⧸ p) ⊗[k] K) :=
  RingHom.ker (residueEvaluation p ι)

/-- Evaluation is onto: `1 ⊗ a` maps to `a`.
Source: Stacks Tag 0C4Y, affine evaluation specialization
(blueprint: lem-trf-separable-evaluation-local-base-change).
Proof: apply the tensor product evaluation formula to `1 ⊗ a` (proof step 1). -/
theorem evaluation_surjective : Function.Surjective (evaluation p ι) := by
  sorry

/-- The specified evaluation ideal is maximal.
Source: Stacks Tag 0C4Y
(blueprint: lem-trf-separable-evaluation-local-base-change).
Proof: step 1 identifies the quotient by the kernel with the field `K`, using
`evaluation_surjective` and the first isomorphism theorem. -/
@[instance] theorem evaluationIdeal_isMaximal : (evaluationIdeal p ι).IsMaximal := by
  sorry

/-- The evaluation ideal contracts to the original closed point.
Source: Stacks Tag 0C4Y
(blueprint: lem-trf-separable-evaluation-local-base-change).
Proof: step 1 evaluates `s ⊗ 1` as `ι (s mod p)`. The field homomorphism `ι`
is injective, so this is zero exactly when `s ∈ p`. -/
theorem evaluationIdeal_comap :
    p = (evaluationIdeal p ι).comap
      (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[k] K) := by
  sorry

/-- The residue-tensor evaluation ideal is maximal.
Source: Stacks Tags 0C4Y and 0C50
(blueprint: lem-trf-separable-evaluation-local-base-change).
Proof: step 4 uses `1 ⊗ a` to prove surjectivity of residue evaluation; its
quotient by the kernel is therefore the field `K`. -/
@[instance] theorem residueEvaluationIdeal_isMaximal :
    (residueEvaluationIdeal p ι).IsMaximal := by
  sorry

/-- The local ring at the specified evaluation point of `S ⊗ K`.
Source: Stacks Tag 0C4Y
(blueprint: lem-trf-separable-evaluation-local-base-change). -/
noncomputable abbrev localRing := Localization.AtPrime (evaluationIdeal p ι)

/-- The local ring at the evaluation point of the residue-field tensor product.
Source: Stacks Tags 0C4Y and 0C50
(blueprint: lem-trf-separable-evaluation-local-base-change). -/
noncomputable abbrev residueLocalRing := Localization.AtPrime (residueEvaluationIdeal p ι)

/-- The canonical map `S_p → (S ⊗ K)_q`, defined by localization of `s ↦ s ⊗ 1`.
Source: Stacks Tag 0C4Y
(blueprint: lem-trf-separable-evaluation-local-base-change). -/
noncomputable def localMap : Localization.AtPrime p →+* localRing p ι :=
  Localization.localRingHom p (evaluationIdeal p ι)
    Algebra.TensorProduct.includeLeftRingHom (evaluationIdeal_comap p ι)

/-- The extended ideal `mB = (p S_p) B` under the canonical local map.
Source: Stacks Tag 0C4Y, clause (4)
(blueprint: lem-trf-separable-evaluation-local-base-change). -/
noncomputable abbrev closedFibreIdeal : Ideal (localRing p ι) :=
  (p.map (algebraMap S (Localization.AtPrime p))).map (localMap p ι)

/-- The maximal ideal `qB` of the evaluation local ring.
Source: Stacks Tag 0C4Y
(blueprint: lem-trf-separable-evaluation-local-base-change). -/
noncomputable abbrev evaluationLocalIdeal : Ideal (localRing p ι) :=
  (evaluationIdeal p ι).map (algebraMap (S ⊗[k] K) (localRing p ι))

/-- The tensor quotient map `S ⊗ K → (S/p) ⊗ K`.
Source: Stacks Tag 0C4Y, clause (4)
(blueprint: lem-trf-separable-evaluation-local-base-change). -/
noncomputable def tensorQuotient : S ⊗[k] K →ₐ[k] (S ⧸ p) ⊗[k] K :=
  Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k p) (AlgHom.id k K)

/-- The scalar structure of the localized residue tensor, induced by `a ↦ 1 ⊗ a`.
Source: Stacks Tags 0C4Y and 0C50
(blueprint: lem-trf-separable-evaluation-local-base-change). -/
noncomputable abbrev residueLocalAlgebra : Algebra K (residueLocalRing p ι) :=
  ((algebraMap ((S ⧸ p) ⊗[k] K) (residueLocalRing p ι)).comp
    (Algebra.TensorProduct.includeRight : K →ₐ[k] (S ⧸ p) ⊗[k] K).toRingHom).toAlgebra

/-- The scalar structure of either fibre quotient of `B`, induced by `a ↦ 1 ⊗ a`.
Source: Stacks Tags 0C4Y and 0C50
(blueprint: lem-trf-separable-evaluation-local-base-change). -/
noncomputable abbrev fibreAlgebra (J : Ideal (localRing p ι)) : Algebra K (localRing p ι ⧸ J) :=
  ((Ideal.Quotient.mk J).comp
    ((algebraMap (S ⊗[k] K) (localRing p ι)).comp
      (Algebra.TensorProduct.includeRight : K →ₐ[k] S ⊗[k] K).toRingHom)).toAlgebra

/-- Local field extension at a specified separable evaluation point, including the
canonical fibre and residue-field isomorphisms and their fraction formulas.
Source: Stacks Tags 0C4Y (clauses (1), (3), (4)) and 0C50
(blueprint: lem-trf-separable-evaluation-local-base-change).

Proof:
1. The preceding evaluation lemmas give surjectivity, maximality and contraction,
by the tensor pushout universal property.
2. Generators `s_i ⊗ 1` show finite type over `K`; the finite-type Noetherian
 theorem makes `S` and `S ⊗ K` Noetherian.
3. Field-extension base change is faithfully flat. Localizing at the evaluation
 prime gives the local map above and Noetherian local rings. A flat local map
 is faithfully flat (the recorded flat-local-ring-map and flat-local-hom nodes).
4. Tensor quotient base change gives a surjection `π : S ⊗ K → (S/p) ⊗ K`
 with kernel `pC`, and evaluation factors through it.
5. Localization of `π` is onto and has kernel `mB`: lift a denominator outside
 the residue evaluation prime and use the equality-of-fractions relation.
 The quotient isomorphism is the first isomorphism below.
6. A finite basis of `S/p` over `k` spans its tensor product over `K`.
 The finite-separable-tensor-field-reduced node gives reducedness.
7. Every prime quotient of this finite-dimensional algebra is a finite-dimensional
 domain over `K`, hence a field. The evaluation prime is therefore minimal.
8. The reduced-minimal-prime localization theorem makes its localization a field.
 Residue evaluation extends by `d/w ↦ e(d)/e(w)`. It is injective as a unital
 field map and onto since it hits all scalars. Compose the two isomorphisms to
 obtain the displayed formula; the resulting kernel is `qB = mB`. This is the
 maximal ideal of `B`, and the same formula identifies its residue field with `K`.
-/
theorem local_base_change [Algebra.FiniteType k S]
    [FiniteDimensional k (S ⧸ p)] [Algebra.IsSeparable k (S ⧸ p)] :
    (Algebra.TensorProduct.includeRight : K →ₐ[k] S ⊗[k] K).toRingHom.FiniteType ∧
    IsNoetherianRing (Localization.AtPrime p) ∧ IsLocalRing (Localization.AtPrime p) ∧
    IsNoetherianRing (localRing p ι) ∧ IsLocalRing (localRing p ι) ∧
    (localMap p ι).FaithfullyFlat ∧ IsLocalHom (localMap p ι) ∧
    @FiniteDimensional K ((S ⧸ p) ⊗[k] K) _ _
      Algebra.TensorProduct.rightAlgebra.toModule ∧
    IsReduced ((S ⧸ p) ⊗[k] K) ∧
    closedFibreIdeal p ι = evaluationLocalIdeal p ι ∧
    evaluationLocalIdeal p ι = IsLocalRing.maximalIdeal (localRing p ι) ∧
    ∃ θ : @AlgEquiv K (localRing p ι ⧸ closedFibreIdeal p ι) (residueLocalRing p ι)
        _ _ _ (fibreAlgebra p ι (closedFibreIdeal p ι)) (residueLocalAlgebra p ι),
    ∃ φ : @AlgEquiv K (residueLocalRing p ι) K _ _ _ (residueLocalAlgebra p ι) _,
    ∃ ψ : @AlgEquiv K (localRing p ι ⧸ evaluationLocalIdeal p ι) K _ _ _
        (fibreAlgebra p ι (evaluationLocalIdeal p ι)) _,
      (∀ (c : S ⊗[k] K) (v : (evaluationIdeal p ι).primeCompl),
        θ (Ideal.Quotient.mk _ (IsLocalization.mk' (localRing p ι) c v)) *
            algebraMap ((S ⧸ p) ⊗[k] K) (residueLocalRing p ι) (tensorQuotient p v) =
          algebraMap ((S ⧸ p) ⊗[k] K) (residueLocalRing p ι) (tensorQuotient p c)) ∧
      (∀ (d : (S ⧸ p) ⊗[k] K) (w : (residueEvaluationIdeal p ι).primeCompl),
        φ (IsLocalization.mk' (residueLocalRing p ι) d w) =
          residueEvaluation p ι d / residueEvaluation p ι w) ∧
      (∀ (s : S) (a : K) (v : (evaluationIdeal p ι).primeCompl),
        φ (θ (Ideal.Quotient.mk _
          (IsLocalization.mk' (localRing p ι) (s ⊗ₜ[k] a) v))) =
            ι (Ideal.Quotient.mk p s) * a / evaluation p ι v) ∧
      (∀ (c : S ⊗[k] K) (v : (evaluationIdeal p ι).primeCompl),
        ψ (Ideal.Quotient.mk _ (IsLocalization.mk' (localRing p ι) c v)) =
          evaluation p ι c / evaluation p ι v) := by
  sorry

end Algebra.SeparableEvaluation
