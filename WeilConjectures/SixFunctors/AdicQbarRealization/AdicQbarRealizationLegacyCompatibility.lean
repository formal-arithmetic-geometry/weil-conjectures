/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData

import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationIsomorphismNormalization
import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorRealizationDescent
import WeilConjectures.SixFunctors.AdicQbarRealization.Native.NativeAdicRealizationData
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
import WeilConjectures.SixFunctors.AdicQbarRealization.AmbientHomEvaluation.CoherenceCalculus.CommonStageEvaluationFiniteSquare
import WeilConjectures.SixFunctors.Normalized.NormalizedCommonEvaluationForStructure
import WeilConjectures.SixFunctors.AdicQbarRealization.Native.NativeAdicAmbientHomConstructible
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.LocallyFiniteAdicCompactSupportRealization

/-! # Archived common-stage realization compatibility

This is the complete former Family-valued proof, isolated from the actual condensed
section realization. Only callers whose statements still use the withdrawn model
import this archive during their own route-switch repairs.
Source: BS Definition 6.8.8, Proposition 6.8.14 and Remark 6.8.15;
HRS Proposition 5.2, Theorem 7.7 and Lemma 7.9.
(blueprint: lem-sf-adic-qbar-constructible-realization).
-/

@[expose] public noncomputable section
universe u

section LegacyCompatibility

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
attribute [local irreducible] HasDerivedCategory.standard
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization


/-- The canonical exact symmetric monoidal common-stage realization in ordinary
modules over the native finite-extension-valued coefficient sheaf, with the
ambient evaluation-transpose Hom comparison and arbitrary-isomorphism coherence.
Source: BS Definition 6.8.8, Proposition 6.8.14 and Remark 6.8.15; HRS Proposition
5.2, Theorem 7.7 and Lemma 7.9
(blueprint: lem-sf-adic-qbar-constructible-realization).

Proof (lem-sf-constructible-exceptional-coefficient-construction,
lem-sf-locally-finite-adic-compact-support-realization): for each geometric space T,
apply the normalized coefficient construction to the identity of T and the native
compact-support realization to its proper identity compactification. Its source
Realization and the section-module equivalence of its NativeGeometry give the native
realization of T and its ordinary section-module presentation; the identity is
separated, of finite type and proper, and T is of finite type over the fixed field.

Apply lem-sf-adic-completed-tensor-realization-descent to this Realization: it gives
the symmetric tensor, unit and coherence data and the finite quotient normalizations,
with the fixed residue-field invertibility instance (by subsingleton equality).

Take the fixed normalized common-stage closed structure podCommonClosed. Its inverse
transpose is evaluation after tensoring with the transpose, by parameter naturality
applied to the identity of the Hom object (lem-pod-derived-automorphism-hom-evaluation).
Apply lem-sf-adic-ambient-hom-evaluation-comparison to the tensor data, the
presentation and this closed structure: it makes the evaluation-transpose Hom
comparison invertible, natural and evaluation-preserving, and its transpose equation
applied to a transpose gives the realized transpose law. This gives At, its finite
normalizations and HomLaws on every T.

Choose these data for all T at once and apply
lem-sf-adic-realization-isomorphism-normalization to them. Its Family carries the
integral, identity, composition, tensor, coefficient-unit and Hom equations for
arbitrary scheme isomorphisms, including semilinear geometric Frobenius, without a
k-linearity hypothesis or a site-perfectness restriction on the permitted Hom pair. -/
theorem adic_qbar_constructible_realization_legacy (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p) : Nonempty (Family l D) := by
  classical
  have hR := fun T : GeometricSpace D ↦ native_realization_and_presentation D l hl T
  choose R P using hR
  have hA := fun T : GeometricSpace D ↦ normalized_tensor_and_hom D l hl T (R T) (P T)
  choose A N H using hA
  let finite := fun T E ↦ Classical.choice (N T E)
  obtain ⟨F, _⟩ := adic_realization_isomorphism_normalization l D hl R A finite P H
  exact ⟨F⟩


end WeilConjectures.AdicQbarRealization

end LegacyCompatibility
