/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativeProperCoefficientOperations
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackIntegralModuleBalance
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackIntegralDerivedBalance
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackCompletion

/-! # Normalized integral comparisons over geometric spaces

Source: Bhatt--Scholze, Lemma 6.5.9, Proposition 6.6.11 and Remark 6.8.15.
(blueprint: lem-sf-native-pullback-integral-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization.Proper
open AlgebraicallyClosedCoefficients (Index Coefficient)

/-- Ordinary balance, its derived representative square and the specified completion
unit provide every finite-integral comparison. Source: Bhatt--Scholze, Lemma 6.5.9,
Proposition 6.6.11 and Remark 6.8.15.
(blueprint: lem-sf-native-pullback-integral-comparison).

Proof: geometric spaces are quasi-compact and finite type over a field, so both are
noetherian. For each finite coefficient field, construct the tensor-unit-normalized
ordinary balance by the scalar-restriction/direct-image square. Exact localization gives
its derived balance with the equation on all cochain representatives. The completion
helper makes the actual ordinary-to-completed unit a natural isomorphism on integral
constructible inputs, so use its components for completion. Each field of the comparison
record is supplied with its specified normalization; no arbitrary maps are substituted. -/
theorem nativePullbackIntegralComparison (l : ℕ) [Fact l.Prime]
    (D : FiniteFieldDatum.{u}) (Z T : GeometricSpace D) (p : Z.base ⟶ T.base)
    [∀ x : Z.base.left, Invertible (l : Z.base.left.residueField x)]
    [∀ x : T.base.left, Invertible (l : T.base.left.residueField x)]
    (R : LocallyFiniteAdicRealization.Realization l Z.base.left)
    (S : LocallyFiniteAdicRealization.Realization l T.base.left)
    (O : Operations l p.left R S) (E : Index l (PadicAlgCl l)) :
    Nonempty (IntegralComparison l p.left R S O E) := by
  let := Z.finiteType
  let := Z.quasiCompact
  let := T.finiteType
  let := T.quasiCompact
  let : CompactSpace Z.base.left := QuasiCompact.compactSpace_of_compactSpace Z.base.hom
  let : CompactSpace T.base.left := QuasiCompact.compactSpace_of_compactSpace T.base.hom
  let : IsLocallyNoetherian Z.base.left :=
    LocallyOfFiniteType.isLocallyNoetherian Z.base.hom
  let : IsLocallyNoetherian T.base.left :=
    LocallyOfFiniteType.isLocallyNoetherian T.base.hom
  let : IsNoetherian Z.base.left := ⟨⟩
  let : IsNoetherian T.base.left := ⟨⟩
  obtain ⟨b, hb⟩ := nativePullbackIntegralModuleBalance l p.left R S O E
  obtain ⟨d, hd⟩ := nativePullbackIntegralDerivedBalance l p.left R S O E b
  obtain ⟨e, he, _⟩ := nativePullbackCompletion l D Z T p
    (Coefficient.{u} l (PadicAlgCl l) E)
  exact ⟨{
    balance := b
    sections := hb
    derived := d
    representative := hd
    completion := fun K ↦ e.app K
    completion_hom := he }⟩

end WeilConjectures.AdicQbarRealization.Proper
