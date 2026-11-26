/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralReconstructionInterfaces
import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralReconstructionEquivalence
import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralSystemExistence
import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralNormalizedAdjunction
import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralRealizationAssembly

/-!
# Integral exceptional reconstruction assembly

Every scheme of finite type over the base field has an integral reconstruction, and a
compactified morphism carries normalized exceptional systems together with a realization of
their adjunction by the actual integral comparisons.

## Implementation details

The proof assembles the separate steps: the reconstruction equivalence on uniform finite-Tor
subcategories (`exceptionalIntegralReconstructionEquivalence`), existence of the exceptional
systems (`exceptionalIntegralSystemExistence`), the normalized system adjunction
(`exceptionalIntegralNormalizedAdjunction`) and its realization by the integral proper/open
comparisons (`exceptionalIntegralRealizationAssembly`). The integral adjunction is the composite
of the two reconstruction adjunctions with the restricted system adjunction. Absolute
separatedness of `X` and `Y` is not assumed.

## References

* [Zheng, Propositions 2.23, 2.29, 3.16, Lemma 5.22 and Proposition 5.24]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures.ExceptionalIntegralReconstruction
open IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Integral reconstruction and the normalized compact-support adjunction: every scheme of
finite type over `D.k` has a `Reconstruction`, and for the compactification `c` of `f` there
are reconstructions of `X` and `Y`, exceptional systems `s` and a system adjunction `a` that is
realized by the actual integral comparisons. -/
theorem exceptionalIntegralReconstruction (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) :
    (∀ (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
      [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))],
      Nonempty (Reconstruction l E T)) ∧
    ∃ (rX : Reconstruction l E X) (rY : Reconstruction l E Y)
      (s : Systems l E c) (a : SystemAdjunction l E c s),
      Nonempty (Realization l E c D hl rX rY s a) := by
  have hrec : ∀ (T : Scheme.{u}) [T.Over (Spec (.of D.k))]
      [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))],
      Nonempty (Reconstruction l E T) := fun T ↦
    exceptionalIntegralReconstructionEquivalence l E D hl T
  obtain ⟨rX⟩ := hrec X
  obtain ⟨rY⟩ := hrec Y
  obtain ⟨s⟩ := exceptionalIntegralSystemExistence l E D hl f c
  obtain ⟨a⟩ := exceptionalIntegralNormalizedAdjunction l E D hl f c rX s
  obtain ⟨t, ht⟩ := exceptionalIntegralRealizationAssembly l E D hl f c rX rY s a
  exact ⟨hrec, rX, rY, { s with transport := t }, a.withTransport l E c s t, ht⟩

end WeilConjectures.ExceptionalIntegralReconstruction
