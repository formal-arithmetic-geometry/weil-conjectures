/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralReconstructionInterfaces

/-!
# Realization of the reconstructed exceptional adjunction

A normalized system adjunction is realized by the actual integral proper/open comparisons, after
choosing compatible transport shifts on the same functors.

## Implementation details

The transport record is rebuilt on the same ordinary adjoint, site maps and proper/open
comparison, using their localized cochain shifts; an arbitrary transport record does not assert
that its shift fields have this normalization. The integral adjunction is obtained by composing
the two reconstruction equivalences with the normalized system adjunction. The left realization
follows the total limit of the system left functor by the proper direct-image/limit comparison
and the inverse open-adjunction mate of reduction pullback. The shift comparisons are pasted on
the same proper/open word.

## References

* [Zheng, Section 5, Construction 5.25 and Proposition 5.24]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralReconstruction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- A normalized system adjunction `a` is realized by the actual integral proper/open
comparisons, for a suitable choice `t` of transport shifts on the same functors. -/
theorem exceptionalIntegralRealizationAssembly
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (rX : Reconstruction l E X) (rY : Reconstruction l E Y)
    (s : Systems l E c) (a : SystemAdjunction l E c s) :
    ∃ t : ExceptionalSystemTransport s.right s.siteX s.siteY s.siteZ
      s.properOpen s.comparison,
      Nonempty (Realization l E c D hl rX rY { s with transport := t }
        (a.withTransport l E c s t)) := by sorry

end WeilConjectures.ExceptionalIntegralReconstruction
