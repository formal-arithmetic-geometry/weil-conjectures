/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.Weights

/-!
# Real Weil sheaves on an arbitrary base are mixed

A constructible Weil sheaf is `ι`-*real* (`AlgebraicGeometry.WeilSheaf.IsReal`) if the realization
under `ι` of every local Frobenius characteristic polynomial has real coefficients. Over a curve
this forces purity on a dense open, which is the content of the blueprint section
`sec-purity-real-sheaves`; this file states the extension of that statement to an arbitrary
separated finite-type `k₀`-scheme, which is the input the Deligne–Laumon reduction needs in order
to turn the reality of a local `L`-factor into a weight bound.

## Implementation notes

A Noetherian induction reduces to a lisse real sheaf on a smooth affine irreducible stratum, where
an irreducibility-preserving Bertini theorem produces a family of smooth geometrically irreducible
curve sections on which each constituent becomes pure of a weight independent of the curve;
mixedness then descends along finite constant extensions and is spliced back along the open–closed
sequence.

## Main statements

- `AlgebraicGeometry.WeilSheaf.IsReal.isMixed`: blueprint `sk-i-dl-general-real`.

## References

- [Deligne, *La conjecture de Weil : II*][deligne1980], Publ. Math. IHÉS **52** (1980), §1.8, for
  real sheaves and their mixedness.
- [Kiehl, Weissauer, *Weil conjectures, perverse sheaves and l-adic Fourier
  transform*][kiehlWeissauer2001], Springer (2001), Appendix B, for the
  irreducibility-preserving Bertini theorem the proof uses.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every constructible `ι`-real Weil sheaf on a separated finite-type `k₀`-scheme is `ι`-mixed
(blueprint: `sk-i-dl-general-real`). -/
theorem WeilSheaf.IsReal.isMixed {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {ι : PadicAlgCl l →+* ℂ} {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l X} (hF : F.IsReal ι) :
    F.IsMixed ι :=
  sorry

end AlgebraicGeometry
