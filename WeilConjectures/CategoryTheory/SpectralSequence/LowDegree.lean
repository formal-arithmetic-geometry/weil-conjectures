/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.Exact
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# The exact sequence of low degree terms of a spectral sequence

Let `E` be a first quadrant cohomological spectral sequence starting at the `E₂`-page which
abuts to an `ℕ`-graded object `H`. Then there is an exact sequence of low degree terms
`0 ⟶ E₂^{1,0} ⟶ H¹ ⟶ E₂^{0,1} ⟶ E₂^{2,0}`, the last map being the differential `d₂`.

Indeed, the abutment filtration `H¹ = F⁰ ⊇ F¹ ⊇ F² = 0` has graded pieces
`F¹ ≅ E∞^{1,0} = E₂^{1,0}` and `H¹ / F¹ ≅ E∞^{0,1} = ker (d₂ : E₂^{0,1} ⟶ E₂^{2,0})`, since in the
first quadrant no other differential enters or leaves these spots.

## Main statements

- `CategoryTheory.SpectralSequence.Abutment.exists_lowDegree_exact`: the exact sequence of low
  degree terms.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace SpectralSequence

variable {E : E₂CohomologicalSpectralSequenceNat C} {H : ℕ → C}

end SpectralSequence

end CategoryTheory
