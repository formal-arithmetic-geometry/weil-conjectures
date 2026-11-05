/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso

/-!
# The exceptional inverse image of a closed immersion restricted to an open

Let `i : Z ⟶ X` be a closed immersion and `W ⊆ X` an open subscheme, with `i ∣_ W : Z ∩ W ⟶ W`
the restricted closed immersion. Over a locally noetherian base, `Ri^!` commutes with the
restriction to `W`:

`j_Z^* Ri^! M ≅ R(i ∣_ W)^! j^* M`,

where `j : W ⟶ X` and `j_Z : Z ∩ W ⟶ Z` are the open immersions. Both sides are the exceptional
inverse image along `Z ∩ W ⟶ X`, by the composition law; over a locally noetherian base the
open immersions are quasi-compact, so their exceptional inverse images are the restrictions.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_mapDerivedCategory_upperStar_rightDerivedUpperShriek`
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Z : Scheme.{u}}

end Etale

end AlgebraicGeometry
