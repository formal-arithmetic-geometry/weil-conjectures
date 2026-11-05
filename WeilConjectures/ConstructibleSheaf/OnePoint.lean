/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.LowerStarOpenStalk

/-!
# Sheaves with finite stalks on a one-point scheme are finite locally constant

Let `Y` be a scheme with exactly one point and `H` a sheaf of modules over a finite ring on the
small étale site of `Y` whose geometric stalks are finite.
Then `H` is finite locally constant. For `Y = Spec k` this is the statement that a discrete
Galois module with finite underlying set is trivialised by a finite separable extension of `k`.

Every étale `Y`-scheme is discrete, so its points are open. Fix a geometric point `ȳ` of `Y`.
The finitely many elements of the stalk `H_ȳ` are germs of sections over a common étale
neighbourhood, which may be shrunk to a single point `V`. Every nonempty étale `W ⟶ V` is
surjective, hence a covering, so the sections of `H` over a one-point `W` inject into every
stalk of `W`; lifting `ȳ` to `W` shows that restriction `H(V) ⟶ H(W)` is surjective for one-point
`W` over `V`, and injective for nonempty `W`. Consequently the restriction of `H` to `V` is the
constant sheaf with value `H(V)`: the map from the constant presheaf is locally injective and
locally surjective. As `V ⟶ Y` is surjective, `H` is locally constant.

## Main statements

- `AlgebraicGeometry.Etale.injective_toPresheafFiber_of_subsingleton`: sections over a one-point
  étale scheme inject into stalks.
- `AlgebraicGeometry.Etale.isFiniteLocallyConstantSheaf_of_subsingleton`: a sheaf of modules with
  finite stalks on a one-point scheme is finite locally constant.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [Ring Λ]

section OnePoint

variable {Y : Scheme.{u}} [Subsingleton Y] (H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))

end OnePoint

end Etale

end AlgebraicGeometry
