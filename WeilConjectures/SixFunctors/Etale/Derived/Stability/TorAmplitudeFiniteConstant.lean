/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeResidueIdeal
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ResidueTorTest

/-!
# Testing Tor amplitude on finitely generated constant sheaves

Let `Λ` be a commutative ring and `K ∈ D(X_ét, Λ)`. If `K ⊗ᴸ M_X` has homology in `[a, b]` for
every finitely generated `Λ`-module `M`, then `K` has Tor amplitude in `[a, b]`
(`AlgebraicGeometry.Etale.torAmplitudeIn_of_forall_finite_constantSheaf`).

Represent `K` by a K-flat complex `P` of flat sheaves. Exactness of `P ⊗ F` is checked on the
stalks at the geometric points `x̄`, where it is the exactness of `P_x̄ ⊗ F_x̄`. As `P_x̄` is a
complex of flat modules, this follows from the exactness of `P_x̄ ⊗ M` for the finitely generated
submodules `M` of `F_x̄` (`LinearMap.exact_rTensor_of_forall_finite`), and `P_x̄ ⊗ M` is the stalk
of `P ⊗ M_X`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

end Etale

end AlgebraicGeometry
