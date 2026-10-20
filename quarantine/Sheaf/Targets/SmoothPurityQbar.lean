/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.TateTwist.ProEtale
public import Sheaf.Paper.PbcQbarCategory
public import Sheaf.Paper.PbcCoefficientTwists
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.SmoothPurity.NormalizedWitness

/-!
# Smooth purity at the condensed algebraic-closure coefficient unit

Source: archived `WeilConjectures/SmoothPurity/Defs.lean`, lines 76–92;
current blueprint `sec-smooth-purity/sk-thm-sp-qbar` and `sk-thm-purity-transport`
(blueprint: nt-target-smooth-purity-qbar).

The exceptional functor is the chosen Nagata right adjoint on bounded constructible
internal modules. The conclusion is an isomorphism in the ambient derived category,
using the actual condensed Tate twist. The common-stage coefficient category is
used in the reconstruction argument; it is not the category of the conclusion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped CategoryTheory.Obj
open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- Smooth purity at the condensed coefficient unit.
Source: archived SmoothPurity/Defs.lean, lines 76–92; current blueprint
`sk-thm-sp-qbar` and `sk-thm-purity-transport`
(blueprint: nt-target-smooth-purity-qbar).

Proof plan:
1. Work over the original field and in the actual condensed module-object categories,
   with the chosen Nagata compactification and its composite adjunction
   (`sk-def-sfb-dc-setting`, `prop-weil-pbc-qbar-condensed-two-colimit`). The coefficient
   unit is bounded constructible of Tor amplitude [0,0]. Finite type over the field
   gives Noetherianity and finite dimension (`lem-weil-pbc-finite-type-over-noetherian`,
   `lem-kun-dimension-finite-type`).
2. The diagonal/DNC finite smooth-adjunction theorem over this same field gives
   gamma_n : A_{n,X}(d)[2d] ≅ Rf_n^! A_{n,Y}
   (`lem-pur-finite-smooth-adjunction-general-base`).
3. Its counit-defined coefficient comparisons give the quotient cocycle and
   compatibility of gamma_n with reduction, including the identity normalization
   at d = 0 (`lem-pur-finite-smooth-adjunction-general-base`).
4. Reconstruct the strict normalized Tate and unit towers in the completed integral
   categories with their canonical reductions (`lem-pur-condensed-tate-integral-tower`).
5. Apply case (b) of `lem-pur-condensed-exceptional-reconstruction`: the Tate tower
   has the single degree -2d, so functorial good truncation identifies the systems
   and gives c : U_X(M) ≅ G(U_Y(L)), for the target's chosen upper shriek G.
6. `lem-pur-condensed-tate-realization` at d = 0 gives e_Y : U_Y(L) ≅ B_Y.
   Hence c.symm after G(e_Y.symm) gives a : G(B_Y) ≅ U_X(M).
7. `lem-pur-condensed-tate-realization` gives the ambient comparison
   b : iota_X(U_X(M)) ≅ tateTwistDerived X ell d[2d].
8. Compose iota_X(a) with b. Its inverse is the reverse composite of their inverses;
   functoriality and the inverse equations verify that this is an isomorphism.

The smoothness instance is an explicit theorem binder, so it remains in the
elaborated statement. Only existence is asserted: no unconstructed isomorphism
is introduced as definition data. -/
theorem nonempty_smoothPurityIso
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ℓ)] {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f.left] :
    Nonempty
      (((boundedConstructibleUpperShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj
        (𝟙_ (Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧))).obj ≅
        (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X.left ℓ d)) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
