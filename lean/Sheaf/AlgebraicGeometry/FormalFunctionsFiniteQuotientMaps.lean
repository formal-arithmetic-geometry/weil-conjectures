/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.AlgebraicGeometry.FormalFunctionsFinitePullback
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties
import Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoicesExist
import Sheaf.AlgebraicGeometry.SpecLocalRingCanonicalMorphism

/-! # Finite pullback of the local germ formula

Source: Stacks Project, Tags 02OD, 01F7, 01FB and 01E4.
(blueprint: lem-weil-pbc-formal-functions-finite-quotient-maps)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
namespace AlgebraicGeometry
noncomputable section

/-- Composing the local germ formula with canonical finite-level pullback gives theta.
Source: Stacks Project, Tag 02OD, factorization c_n through c; Tags 01F7, 01FB, 01E4.
(blueprint: lem-weil-pbc-formal-functions-finite-quotient-maps)

Proof: Choose an injective resolution of F' and open comparison data for the local
base-change square. The local spectrum map is flat (02KH), as is its base change,
so such data exist by the open-choice existence theorem. Apply the
local germ formula on V to the representative xi. Restrict the h-map
formalFunctionsFiniteFMap to the inverse image of f inverse V. Its adjunction equation
says that composing it with the unit for the local base change is the unit for i_n.
The restriction-unit square and cohomology composition therefore identify the resulting
map with the finite-level pullback on xi. The section-class representative in the germ
is independent of the open resolution comparisons: their augmentations identify
them with the restriction of I, and the pinned section maps give the canonical
cohomology comparison for that restriction. Equivalently, augmentation-preserving
lifts are homotopic and induce the same cohomology map. Thus it equals the representative
used by any prescribed finite-level open choices D. Substitution of the assumed formula
for r gives exactly IsFormalFunctionsTheta, for every I, J, V, D and xi. No
surjectivity of r or equivalence property of a is needed. For zero coefficients or
empty fibre all maps are zero; in degree zero this is composition of section pullbacks.
There is no quotient-system isomorphism or completed module in this argument. -/
theorem formalFunctions_finite_quotient_maps {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [IsLocallyNoetherian Y] (F : X.Modules)
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) (y : Y) (p n : ℕ)
    (r : formalFunctionsLocalCohomology f y F p →ₗ[Y.presheaf.stalk y]
      formalFibreCohomologyLocal f y F p n)
    (hr : ∀ z, r z = formalFunctionsFinitePullback f y F p n z)
    (a : formalFunctionsStalk f y F p →ₗ[Y.presheaf.stalk y]
      formalFunctionsLocalCohomology f y F p)
    (ha : IsFormalFunctionsLocalComparison f y F p a) :
    IsFormalFunctionsTheta f y F p n (r.comp a) := by sorry

end
end AlgebraicGeometry
