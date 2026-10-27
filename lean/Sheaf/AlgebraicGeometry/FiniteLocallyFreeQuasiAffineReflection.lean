/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
import Sheaf.AlgebraicGeometry.FiniteLocallyFreeFunctionNorm
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction

/-!
# Quasi-affineness reflected by finite locally free morphisms

Source: Stacks Project, Divisors, Tags 0BD1 and 0BD2; the assertion is the
relative form over an arbitrary scheme
(blueprint: lem-sfb-finite-locally-free-quasi-affine-reflection).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- A finite locally free morphism of positive constant degree reflects
quasi-affineness of a morphism to the same base. Source: Stacks Project,
Divisors, Tags 0BD1 and 0BD2 (blueprint: lem-sfb-finite-locally-free-quasi-affine-reflection).

Proof:
1. Fix an affine open `U` of `S` and restrict the two structure maps and `π` over `U`.
   The source restriction is quasi-affine by def-nagata-quasi-affine-morphism.
   The restricted finite, flat, locally finitely presented charts and their fibres
   still have degree `d` (def-pc-finite-locally-free).
2. Apply lem-sfb-finite-locally-free-function-norm to the restricted map `f`.
   Its image is closed by lem-weil-pbc-finite-closed-map-finite-fibres. If a point
   lies outside this image, its open complement `V` has empty inverse image.
   Therefore the pullbacks of `0` and `1` to this inverse image coincide.
   Applying the multiplicative norm and its scalar-power identity gives `0 = 1`
   on `V`, since `d ≥ 1`. This contradicts the nonzero local ring at that point.
   Thus `f` is surjective.
3. By lem-sfb-quasiaffine-affine-basic-open-criterion the source is quasi-compact
   and has affine basic opens around every point. The multiplication isomorphisms
   identify every tensor power of its structure sheaf with itself. Taking power
   one makes the structure sheaf ample (def-weil-pbc-ample-invertible-module).
   The target structure sheaf is invertible by def-sc-invertible-module. Its tensor
   pullback is the source structure sheaf (def-pc-module-pullback): locally the
   isomorphism sends `b ⊗ a` to `b f♯(a)`, with inverse `b ↦ b ⊗ 1`.
   Apply lem-sfb-finite-locally-free-ample-reflection to this line and `f`.
4. The ample target structure sheaf makes the target quasi-compact and supplies
   affine nonvanishing loci of positive tensor powers at every point. Multiplication
   identifies those powers with the structure sheaf and preserves nonvanishing.
   The basic-open criterion makes the target quasi-affine. This works over every
   affine `U`, proving relative quasi-affineness. No division by `d`, reducedness,
   or Noetherianity is used.
-/
theorem isQuasiAffineHom_of_finiteLocallyFree
    {S : Scheme.{u}} (X Y : Over S) (π : X ⟶ Y) (d : ℕ) (hd : 1 ≤ d)
    [π.left.IsFiniteLocallyFreeOfDegree d] [IsQuasiAffineHom X.hom] :
    IsQuasiAffineHom Y.hom := by
  sorry

end AlgebraicGeometry
