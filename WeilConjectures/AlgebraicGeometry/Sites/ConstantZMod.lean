/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.Gm

/-!
# The constant étale sheaf `ℤ/n` and its degree-zero cohomology

The constant sheaf `ℤ/n` on the small étale site of a scheme `X` and the canonical map from
`ℤ/n` to its degree-zero cohomology. The latter is the unit of the constant-sheaf adjunction,
evaluated at the terminal object of the small étale site and transported along
`CategoryTheory.Sheaf.H.equiv₀`; it is bijective as soon as `X` is connected, which is the
degree-zero half of the curve estimate and has nothing to do with curves.

## Main definitions

- `AlgebraicGeometry.Scheme.constantZMod`: the constant étale sheaf `ℤ/n`.
- `AlgebraicGeometry.Scheme.toSheafHConstantZMod`: the canonical map
  `ℤ/n →+ H⁰(X_ét, ℤ/n)`.

## Main statements

- `AlgebraicGeometry.Scheme.bijective_toSheafHConstantZMod`: the canonical map is bijective
  for a connected scheme. The proof is `sorry`.

## Blueprint references

The labels quoted below are labels of the *sketch* blueprint, which lives in the separate
repository `formal-arithmetic-geometry/weil-conjectures-blueprint`, not of `blueprint/src` in
this repository.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (n : ℕ)

/-- The constant étale sheaf `ℤ/n` on a scheme `X`.
(blueprint: `def-sc-constant-sheaves`) -/
noncomputable abbrev constantZMod : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))

/-- The canonical map `ℤ/n →+ H⁰(X_ét, ℤ/n)`: the unit of the adjunction
`CategoryTheory.constantSheafAdj` evaluated at the terminal object of the small étale site,
read through the identification `CategoryTheory.Sheaf.H.equiv₀` of `H⁰` with the sections over
that terminal object. -/
noncomputable def toSheafHConstantZMod : ZMod n →+ Sheaf.H (X.constantZMod n) 0 :=
  (((Sheaf.H.equiv₀ (X.constantZMod n)
        (terminalIsTerminal (C := X.Etale))).symm.toAddMonoidHom.comp
      ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal).unit.app
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))).hom).comp
    (AddEquiv.ulift.symm : ZMod n ≃+ ULift.{u + 1} (ZMod n)).toAddMonoidHom)

/-- For a connected scheme the canonical map `ℤ/n →+ H⁰(X_ét, ℤ/n)` is bijective: a global
section of the constant sheaf is a locally constant function on `X`, hence constant. The proof
is `sorry`. -/
theorem bijective_toSheafHConstantZMod [ConnectedSpace X] :
    Function.Bijective (X.toSheafHConstantZMod n) :=
  sorry

end AlgebraicGeometry.Scheme
