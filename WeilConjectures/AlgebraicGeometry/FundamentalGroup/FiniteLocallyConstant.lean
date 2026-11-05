/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
public import WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale

/-!
# Finite locally constant sheaves of sets on the small étale site

Let `Y` be a scheme. A sheaf of sets `F` on the small étale site of `Y` is *locally constant*
if there is an étale cover of `Y` over each member of which `F` is constant, and *finite
locally constant* if moreover its stalks at all geometric points are finite. These sheaves
form the category `FLC(Y)` which, together with the category `FÉt(Y)` of finite étale
`Y`-schemes (`AlgebraicGeometry.Scheme.FiniteEtale`), is the setting of the Galois theory
of finite étale covers.

## Main definitions

- `AlgebraicGeometry.Scheme.FiniteLocallyConstant`: the category `FLC(Y)`.
- `AlgebraicGeometry.Scheme.FiniteLocallyConstant.fiber`: the stalk functor
  `FLC(Y) ⥤ FintypeCat` at a geometric point.

## Implementation notes

Finite locally constant sheaves of sets are defined by
`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheafOfTypes`; as there, the values live in
`Type (u + 1)`, one universe above the base schemes.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}}

variable (Y) in
/-- Blueprint `def-galois-categories`: Finite etale covers and finite locally constant sheaves.

The category `FLC(Y)` of finite locally constant sheaves of sets on the small étale site of
`Y`, with morphisms of sheaves; the category `FÉt(Y)` of finite étale `Y`-schemes is
`AlgebraicGeometry.Scheme.FiniteEtale`. The small étale site `Y_ét` (blueprint
`def-weil-pbc-etale-site`) is Mathlib's `AlgebraicGeometry.Scheme.smallEtaleTopology`, and finite
torsors (blueprint `def-weil-pbc-finite-torsors`) are `CategoryTheory.Sheaf.Torsor`. -/
protected abbrev FiniteLocallyConstant : Type (u + 2) :=
  ObjectProperty.FullSubcategory fun F : Sheaf Y.smallEtaleTopology (Type (u + 1)) ↦
    IsFiniteLocallyConstantSheafOfTypes F

namespace FiniteLocallyConstant

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)

end FiniteLocallyConstant

end AlgebraicGeometry.Scheme
