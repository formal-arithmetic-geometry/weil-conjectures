/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.AlgebraicGeometry.TorIndependentPerfectTensorBaseChange
public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeNaturality
public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeCoordinateNaturality
public import WeilConjectures.AlgebraicGeometry.FlatPullbackTorIndependent
public import WeilConjectures.AlgebraicGeometry.PseudoCoherentSupportAnnihilation

/-!
# The derived base change map is invertible for flat base change

Consider a cartesian square of schemes
```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```
with `S`, `S'` affine, `f` quasi-compact and quasi-separated and `g` flat. Then the canonical
base change map `Lg^* Rf_* E ⟶ Rf'_* Lg'^* E` is an isomorphism for every `E ∈ D_QCoh(𝒪_X)`
(Stacks 08IB, 02KH).

The square is Tor-independent since `g` is flat
(`AlgebraicGeometry.flat_right_pullback_torIndependent`), so this is the case `P = 𝒪_X` of
`AlgebraicGeometry.torIndependent_perfect_tensor_baseChange`, transported to an arbitrary
cartesian square by `AlgebraicGeometry.exists_derivedBaseChange_coordinate_naturality`.
-/

@[expose] public section

universe w u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

end AlgebraicGeometry
