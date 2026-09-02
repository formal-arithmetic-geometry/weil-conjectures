/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Modules.Cohomology
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# The Riemann–Roch theorem for smooth projective curves

Let `k` be a field and `f : X ⟶ Spec k` a scheme over `k`. The cohomology
`Hⁱ(X, ℱ)` of an `𝒪_X`-module `ℱ` is a `k`-vector space, and for `X` proper over `k` and `ℱ`
coherent it is finite dimensional and vanishes for large `i`. This file introduces the three
numerical invariants built out of these dimensions — the Euler characteristic of a module, the
degree of an invertible module and the genus of a curve — and states the Riemann–Roch theorem
relating them.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.eulerCharacteristic f M`: the Euler characteristic
  `χ(X, ℱ) = ∑ᵢ (-1)ⁱ dim_k Hⁱ(X, ℱ)`.
- `AlgebraicGeometry.Scheme.Modules.degree f M`: the degree `deg(ℒ) = χ(X, ℒ) - χ(X, 𝒪_X)`
  of an invertible `𝒪_X`-module.
- `AlgebraicGeometry.Scheme.genus f`: the genus `g(X) = dim_k H¹(X, 𝒪_X)` of a curve.

## Main statements

- `AlgebraicGeometry.riemannRoch`: for an invertible module `ℒ` on a smooth projective curve
  over an algebraically closed field,
  `dim_k H⁰(X, ℒ) - dim_k H¹(X, ℒ) = deg(ℒ) + 1 - g(X)`.

## Implementation notes

The Euler characteristic is a `finsum` over all `i : ℕ` rather than a finite sum over a range:
this is the idiom used by `CategoryTheory.GradedObject.eulerChar`, and it takes the junk value
`0` when the support is infinite. Likewise `Module.finrank` takes the junk value `0` on a module
that is not free of finite rank. The hypotheses under which these junk values do not occur — `X`
proper over `k` and `ℱ` coherent — are not part of the definitions; that they are the right
hypotheses is the blueprint's `lem:pc-euler-characteristic-well-defined`. For the same reason
`genus` is defined for an arbitrary scheme over `k`, without the geometric irreducibility
hypothesis under which the blueprint states `def:pc-genus`.

The Euler characteristic and the degree are invariants of a module and live in the
`Scheme.Modules` namespace alongside `Scheme.Modules.cohomology`, whereas the genus is an
invariant of the scheme itself.

## Blueprint

`eulerCharacteristic` implements `def:pc-euler-characteristic`, `degree` implements
`def:pc-degree-line-bundle`, `genus` implements `def:pc-genus` and `riemannRoch` implements
`thm:pc-riemann-roch`.  The proof of `riemannRoch` is a `sorry`, and the three definitions
depend on the `sorry`ed instance `SheafOfModules.isGrothendieckAbelian`, so `#print axioms`
reports `sorryAx` on all four.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

namespace Scheme

open Modules

namespace Modules

/-- The **Euler characteristic** `χ(X, ℱ) = ∑ᵢ (-1)ⁱ dim_k Hⁱ(X, ℱ)` of an `𝒪_X`-module `ℱ`
on a scheme `f : X ⟶ Spec k` over a field `k`.

The sum is a `finsum`, so it is `0` unless all but finitely many of the summands vanish; the
hypotheses that make this the honest alternating sum are the blueprint's
`lem:pc-euler-characteristic-well-defined`.
(blueprint: `def:pc-euler-characteristic`, Stacks 0BEJ) -/
@[stacks 0BEJ]
noncomputable def eulerCharacteristic (f : X ⟶ Spec (.of k)) (M : X.Modules) : ℤ :=
  ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * Module.finrank k ((cohomology f i).obj M)

/-- The **degree** `deg(ℒ) = χ(X, ℒ) - χ(X, 𝒪_X)` of an invertible `𝒪_X`-module `ℒ` on a
scheme `f : X ⟶ Spec k` over a field `k`.

The definition makes sense for an arbitrary `𝒪_X`-module; it is only for invertible modules on
a proper scheme that it has the expected properties.
(blueprint: `def:pc-degree-line-bundle`, Stacks 0AYR) -/
@[stacks 0AYR]
noncomputable def degree (f : X ⟶ Spec (.of k)) (M : X.Modules) : ℤ :=
  eulerCharacteristic f M - eulerCharacteristic f (SheafOfModules.unit _)

end Modules

/-- The **genus** `g(X) = dim_k H¹(X, 𝒪_X)` of a curve `f : X ⟶ Spec k` over a field `k`.

The definition is made for an arbitrary scheme over `k`; the blueprint states it for a
geometrically irreducible smooth projective curve, which is where it computes the genus in the
classical sense.
(blueprint: `def:pc-genus`, Stacks 0B9W) -/
@[stacks 0B9W]
noncomputable def genus (f : X ⟶ Spec (.of k)) : ℕ :=
  Module.finrank k ((cohomology f 1).obj (SheafOfModules.unit _))

end Scheme

open Scheme Scheme.Modules

/-- **Riemann–Roch for smooth projective curves**: if `X` is a smooth projective curve over an
algebraically closed field `k` of genus `g` and `ℒ` is an invertible `𝒪_X`-module of degree
`d`, then `dim_k H⁰(X, ℒ) - dim_k H¹(X, ℒ) = d + 1 - g`.
(blueprint: `thm:pc-riemann-roch`) -/
theorem riemannRoch [IsAlgClosed k] (f : X ⟶ Spec (.of k)) [IsSmoothProjectiveCurve f]
    (M : X.Modules) [M.IsInvertible] :
    (Module.finrank k ((cohomology f 0).obj M) : ℤ) -
      Module.finrank k ((cohomology f 1).obj M) = degree f M + 1 - genus f := by
  sorry

end AlgebraicGeometry
