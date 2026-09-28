/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity

/-!
# A failure of base change is detected over a field

If `BC(p, Λ, q - 1)` holds but `BC(p, Λ, q)` fails, then the failure is already visible after
an affine base change `S' ⟶ S` and over a field: there is a Cartesian square whose base is the
spectrum of a field and a sheaf of `Λ`-modules on it for which the degree-`q` base-change map
is not an isomorphism. The data of such a counterexample is bundled as
`AlgebraicGeometry.Etale.FieldFailure`.

The proof applies `AlgebraicGeometry.exists_spec_field_of_isQcqsLocalProperty` to the
property "the chosen cokernel element survives"; the closed–open splitting hypothesis of that
lemma is supplied by `AlgebraicGeometry.Etale.mono_cokernelMap` and
`AlgebraicGeometry.Etale.mono_cokernelDesc`.

## Main definitions

- `AlgebraicGeometry.Etale.FieldFailure`: a counterexample to `BC(p, Λ, q)` living over a
  field, after an affine base change of `p`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_fieldFailure`: if `BC(p, Λ, q - 1)` holds and
  `BC(p, Λ, q)` fails, such a counterexample exists.

## References

- Stacks Project, Lemma 59.88.6, <https://stacks.math.columbia.edu/tag/0F07>
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}} (p : X ⟶ S)

/-- A counterexample to `BC(p, Λ, q)` living over a field: an affine scheme `S'` affine over
`S`, the base change `p' : X' ⟶ S'` of `p` along it, a field `K` over `S'`, and a sheaf `F`
of `Λ`-modules on `(Spec K)_ét` for which the degree-`q` base-change map of the geometric
fibre square is not an isomorphism. The two squares are stacked:

```
Y' -----e-----> Spec K
|                 |
h                 g
v                 v
X' -----p'-----> S'
|                 |
b                 a
v                 v
X ------p------>  S
```

The base change `a : S' ⟶ S` is required to be affine so that the property `BC(p, Λ, q - 1)`,
which quantifies over quasi-compact quasi-separated morphisms to `S`, transports to `p'`. -/
structure Etale.FieldFailure (q : ℤ) where
  /-- the affine base of the counterexample -/
  S' : Scheme.{u}
  [isAffine : IsAffine S']
  /-- the base change morphism -/
  a : S' ⟶ S
  [isAffineHom : IsAffineHom a]
  /-- the total space of the base change of `p` -/
  X' : Scheme.{u}
  /-- the base change of `p` -/
  p' : X' ⟶ S'
  /-- the morphism covering `a` -/
  b : X' ⟶ X
  /-- `p'` is the base change of `p` along `a` -/
  isPullback : IsPullback b p' p a
  /-- the field over which the failure happens -/
  K : Type u
  [field : Field K]
  /-- the point of `S'` -/
  g : Spec (CommRingCat.of K) ⟶ S'
  /-- the fibre of `p'` over that point -/
  Y' : Scheme.{u}
  /-- the projection of the fibre to the point -/
  e : Y' ⟶ Spec (CommRingCat.of K)
  /-- the projection of the fibre to `X'` -/
  h : Y' ⟶ X'
  /-- the fibre square is Cartesian -/
  isPullback_fibre : IsPullback e h g p'
  /-- the coefficient sheaf witnessing the failure -/
  F : Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
  /-- the base-change map is not an isomorphism -/
  not_isIso : ¬ IsIso (Etale.baseChangeHomologyMap Λ isPullback_fibre q F)

/-- Blueprint `sk-lem-failure-field`: A failure is detected on the generic fibre.

If the base-change property `BC(p, Λ, q - 1)` holds while `BC(p, Λ, q)` fails for some
`q ≥ 1`, there is a counterexample over a field, that is, an
`AlgebraicGeometry.Etale.FieldFailure`. -/
@[stacks 0F07]
theorem Etale.nonempty_fieldFailure (q : ℤ) (hq : 1 ≤ q)
    (hprev : Etale.BaseChangeProperty Λ p (q - 1))
    (hfail : ¬ Etale.BaseChangeProperty Λ p q) :
    Nonempty (Etale.FieldFailure Λ p q) :=
  sorry

end AlgebraicGeometry
