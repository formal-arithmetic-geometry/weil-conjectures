/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs

/-!
# A failure of base change is detected over a field

If `BC(p, Λ, q - 1)` holds but `BC(p, Λ, q)` fails, then the failure is already visible after
an affine base change `S' ⟶ S` and over a field: there is a Cartesian square whose base is the
spectrum of a field and a sheaf of `Λ`-modules on it for which the degree-`q` base-change map
is not an isomorphism.

The proof applies `AlgebraicGeometry.exists_spec_field_of_isStableUnderThickening` to the
property "the chosen cokernel element survives"; the closed–open splitting hypothesis of that
lemma is supplied by `AlgebraicGeometry.Etale.mono_baseChangeHomologyMap`.

## Main statements

- `AlgebraicGeometry.Etale.exists_notIsIso_baseChangeHomologyMap_over_field`.

## References

- Stacks Project, Lemma 59.88.6, <https://stacks.math.columbia.edu/tag/0F07>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}} {p : X ⟶ S}

/-- Blueprint `sk-lem-failure-field`: A failure is detected on the generic fibre.

If the base-change property `BC(p, Λ, q - 1)` holds while `BC(p, Λ, q)` fails, there is a
counterexample over a field: an affine scheme `S'` over `S`, the base change `p' : X' ⟶ S'` of
`p`, a field `K`, a morphism `Spec K ⟶ S'` and a sheaf `F` of `Λ`-modules on `(Spec K)_ét` for
which the degree-`q` base-change map of `AlgebraicGeometry.Etale.baseChangeHomologyMap` is not
an isomorphism. -/
@[stacks 0F07]
theorem Etale.exists_notIsIso_baseChangeHomologyMap_over_field (q : ℤ)
    (hq : Etale.BaseChangeProperty Λ p (q - 1)) (hfail : ¬ Etale.BaseChangeProperty Λ p q) :
    ∃ (S' X' : Scheme.{u}) (_ : IsAffine S') (a : S' ⟶ S) (p' : X' ⟶ S') (b : X' ⟶ X)
      (_ : IsPullback b p' p a) (K : Type u) (_ : Field K) (Y' : Scheme.{u})
      (g : Spec (.of K) ⟶ S') (e : Y' ⟶ Spec (.of K)) (h : Y' ⟶ X')
      (sq : IsPullback e h g p')
      (F : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      ¬ IsIso (Etale.baseChangeHomologyMap Λ sq q F) :=
  sorry

end AlgebraicGeometry
