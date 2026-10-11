/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.SnapperNumericalPolynomial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Intersection numbers of invertible modules

Source: Stacks Project, Varieties, Definition 33.45.3, Tag 0BEP
(blueprint: def-sc-intersection-number).

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.intersectionNumber`: the coefficient of the product
  of the variables in the Euler-characteristic polynomial.
- `AlgebraicGeometry.Scheme.Modules.selfIntersectionNumber`: the repeated-bundle notation.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The intersection number `(L₁ ⋯ L_d · Z)` is the coefficient of the monomial with exponent
one in every variable in the rational polynomial representing the Euler characteristics
of `i_* O_Z` twisted by the integer tensor powers of `L₁, …, L_d`.
Source: Stacks Project, Varieties, Definition 33.45.3, Tag 0BEP
(blueprint: def-sc-intersection-number).

`Classical.epsilon` selects the polynomial by its evaluations on the integer lattice.
Existence follows from `exists_mvPolynomial_eulerChar_tensorPowers` applied to the coherent
module `i_* O_Z`; uniqueness is polynomial identity on the integer lattice over `ℚ`.
These facts are not part of the definition. The degree bound is `d`, since the support of
`i_* O_Z` is the image of the closed immersion. Negative tensor powers use the dual, exactly
as in the recorded Snapper statement. No polynomial data are supplied by `sorry`.
For `d = 0`, the exponent vector is empty, so the coefficient is the constant coefficient. -/
noncomputable def intersectionNumber
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (Z : Scheme.{u}) [Nonempty Z]
    (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ)
    (_hd : topologicalKrullDim Z = ((d : ℕ∞) : WithBot ℕ∞))
    (L : Fin d → X.Modules) [∀ j : Fin d, (L j).IsInvertible] : ℚ :=
  (Classical.epsilon fun P : MvPolynomial (Fin d) ℚ =>
    ∀ n : Fin d → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P =
      (((List.ofFn fun j : Fin d =>
        if 0 ≤ n j then (L j).tensorPow (n j).toNat
        else (L j).dual.tensorPow (-n j).toNat).foldl
          (fun M N : X.Modules => M ⊗ N)
          ((pushforward i).obj (SheafOfModules.unit _))).eulerChar k : ℚ)).coeff
    (Finsupp.onFinset Finset.univ (fun _ : Fin d => 1) (fun _ _ => Finset.mem_univ _))

/-- The notation `(L^d · Z)` means that all `d` invertible modules in the intersection
number are `L`.
Source: Stacks Project, Varieties, Definition 33.45.3, Tag 0BEP
(blueprint: def-sc-intersection-number). -/
noncomputable abbrev selfIntersectionNumber
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (Z : Scheme.{u}) [Nonempty Z]
    (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ)
    (hd : topologicalKrullDim Z = ((d : ℕ∞) : WithBot ℕ∞))
    (L : X.Modules) [L.IsInvertible] : ℚ :=
  intersectionNumber k X Z i d hd (fun _ : Fin d => L)

end AlgebraicGeometry.Scheme.Modules
