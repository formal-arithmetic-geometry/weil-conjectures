## Worker report

The module defines `AlgebraicGeometry.effectiveCartierDivisor_finite_over_field`.
It represents the effective Cartier divisor by an invertible ideal sheaf
`J : X.IdealSheafData`, with closed subscheme `J.subscheme` and inclusion
`J.subschemeι`.

Hypotheses are rendered by `{k : Type u} [Field k]`,
`X : Scheme.{u}` with `[X.Over (Spec (.of k))]`, properness
`[IsProper (X ↘ Spec (.of k))]`, `(hX : X.dim ≤ 1)`, and
`(hJ : J.IsInvertible)`.  The conclusion renders the six clauses as
`J.subscheme.dim ≤ 0`, closed singleton points, no nonempty open of `X` in
the image of `J.subschemeι`, `IsAffine J.subscheme`, finiteness of
`J.subschemeι ≫ X ↘ Spec (.of k)`, and finite-dimensional global sections
`FiniteDimensional k (Γ(J.subscheme, ⊤))` under an explicitly existential
`Algebra k (Γ(J.subscheme, ⊤))` structure.

Dependencies used: `Sheaf.AlgebraicGeometry.Dimension` /
`AlgebraicGeometry.Scheme.dim`; `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible` /
`AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible`; Mathlib
`AlgebraicGeometry.IsProper`; and the recorded smooth-curve declaration
`AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.isFinite_subschemeι_comp`
(inspected but not used because it has extra smoothness hypotheses).

Edge cases checked: empty divisor, `Spec k[t]` with divisor `V(t)`, and
`Spec (k[e]/(e^2))`; the `WithBot ℕ∞` dimension handles the empty scheme.
Searches: LeanFinder/Mathlib search for effective Cartier divisors and finite
proper curves (only general finiteness criteria), Loogle for Cartier/finiteness
names (no match), grep for `EffectiveCartier|CartierDivisor` (none), and `rg`
through source and existing Sheaf modules (only the smooth-curve theorem).
No exact existing declaration was found.

## Earlier second reading (a previous round; superseded)

The node and module were reread together: every hypothesis and each of the six
conclusion clauses is present, the recorded notions are imported, and the proof
is `sorry` only.

## Second reading by G1

Node and source: Stacks, Varieties Tag 0AYY, proof's first two sentences,
uses Divisors Tag 07ZU and Varieties Tag 06LH. The source assumes a field,
a proper scheme of dimension at most one over it, and an effective Cartier
divisor; it imposes no smoothness, nonemptiness, or characteristic condition.

- Field `k`: `{k : Type u} [Field k]`; exact.
- Scheme `X` over `k`: `(X : Scheme.{u}) [X.Over (Spec (.of k))]`; exact.
- Properness: `[IsProper (X ↘ Spec (.of k))]`; exact by the proper-morphism
  dependency's Mathlib match.
- Dimension bound: `(hX : X.dim ≤ 1)`; `Scheme.dim` is the local-ring
  supremum of `def-pc-dimension`, with bottom for the empty scheme; exact.
- Effective Cartier divisor `D`: `(J : X.IdealSheafData)
  (hJ : J.IsInvertible)` and `J.subscheme`; `IsInvertible` requires a regular
  principal ideal on affine neighbourhoods of every point, precisely the
  effective Cartier ideal of `def-nagata-effective-cartier-ideal`. The
  smooth-curve theorem recorded on `def-sc-effective-cartier-divisor` does
  not define the general notion and cannot replace this hypothesis.
- `dim D ≤ 0`: `J.subscheme.dim ≤ 0`; exact.
- Every point of `D` closed in `D`: `∀ x : J.subscheme,
  IsClosed ({x} : Set J.subscheme)`; exact.
- No nonempty open of `X` contained in `D`: negation of the existence of
  `U : X.Opens` with `U ≠ ⊥` and every `x : U` lifted through
  `J.subschemeι`; exact on underlying points.
- `D` affine: `IsAffine J.subscheme`; exact.
- `D → Spec k` finite: `IsFinite (J.subschemeι ≫ X ↘ Spec (.of k))`; exact.
- Finite-dimensional global functions over `k`: `FiniteDimensional k
  (Γ(J.subscheme, ⊤))` with the local `ΓAlgebra` attached to that composite
  morphism; exact scalar action from the structure morphism.

Edge cases: the empty scheme and empty divisor satisfy the dimension bound
through `WithBot`; `U ≠ ⊥` prevents a vacuous open-set obstruction. The
zero-dimensional, possibly nonreduced divisor is included. No index set or
natural-number parameter occurs. The field is arbitrary, including every
characteristic; the shared universe `u` ranges over every field universe.

Independent searches: LeanFinder `finite global functions effective Cartier
divisor proper curve` returned only unrelated elliptic-curve and function-field
declarations; Loogle `finite effective Cartier divisor` returned no match;
grep/`rg` of Mathlib, `WeilConjectures`, and `lean/Sheaf` for Cartier divisors,
invertible ideals, and finite subschemes found only the smooth proper curve
theorem `IsInvertible.isFinite_subschemeι_comp`, whose hypotheses are stronger.
`Scheme.Hom.ΓAlgebra` in source `Morphisms/FiberDegree.lean` is the canonical
algebra structure used here. No exact existing theorem states all clauses.

Mismatch repaired: the worker's existential `Algebra k Γ(D, O_D)` could choose
an algebra structure unrelated to `D → Spec k`; replaced it with the existing
`Scheme.Hom.ΓAlgebra` of that map, updated the node's recorded signature, and
compiled the module cleanly. There are no new definition or dependency modules.
