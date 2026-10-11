## Worker report

The module defines the transparent proposition `ClosedPointResidueFieldCriterion`
and states it in one theorem. Its proof is `sorry`. The proposition definition
holds the full formula and has no `sorry`.

- `K : Type u` and `[Field K]` render the base field; `{X : Scheme.{u}}` is the scheme.
- `f : X ⟶ Spec (.of K)` renders the structure morphism over `K`.
- `[LocallyOfFiniteType f] [QuasiCompact f]` render finite type as in the scheme
  conventions node; `(x : X)` is an arbitrary point.
- The proposition's `letI : Algebra K (X.residueField x)` uses the map induced by `f`, the
  isomorphism from the residue field of `Spec K` to its prime ideal's residue field,
  and the field equivalence from `K` to that residue field.
- `x ∈ closedPoints X ↔ Algebra.trdeg K (X.residueField x) = 0` is part (a)'s
  closedness/transcendence-degree equivalence.
- `x ∈ closedPoints X ↔ Module.Finite K (X.residueField x)` is part (a)'s
  closedness/finite-extension equivalence. The two equivalences together give the
  stated trdeg-zero/finite-extension equivalence.
- `IsSepClosed K → x ∈ closedPoints X →` is precisely part (b)'s two premises.
  Its conclusion contains `Module.Finite K (X.residueField x)`,
  `IsPurelyInseparable K (X.residueField x)`, and
  `IsSepClosed (X.residueField x)` for its three clauses. The theorem's
  `ClosedPointResidueFieldCriterion f x` unfolds to exactly these clauses.

Dependencies used: `Algebra.trdeg` from
`Mathlib.RingTheory.AlgebraicIndependent.Basic` (node
`def-kun-transcendence-degree`); `AlgebraicGeometry.Scheme.residueField` and
`Scheme.Hom.residueFieldMap` from `Mathlib.AlgebraicGeometry.ResidueField`
(`def-weil-residue-field`); `closedPoints` from
`Mathlib.Topology.JacobsonSpace` (`def-weil-closed-points`). The scheme
conventions node has no declaration of its own and explicitly delegates finite
type to `LocallyOfFiniteType` plus `QuasiCompact` from Mathlib.

Edge cases: the empty scheme has no `x`, so the universal claim is vacuous; no
point existence is assumed. A nonclosed generic point of an affine line has
positive trdeg, while a rational closed point has trdeg zero and finite
extension. In positive characteristic, a finite extension of a separably closed
field can be nontrivial and purely inseparable, so the statement does not assert
that the residue field equals the base. Characteristic zero is included.

Searches: `msearch leanfinder "closed point finite type scheme residue field
finite over base field transcendence degree zero separably closed"` found the
related `AlgebraicGeometry.isClosed_singleton_iff_locallyOfFiniteType`, which
does not state the full criterion. `msearch loogle
"AlgebraicGeometry.isClosed_singleton_iff_locallyOfFiniteType, Algebra.trdeg,
IsPurelyInseparable"` returned zero hits. `msearch grep
"isClosed_singleton|residueField.*finite|IsSepClosed|IsPurelyInseparable"
AlgebraicGeometry` found related declarations but no full match. `rg` over
`WeilConjectures` found `ClosedPoints.lean`, concerning finite *cardinality* of
residue fields over `ℤ`, not finite degree over arbitrary `K`. `grep -rn` for
the node id in `WeilConjectures` found nothing. `rg` over `lean/Sheaf` found no
matching theorem. The recorded Stacks/blueprint source directory is absent on
this machine; the node's statement and full proof were available in its JSON.

## Second reading by M1

The node introduces a field `K`, a scheme `X` of finite type over `K`, a point
`x : X`, and the structure morphism `f : X ⟶ Spec K`. The module renders these
as `{K : Type u} [Field K]`, `{X : Scheme.{u}}`, `(f : X ⟶ Spec (.of K))`, and
`(x : X)`. Finite type is rendered by exactly `[LocallyOfFiniteType f]`
and `[QuasiCompact f]`; there is no extra separatedness, Noetherian,
finite-presentation, or characteristic hypothesis. Verdict: match.

The node's part (a) clause ``x is closed iff trdeg_K kappa(x) = 0`` is the
first conjunct of `ClosedPointResidueFieldCriterion f x`, namely
`x ∈ closedPoints X ↔ Algebra.trdeg K (X.residueField x) = 0`. The clause
``x is closed iff kappa(x) is finite over K`` is the second conjunct,
`x ∈ closedPoints X ↔ Module.Finite K (X.residueField x)`. The local `letI`
uses the residue-field map induced by `f` and identifies `kappa(f x)` with
`K`, so `Module.Finite` and `Algebra.trdeg` refer to the intended extension.
Verdict: both equivalences and their quantifier order match.

The node's part (b) hypotheses ``K separably closed`` and ``x closed`` are
rendered as `IsSepClosed K → x ∈ closedPoints X →`. Its three conclusions are
rendered in the same order as
`Module.Finite K (X.residueField x) ∧ IsPurelyInseparable K
(X.residueField x) ∧ IsSepClosed (X.residueField x)`. Verdict: match.

Dependencies were checked against their declarations: `Algebra.trdeg` is the
Mathlib transcendence degree; `X.residueField x` and `f.residueFieldMap x` are
the Mathlib residue-field notions; and `closedPoints X` is Mathlib's singleton
closed-point set. The scheme-conventions node fixes finite type as the two
classes used above and adds no hidden hypothesis. Searches in Mathlib and
`WeilConjectures/` found only related formulations, not this composite
criterion; no duplicate declaration exists in `lean/Sheaf`.

Edge cases checked: the empty scheme is covered vacuously because `x : X` has
no inhabitant; no point-existence assumption is added. The zero-dimensional
case is represented by `trdeg = 0`; positive characteristic permits nontrivial
purely inseparable residue extensions; characteristic zero remains included;
and the universe is shared by `K` and `X` without excluding the node's cases.

The only mismatch found was documentary: both declaration docstrings named the
blueprint but omitted its source place. I added `Source: blueprint node
`lem-kun-closed-point-field`, order 1694` to both docstrings. No mathematical
or typing change was needed; `scompile.py` compiles the repaired module cleanly.

## Reviewer fix (R-cpf0724)

H4: the `K`-algebra structure on `X.residueField x` induced by the structure morphism exists
in the source repository as `AlgebraicGeometry.Scheme.Hom.residueFieldAlgebraMap`
(`WeilConjectures/ZetaSeries.lean`, used by `Hom.finite_residueField_of_isClosed` and
`Hom.dense_setOf_isClosed_finite_isSeparable`); the delivery rebuilt it inline. The fixed module
uses `letI := (f.residueFieldAlgebraMap x).toAlgebra` and states the three clauses directly in the
theorem's type, dropping the wrapper `ClosedPointResidueFieldCriterion` (no node's notion; it hid
the statement from the record). The statement is otherwise unchanged; the theorem's docstring now
gives the node's proof in its four steps. The source's `Hom.finite_residueField_of_isClosed` is
one direction of the second equivalence of (a) only, so no existing declaration states the node.
