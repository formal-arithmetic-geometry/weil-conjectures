## Worker report

The module states `AlgebraicGeometry.isAffine_and_isFinite_of_dim_le_zero`, with a `sorry`
proof. Its source is Stacks Project, Varieties, Lemma 33.20.2 (Tag 06LH), algebraic case.
The local `literature/stacks-project/` checkout is absent on this machine; I read the cited
lemma at https://stacks.math.columbia.edu/tag/06LH. Its algebraic case says affine and finite
over the field. The node's `≤ 0` includes the empty case, as its proof notes.

Statement correspondence:

- Field `k`: `{k : Type u} [Field k]`.
- Scheme `Y` over `k`: `(Y : Scheme.{u}) [Y.Over (Spec (.of k))]`. This instance supplies the
  structure morphism `Y ↘ Spec (.of k)`.
- Finite type of that morphism: `[LocallyOfFiniteType (Y ↘ Spec (.of k))]` and
  `[QuasiCompact (Y ↘ Spec (.of k))]`, the two conditions of the Mathlib match for
  `def-weil-finite-type-morphism`.
- Dimension at most zero: `(hY : Y.dim ≤ 0)` using `Scheme.dim` from
  `Sheaf.AlgebraicGeometry.Dimension`.
- Affineness: `IsAffine Y`, the first conjunct of the conclusion.
- Finite structure morphism: `IsFinite (Y ↘ Spec (.of k))`, the second conjunct.

Dependency declarations inspected and used: `def-weil-finite-type-morphism` maps to
`AlgebraicGeometry.LocallyOfFiniteType` in
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `AlgebraicGeometry.QuasiCompact` in
`Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`; `def-pc-dimension` maps to
`AlgebraicGeometry.Scheme.dim` in `Sheaf.AlgebraicGeometry.Dimension`;
`def-pc-scheme` maps to `AlgebraicGeometry.Scheme` in Mathlib;
`def-weil-finite-integral-morphism` maps to `AlgebraicGeometry.IsFinite` in
`Mathlib.AlgebraicGeometry.Morphisms.Finite`. I read each recorded signature and docstring.

Edge cases: an empty `Y` is included, since there is no `Nonempty Y` binder and
`Scheme.dim` assigns it `⊥`, which is at most zero. `Spec k`, a nonreduced finite algebra
such as `k[ε]/(ε²)`, and finite disjoint unions of points remain included; the affine line
is excluded by the dimension hypothesis. No restriction on the characteristic of `k` occurs.

Existing declaration searches:

- `msearch.py ... leanfinder "finite type zero dimensional scheme over a field is affine and
  finite over the field"`: eight hits, including finite discrete schemes are affine and
  Artinian schemes are finite; no exact combined theorem.
- `msearch.py ... loogle "AlgebraicGeometry.IsAffine, AlgebraicGeometry.IsFinite"`: no hit.
- `msearch.py ... grep "isAffine.*dim|dim.*isAffine|isFinite.*dim|dim.*isFinite"
  AlgebraicGeometry`: fourteen hits, no exact theorem.
- `rg` in the source `WeilConjectures/` for dimension, finite and affine schemes: no exact
  theorem. `grep -rn "lem-pc-algebraic-dim-zero-affine-finite"` there: no hit.
- `rg` in `lean/Sheaf/AlgebraicGeometry` for dimension, finiteness and Artinian schemes:
  no exact theorem. The source module `FiniteOverField.lean` contains only the converse
  direction from finiteness to finite discrete space.

The server single-file compile completed with exit code 0 in 1.6 seconds and no messages.

## Second reading by H1

Independent comparison with the node and Stacks Project, Varieties, Tag 06LH,
Lemma 33.20.2. Its Definition 33.20.1 says an algebraic `k`-scheme is precisely a
scheme whose structure morphism to `Spec k` is of finite type. Neither definition
adds separatedness, reducedness, or a characteristic assumption.

- Object `k`, a field: `{k : Type u} [Field k]`; exact, with arbitrary characteristic.
- Object `Y`, a scheme over `k`: `(Y : Scheme.{u}) [Y.Over (Spec (.of k))]`;
  the latter gives the structure morphism `Y ↘ Spec (.of k)`; exact.
- Hypothesis finite type over `k`: `[LocallyOfFiniteType (Y ↘ Spec (.of k))]`
  and `[QuasiCompact (Y ↘ Spec (.of k))]`; together these are precisely finite
  type as defined in dependency `def-weil-finite-type-morphism` and Stacks 01T0.
- Hypothesis dimension at most zero: `(hY : Y.dim ≤ 0)`; `Scheme.dim` in the
  recorded `def-pc-dimension` module is the supremum of the Krull dimensions
  of the local rings. Exact, with `⊥` for an empty scheme.
- Conclusion affine: `IsAffine Y`; exact Mathlib notion from `def-pc-scheme`.
- Conclusion finite over the field: `IsFinite (Y ↘ Spec (.of k))`; exact
  Mathlib notion from `def-weil-finite-integral-morphism`. The conjunction
  retains both clauses and no extra conclusion.

The recorded dependency signatures were checked against their definitions:
`Scheme.dim` in `Sheaf.AlgebraicGeometry.Dimension`, `Scheme` and `IsAffine`
in Mathlib, `LocallyOfFiniteType` and `QuasiCompact` in Mathlib's morphism
modules, and `IsFinite` in `Mathlib.AlgebraicGeometry.Morphisms.Finite`.
There is no extra Noetherian, proper, separated, nonempty, or universe
restriction in the theorem.

Edge cases: the empty scheme satisfies `Y.dim ≤ 0` because its dimension is
`⊥`, and both conclusions remain part of the statement. A zero ring may
appear as its affine coordinate ring. `Spec k`, nonreduced Artinian spectra,
and finite disjoint unions of points are included. There is no index set or
integer `n` in this node; dimension zero is covered by `≤ 0`. The field has
arbitrary characteristic and the universe `u` is explicitly bound.

Independent existing-declaration searches: `msearch.py` LeanFinder query
`affine finite zero dimensional algebraic scheme field` found component facts
such as affineness of finite discrete schemes, but no combined theorem;
Loogle query `AlgebraicGeometry.IsFinite, AlgebraicGeometry.Scheme.dim`
returned no result because the project-specific `Scheme.dim` is unknown to
that index; grep query `IsArtinianScheme|finite_of.*dim|dim.*isFinite`
found Artinian and quasi-finite component facts, not this conclusion.
An `rg` search of the source `WeilConjectures/AlgebraicGeometry/FiniteOverField.lean`
and the project's `lean/Sheaf/AlgebraicGeometry` found only the converse or
related finite-over-field results. The new theorem does not duplicate one.

Mismatches found: none. Changes to the Lean module or node: none. The
statement remains verbatim equal to the node's `lean.statement`; the proof
is `sorry`, and its docstring follows the node's four proof steps.
