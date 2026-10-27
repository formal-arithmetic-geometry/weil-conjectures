## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceLargestSchematicOpenOverField` states
`AlgebraicGeometry.AlgebraicSpace.exists_largest_schematic_open_over_field`.
For a field `k` and an algebraic space `X` over `Spec k`, it asserts an open
subspace `U : OpenSubspace X` whose presheaf is Mathlib's
`Functor.IsRepresentable`, and that every representable open subspace `V` is
below `U` in the `PartialOrder` supplied by `OpenSubspace`. The theorem proof is
`sorry`, as required for stage 2.

The field hypothesis is rendered by `(k : Type u) [Field k]`; `Spec (.of k)`
is the scheme base, and `(X : AlgebraicSpace (Spec (.of k)))` is the algebraic
space over that base. The open-subspace notion and inclusion order are rendered
by `AlgebraicGeometry.AlgebraicSpace.OpenSubspace` from
`Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`. The phrase “represented by
a scheme” is rendered by `U.val.toFunctor.IsRepresentable`, whose Mathlib
meaning is existence of a representing object in the category of schemes over
`Spec k`. The maximality clause is
`∀ V : OpenSubspace X, V.val.toFunctor.IsRepresentable → V ≤ U`.
No quasi-separatedness, finite-type, quasi-compactness, separation, or
nonemptiness hypothesis is present; the existential permits the empty open
subspace. The statement has no additional density assertion.

The only statement dependency declarations used are:

- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`,
  `AlgebraicGeometry.AlgebraicSpace.OpenSubspace`;
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace`;
- Mathlib `Field` (`Mathlib.Algebra.Field.Defs`).

Searches for an existing declaration were run on 2026-10-24: `msearch.py`
`leanfinder` query “An algebraic space over a field has a largest open subspace
represented by a scheme” returned only generic scheme affine/open results;
`msearch.py` `leansearch` query “An algebraic space has a largest open subspace
which is representable by a scheme” returned only generic scheme affine/open
results; `msearch.py` `loogle` query `"AlgebraicSpace", "OpenSubspace"`
returned 0 hits; `msearch.py` `grep` query
`schematic.?locus|largest.*schem|schematic.*open` in `AlgebraicGeometry`
returned 0 hits; and `rg` over `lean/WeilConjectures` and `lean/Sheaf` found no
statement of this theorem (the existing `exists_dense_scheme_open` concerns a
different quasi-compact diagonal hypothesis). Thus no existing declaration
matches this node.

Edge cases checked: `OpenSubspace X` is a subtype with a genuine partial order;
the existential allows the empty open, and no index, finiteness, separation, or
density condition was introduced. The base field may have any characteristic.

## Second reading by Q41

I reread the node and module line by line. The node's field and algebraic-space
hypotheses correspond to `k : Type u`, `[Field k]`, and `X` over `Spec k`. Its
open-subspace and inclusion-order clause corresponds exactly to `OpenSubspace`
and `≤`. Its two schematic clauses correspond to `IsRepresentable` for `U` and
for each `V`, with `V ≤ U`. The source explicitly imposes no
quasi-separatedness, finite-type, quasi-compactness, or nonemptiness condition;
none appears in the Lean statement. The source allows the largest open to be
empty; an existential over `OpenSubspace X` does not exclude that case. No
mismatch was found.
