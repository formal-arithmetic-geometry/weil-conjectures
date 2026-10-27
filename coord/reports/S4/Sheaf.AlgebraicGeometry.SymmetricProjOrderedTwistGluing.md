## What changed

The proof of `AlgebraicGeometry.SymmetricProjTautologicalCharts.exists_ordered_twist_comparison`
now assembles two strict intermediate statements. `exists_ordered_twist_line` supplies the
(global) line isomorphism, and `ordered_twist_coordinate_compatibility` supplies the
coordinate equalities for a supplied line isomorphism. The item imports these two proof-only
modules and combines their conclusions. All three modules compile with `lcompile.py --all`.

## Proved and sorry left

The original item theorem is proved by a complete Lean term from the two intermediate
statements: 1 original hole closed by decomposition, 0 original holes remain. Two strictly
smaller proof obligations are added:

- `AlgebraicGeometry.SymmetricProjTautologicalCharts.exists_ordered_twist_line`
  (`lem-trf-symmetric-proj-ordered-twist-line`) remains `sorry`; it is the global line
  existence/gluing step.
- `AlgebraicGeometry.SymmetricProjTautologicalCharts.ordered_twist_coordinate_compatibility`
  (`lem-trf-symmetric-proj-ordered-twist-coordinates`) remains `sorry`; it is the local
  generator computation and descent of coordinate equalities.

No `sorry` occurs inside a definition, private declaration, or the completed parent proof.

## No longer needed

No pre-existing imports or DAG dependencies are removed. The parent proof now uses only the
 two new intermediate nodes; the previously listed geometric dependencies are delegated to
those nodes. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The prior split exposed the full gluing theorem as one large obligation. Its conclusion has
independent geometric components (line existence and coordinate compatibility), so retaining
those as separate named statements gives a strict decomposition and a short, checkable parent
proof. No target statement or existing definition was changed.

## New nodes

`lem-trf-symmetric-proj-ordered-twist-line` records the global line-isomorphism construction.
`lem-trf-symmetric-proj-ordered-twist-coordinates` records the coordinate-section equality for
a supplied isomorphism. Each node has a matching module and declaration in this delivery.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
