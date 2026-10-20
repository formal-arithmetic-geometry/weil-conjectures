## What changed

The assigned module already contains a complete proof of
`AlgebraicGeometry.Scheme.Modules.external_cup_scalar_balance`; it has no `sorry`.
I copied the current module and node into the sandbox and verified the module against
its current adopted dependency
`WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`.
The private proof `ext_map_comp_smul` was normalized from one multi-lemma `rw` invocation to three explicit rewrites. This changes only proof syntax; no public declaration, statement, definition, or DAG record was changed.

## Proved and sorry left

The existing theorem `external_cup_scalar_balance` is proved. There are zero `sorry`s
in the assigned module, and this delivery adds zero `sorry`s.

## No longer needed

No proof imports or proof-dependency nodes were removed. The withdrawn duplicate Sheaf
field-linear operations module is not imported; the module uses the adopted
WeilConjectures twin already selected in the current source.

## Where the brief, the DAG or earlier work was wrong

The assignment is stale relative to the current repository: the item module was
already proved and its dependency migration was already landed. The current file compiles with `lcompile.py`; the public theorem and all intermediate private lemmas remain unchanged in type.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
