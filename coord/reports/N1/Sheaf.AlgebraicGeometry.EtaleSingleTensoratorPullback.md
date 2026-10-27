## What changed

Proved `AlgebraicGeometry.Etale.singleFunctorObjTensorIso_pullback` without changing
its statement or any definition. Its proof privately imports three new support
modules, each containing a fully proved theorem:

- `Sheaf.AlgebraicGeometry.EtaleSingleHomotopyTensorPullback` computes the single
  cochain tensor square for an additive monoidal left adjoint and passes it to the
  homotopy quotient.
- `Sheaf.AlgebraicGeometry.EtaleSinglePullbackCounit` identifies the prescribed
  single/pullback comparison with the exact derived counit.
- `Sheaf.AlgebraicGeometry.EtaleSingleTensoratorHomotopyFactorization` rewrites the
  existing flat single tensorator through the homotopy quotient and Qh.

The item combines these identities with the existing derived tensor/counit square
by a proved categorical transport calculation. The source and target single/Qh
isomorphisms cancel, leaving exactly the prescribed single/pullback comparison.
The original node's proof and dependencies record this argument.

Removed the unused public import of `Derived.TensorStructure`. The sole direct
importer, `Sheaf.AlgebraicGeometry.EtaleSingleFunctorMonoidalCompatibility`, already
imports that module explicitly. Its unchanged source is checked against the delivery.
The import change is recorded in
`coord/changes/etale-single-tensorator-pullback-imports.md`.

Validation: the four delivery modules and the unchanged direct importer compiled
using `lcompile.py --all`. The item took 48.9 seconds; the importer took 56.0
seconds. The temporary importer copy was removed after checking.

## Proved and sorry left

Closed the original module's sole hole:
`AlgebraicGeometry.Etale.singleFunctorObjTensorIso_pullback`
(`lem-pur-etale-single-tensorator-pullback`).

Added zero holes. All three new public support theorems and all private helpers
are proved. There is no `sorry` in any Lean file of this delivery; no obligation
is split off to another worker.

## No longer needed

Removed the unused public import
`WeilConjectures.SixFunctors.Etale.Derived.TensorStructure` from the item.
The statement uses only `Derived.Invertible`; the proof uses its existing derived
tensor/counit identity. The parent still imports `TensorStructure` for its own
statement. No module, declaration, node, or unit step is withdrawn.

The proof follows the assigned route, reusing the existing proved single cochain
tensor isomorphism and tensorator factorization. No declared mathematical dependency
of the original argument is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The newest blueprint locates
`sk-prop-a1-kummer` in `sec-six-functors-basics`, while the unit record still names its
older `sec-smooth-purity` source location; the current statement and proof were read
from `literature/blueprint/latest/`.

`blueprint_refs.py ancestor` returns `None` here because it follows node ids in
`created.item`, whereas this stage-3 node records its parent module name. The new
nodes inherit the item's recorded blueprint ancestor, `lem-pur-frame-independence`,
with the item prepended to its existing `via` list.

Profiling found costly sheaf-category instantiation and construction of the full
derived oplax monoidal instance. The component calculation is now proved for general
coefficient categories, and the transport calculation uses the comparison natural
transformation directly. These changes remove that cost without changing shared
definitions. The remaining cumulative checking cost is distributed among the three
proved support modules and the item. No transparency override is introduced.

## New nodes

`lem-pur-etale-single-homotopy-tensor-pullback` attaches the proved theorem
`AlgebraicGeometry.Etale.singleHomotopyTensorIso_pullback`. It is the ordinary
single-complex tensor square after the homotopy quotient, with no derived inverse
image, flat objects, or canonical derived single comparison in its statement.

`lem-pur-etale-single-pullback-counit` attaches the proved theorem
`AlgebraicGeometry.Etale.singleFunctorObjIsoQh_pullback_counit`. It identifies a single
comparison with the exact-functor counit, without tensor products or flatness.

`lem-pur-etale-single-tensorator-homotopy-factorization` attaches the proved theorem
`AlgebraicGeometry.Etale.singleFunctorObjTensorIso_homotopy_factorization`. It factors
one flat single tensorator through Qh, using the existing proved cochain factorization;
there is no inverse image or pullback equation in its statement.

All three nodes are proved support steps, not new sorry obligations. The import
change record is `coord/changes/etale-single-tensorator-pullback-imports.md`.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
