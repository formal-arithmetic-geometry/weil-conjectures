## What changed

Replaced the sole `sorry` in `lean/Sheaf/AlgebraicGeometry/BaseChangeDimension.lean`,
`AlgebraicGeometry.baseChange_dim`, with a complete Lean proof following the existing node's
three-step plan. No signature, definition, public import, or existing docstring changed.

A proved private helper, `topologicalKrullDim_eq_iSup_of_affine_openCover`, applies
`Scheme.dim_eq_iSup_ringKrullDim_of_affineOpenCover` to the ranges of an affine open cover.
The isomorphisms `isoOpensRange` and `isoSpec`, homeomorphism invariance, and
`PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim` convert its formula to the supremum
of the chart dimensions.

For an empty source, the first pullback projection proves the pullback empty; the dimension
comparison theorem and the empty supremum give equality. For a nonempty source, Mathlib's
surjectivity instances for a morphism between field spectra and its base change prove the
pullback nonempty. `Scheme.Pullback.openCoverOfLeft` supplies its affine charts.
For each original chart, `Spec.preimage` supplies its base-field algebra structure,
`HasRingHomProperty.Spec_iff` proves finite generation from `LocallyOfFiniteType`, and
`pullbackSpecIso` identifies its base change with the tensor-product spectrum. The first
clause of `dim_base_change` equates the chart ring dimensions; `iSup_congr` finishes.
All four universes of that bundled theorem are explicitly instantiated to avoid an
unconstrained universe from its unused second clause.

Searches: Lean Finder for dimension invariance of finite type schemes under field extension;
Loogle for `topologicalKrullDim`; launcher grep for
`topologicalKrullDim.*pullback|pullback.*topologicalKrullDim`; and repository/Mathlib `rg`
for dimension and pullback chart lemmas. No existing theorem directly closes this statement.
The existing stated dependencies suffice without any new unproved intermediate statement.

## Proved and sorry left

Proved `AlgebraicGeometry.baseChange_dim` (node `base-change-dimension`): 1 of 1 original
sorries removed. The private affine-cover helper is also proved. No `sorry` remains in the
item's module, and the delivery adds no `sorry` anywhere.

This is a stage-3 proof from existing declarations, not a claim of transitive axiom freedom:
it uses the currently stated `AlgebraicGeometry.dim_base_change`
(node `lem-pc-dim-base-change`),
`AlgebraicGeometry.Scheme.dim_eq_iSup_ringKrullDim_of_affineOpenCover`
(node `lem-pc-dimension-affine-open-cover`), and
`AlgebraicGeometry.Scheme.dim_eq_topologicalKrullDim`
(node `lem-pc-scheme-dimension-local-rings`). Those imported proofs remain subsequent items.

Local compilation passes with no errors or warnings. The proof explicitly includes the empty
scheme, and the ring theorem includes zero charts. It uses no connectedness, exact
one-dimensionality, or integrality assumption; zero-dimensional and disconnected curves
therefore retain the original statement's coverage.

## No longer needed

None. All three original proof imports are used. No original node or module is pruned:
the existing affine scalar-extension and affine-cover route is retained. A trial explicit
Mathlib `PullbackCarrier` import was removed because the original imports already provide
its declarations and instances; it is not part of the delivery.

## Where the brief, the DAG or earlier work was wrong

No statement or proof-plan correction was needed. The unit's `realized` statement and step
lists are empty; the existing node's route is nevertheless preserved. The DAG already
records all logical proof dependencies, so no node update or change record is necessary.

## Second reading by M1

1. Compared the delivered module against the repository with `diff -u`: the only
   changes are a proved private helper and the body of `baseChange_dim`. The existing
   signature, docstring, definitions and imports are byte-for-byte unchanged. Pass;
   no statement change or change record is needed.
2. Independently compiled the delivered module with `lcompile.py`: no errors or
   warnings. Scanned its Lean source: no `sorry`, prohibited declaration or kernel
   bypass. A scratch copy prints axioms for both the private helper and
   `baseChange_dim`: only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`
   from the existing imported open theorems. Pass as a stage-3 reduction; this is
   not yet a transitively axiom-free target.
3. No split-off statement or new unproved theorem exists. The private helper is a
   direct conversion of the existing affine-cover formula, with the correct
   nonemptiness hypothesis and arbitrary (including empty) affine charts. Reviewed
   the empty-source branch, finite-type inference on each chart, the induced
   algebra map, the pullback isomorphism, and both dimension-equality directions.
   Pass; zero rings, zero-dimensional and disconnected sources remain covered.
4. Independently searched Lean Finder for Krull dimension as a supremum on affine
   open coverings, Loogle for `ringKrullDim, TensorProduct`, and `rg` in the local
   library and pinned Mathlib dimension files. No existing proved theorem gives a
   shorter closure of this statement. The upstream scalar-extension theorem is
   also still open and does not eliminate the affine-cover argument. All three
   proof imports are used; both public imports are needed by the statement.
   Checked every old `proof_deps`: none is omitted from the route, so the pruning
   list is complete. The unit record's realized lists are empty, and its first
   step (base change remains a curve) retains this dimension argument. Pass.
   The literature `_section.md` is not present on this machine; the unit record
   supplies its complete statement and steps.
5. Opened `base-change-dimension.json` and the Lean/Mathlib records of all its
   dependencies. The three proof steps match the empty/nonempty split, affine
   pullback charts, tensor-product dimension equality and supremum comparison.
   Its `proof_deps` and `proof_origin` remain accurate; no node edit is needed.
   Pass.

Second reading changed only this report: added the independent review and
verification evidence. No repair of Lean, imports, statements or nodes was needed.
