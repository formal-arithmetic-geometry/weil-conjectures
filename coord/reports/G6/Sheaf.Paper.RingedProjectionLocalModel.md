## What changed

Replaced the sorry body of
`AlgebraicGeometry.Scheme.ProjectionRestriction.localModel_exists` by a reduction
with its original signature. Added proof imports of
`Sheaf.Paper.RingedProjectionLocalData` and
`Sheaf.Paper.RingedProjectionLocalTensorSquare`.

The item proves two private helpers, `projection_eq` and `projection_square`.
The latter is a categorical proof for arbitrary categories, four tensor functors,
a pullback square and a direct-image comparison satisfying the counit mate law.
It transposes the two projection paths under the local adjunction, uses tensor
coherence and naturality, then cancels the pullback comparison with its inverse.
Specializing it to the supplied normalized local data proves precisely the
existing `Local.ProjectionCompatible` equation, including the specified source
and target isomorphisms.

Two new modules isolate the remaining geometric work. `localData_exists`
constructs the normalized local operations and comparisons without any projection
condition. `localTensorSquare` states the tensor coherence equation for an
already supplied Local datum, before inserting a direct-image input or taking
any projection mate. Neither theorem restates the original existence of a
projection-compatible package. Their combination requires the proved adjunction
calculation in the item module.

No existing statement, definition, public import or source-library file changes.
The original node now records these two prerequisites and the proved formal
mate calculation. Each new theorem has its own node and a complete proof in
words.

## Proved and sorry left

Closed original hole:
`AlgebraicGeometry.Scheme.ProjectionRestriction.localModel_exists`
(node `lem-weil-pbc-ringed-projection-local-model`). The item module has zero
remaining sorry bodies. The proved private categorical helpers have no holes.

Added holes, each in its own module:

- `AlgebraicGeometry.Scheme.ProjectionRestriction.localData_exists`, in
  `Sheaf.Paper.RingedProjectionLocalData`, node
  `lem-weil-pbc-ringed-projection-local-data`.
- `AlgebraicGeometry.Scheme.ProjectionRestriction.localTensorSquare`, in
  `Sheaf.Paper.RingedProjectionLocalTensorSquare`, node
  `lem-weil-pbc-ringed-projection-local-tensor-square`.

This is a decomposition: one old hole closed, two strictly smaller obligations
added, net minus one in the hole ledger. It is not an unconditional proof of the
original theorem. There are no sorry bodies in definitions and no data chosen
from these existence theorems in a definition.

Validation: lcompile.py compiled the two new prerequisites in import order
(localData_exists: 4.3 seconds initially, localTensorSquare: 3.6 seconds after
making the stored additivity instances explicit). The final item compiled cleanly
in 5.2 seconds. The final main proof explicitly normalizes composed functor
objects and the inverse of the symmetric pullback isomorphism. All files are
under the 60-second limit. A source-only traversal checked all 739 nodes reachable
from the revised item without finding a dependency cycle; node attachments and
the unions of step dependencies agree. The generic combining lemma uses no
nonstandard axioms. The two named holes remain explicit prerequisites of the
public result. deliver3.py runs the final compile and packet preflight.

## No longer needed

No existing Lean import was removed, and no existing module is withdrawn.
The generic `lem-weil-pbc-ringed-exchange-tensor-coherence` theorem and its module
`Sheaf.Paper.RingedExchangeTensorCoherence` are no longer proof dependencies of
this item: its formal categorical calculation is proved directly for the actual
package functors, avoiding conversion to a separate ringed-tensor-edge interface.
This does not claim that the generic theorem is unused elsewhere.

The other six former proof dependencies are still needed below the two new
construction and tensor-square nodes; they are not claimed as pruned. The new
square node uses the existing representative tensor-square theorem and cochain
tensor rigidity for its proposed geometric proof. All delivered imports are
needed by statements or proofs.

## Where the brief, the DAG or earlier work was wrong

The planned route is mathematically appropriate, but its declarations do not
immediately fill the fields of Local. The generic slice declarations use one
small site universe, whereas this package uses pro-etale objects in Type (u+1)
and morphisms in Type u. Its TensorModel, exact Operation and representative
normalizations also differ from the generic RingedTensorCorner/Edge
presentation. The new obligations preserve the actual universes and all
normalization fields instead of assuming definitional equality of these
interfaces. The formal counit-mate step itself does not require either generic
ringed-site presentation.

The new statements were checked on identity functors and identity squares,
zero input and zero coefficient cases, and arbitrary unbounded inputs. The
local-data statement omits only the separate projection condition; the tensor
square is the canonical pure-tensor equality, with unchanged bidegrees and
therefore no extra sign. The combining proof is valid for arbitrary categories
and imposes no additional geometric, boundedness or nonzero assumptions.
The unit and chapter routes are unchanged.

## New nodes

`lem-weil-pbc-ringed-projection-local-data` records construction steps 1--3 of the
original plan: the localized operations, derived square and mate law, tensor
models and their shift normalizations. It is realized by
`lean/Sheaf/Paper/RingedProjectionLocalData.lean`.

`lem-weil-pbc-ringed-projection-local-tensor-square` records only the tensor
square used in step 4 before the formal projection-mate calculation. It applies
to an already supplied Local datum and is realized by
`lean/Sheaf/Paper/RingedProjectionLocalTensorSquare.lean`. Its source proof uses
ordinary pure tensors, signed totalization, representative normalization and
faithfulness of descent. It does not assert projection compatibility.

Searches: LeanSearch for derived localized restriction and tensor; Loogle for
`SheafOfModules.overFunctor`; LeanFinder for restriction and projection mates;
Mathlib source searches for ordinary restriction and tensor comparisons; project
and DAG searches for the exact package and square. These found the ordinary
Mathlib functors and the differently presented generic project lemmas, but no
statement matching either new obligation. Whole-blueprint searches for localized
tensor, tensor square and projection restriction found no matching blueprint
node. Search details are retained in each new node. No change record is needed
because no existing definition or statement changed.

The cochain tensor rigidity node `lem-sf-cochain-tensor-model-rigidity` is a
generic tool for faithfulness with an arbitrary derived target category. It is
used below the localized tensor square, where the existing TensorModel.descent
field alone has a fixed target. Any cross-unit tool approval remains for the
maintainer; this delivery adds no tool_uses approval.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
