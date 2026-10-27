## What changed

Proved `WeilConjectures.pullbackTensorBraiding_existsUnique` by conjugating the signed
cochain symmetry with the recorded K-flat tensor comparisons and descending it through
fully faithful restriction to resolving representatives. K-flat resolutions and the
quotient-to-derived comparison provide the required full faithfulness. The representative
square follows by cancellation; faithfulness proves uniqueness.

Reused the existing `CategoryTheory.RingedDerivedNative.complexConstraints` in the signed-total
proof and extracted private helpers for its generator formula, its native natural
isomorphism, and the categorical descent. The native natural isomorphism is constructed
by conjugating the generic braided tensor isomorphism; the existing total-tensor map
identity supplies naturality. Generator uniqueness identifies its components with the
selected signed symmetry in the derived representative square. Local reducibility annotations keep the
chosen intrinsic structures and comparison constructions sealed during proof checking.
All existing signatures, public imports, and data constructions are preserved. Updated the existing node's proof and dependencies. No new public modules.

Removed the unused direct private import
`Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`. No declaration is withdrawn.
The existing public imports still reach that module and `ProjectiveLineGenusZero`;
this packet does not claim to prune either module from the import closure.

Validation: the final item module compiled successfully through `lcompile.py` in 33.6 seconds,
with no diagnostics (result `7791a9bb0e9dd3f3a8717cab`). Delivery repeats the required compiler,
axiom, consumer, and node checks before pushing. The first delivery attempt returned capacity
busy without pushing; the packet is being retried unchanged except for this validation record.

## Proved and sorry left

Original holes: 5. Closed: `WeilConjectures.pullbackTensorBraiding_existsUnique`.
Added holes: 0. Split-off statements: 0.

The following four original holes remain in the item, all attached to
`def-pur-finite-pullback-tensor-comparison`:

- `WeilConjectures.canonicalFinitePullbackTensor_associativity`
- `WeilConjectures.canonicalFinitePullbackTensor_unit`
- `WeilConjectures.canonicalFinitePullbackTensor_composition`
- `WeilConjectures.canonicalFinitePullbackTensor_braiding`

The pre-existing signed-total existence and uniqueness theorem remains proved. The descent
uses the existing declarations for K-flat resolution and resolving-representative
whiskering; no replacement assumption or new hole is introduced.

## No longer needed

Removed the redundant direct private import
`Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`: none of the item's declarations
uses it directly. The retained public import `ProEtaleOpenSquareExchange` still imports
it. `ProjectiveLineGenusZero` also remains reachable through the retained public
`DerivedPullbackTensorHom` import. Consequently zero modules are pruned from the
item's complete import closure. No DAG node or module is withdrawn.

All original node proof dependencies remain needed by the retained proofs. The added
proof dependencies are `lem-sf-ringed-tensor-complex-constraints`, `lem-pc-kflat-resolution`
and `lem-weil-pbc-resolving-representative-whiskering`.

## Where the brief, the DAG or earlier work was wrong

The current rework row quarantines this item because of the transitive
ProjectiveLineGenusZero import. The live item source exists; this packet preserves its
Lean attachment and public API. It removes a redundant direct private import; the
transitive quarantine dependency remains through existing public imports. No upstream
declaration or import has been removed to bypass it.

The braiding descent needs no choice of native derived monoidal structure: it follows
from the binary tensor model alone. The remaining associativity and unit equations
involve the separately chosen intrinsic monoidal constraints. The binary tensor-model
comparison does not itself state their representative normalization; completing those
proofs requires accounting for that additional coherence. Their statements and existing
proof plans are retained.

## Second reading by X6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
