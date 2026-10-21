## What changed

Filled the remaining scalar-extension and coherence proofs in
`Sheaf.Paper.FiniteStagePairCategory`. Completed coefficient maps are identified
with the existing scalar-extension maps at the canonical small fields. The
existing integral/rational extension construction supplies the factorization;
localization gives literal uniqueness and lifts the associator. Ordinary tensor
units follow from adjoint uniqueness, derived units from the universal derived
counit. Restriction coherence and the mates correspondence prove the pentagon
and unit equations, which full integral inclusions and rationalization preserve.

All existing public signatures, attributes, public imports and non-theorem bodies
are unchanged. New helpers are private and proved; the new imports are private
proof imports. Three comparison definitions stay locally irreducible during
the rational coherence proofs; their normalization lemmas expose exactly the
needed equations, and private unit helpers unfold the choices explicitly.
This avoids repeated expansion of nested chosen witnesses. The DAG copy records
the dependencies of these proofs. No other
Lean module is changed. The scoped elaboration commands and consumer inventory
are recorded in `coord/changes/H8-finite-stage-scalar-proofs.md`.

## Proved and sorry left

Original holes closed (all in `AlgebraicGeometry.Scheme`, node
`def-weil-pbc-finite-stage-pair-category`):

- `pbcAmbientScalarExtension_preserves`.
- `pbcRationalScalarExtension_exists`.
- `pbcOrdinaryScalarUnit_exists`.
- `pbcAmbientScalarUnit_exists`.
- `pbcScalarAssociator_exists`.
- `pbcScalarAssociator_cocycle`.
- `pbcScalarSystem_units`.
- `pbcScalarExtension_additive`.

Eight original holes closed; zero holes added; zero split off; zero holes remain
in the item. Previously completed proofs, including the common-stage
preadditive construction, remain intact. The proofs use existing declarations
of the recorded dependencies, including scalar-transport statements that are
still separate stage-3 items; this delivery introduces no additional assumptions.

Validation: after the resumed delivery exceeded the 60-second compile limit,
keeping the chosen comparisons folded reduced elaboration time. The complete
revised file compiled cleanly through `lcompile.py` in 44.4 seconds (exit code 0,
no warnings). Static comparison against current shared sources confirms every
original declaration header is unchanged, the original eight holes are closed,
and no line exceeds 100 characters. Only the permitted DAG fields `proof`,
`proof_deps`, and `proof_origin` change. The delivery tool performs the final
compile and axiom checks before pushing.

## No longer needed

None of the original public imports, statement dependencies, or modules is
withdrawn. The existing scalar-extension theorem supplies the preservation and
rational construction, so their longer direct tensor/tower arguments need not
be repeated here; their existing dependencies remain needed by that theorem.
The generic exact-functor associativity helper imported from
`SuccessiveDerivedQuotientNormalization` is used only as categorical coherence,
not as the integral-model theorem realized by that module. The blueprint unit's
own statement and proof steps are preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was needed. The definition node had no proof
steps for the scalar-extension existence and coherence theorems contained in
its Lean module; the delivery records the actual proof route in that node.
The raw localization's universal property is needed for literal functor
uniqueness, including the object function. The identity coefficient field and
all repeated-field cases use the existing literal-identity branches and their
specified tensor-unit comparisons. The proof also covers the empty scheme.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
