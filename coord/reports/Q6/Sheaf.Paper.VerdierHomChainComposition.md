## What changed

Replaced the sole hole in `VerdierHomChainComposition.lean`,
`WeilConjectures.VerdierHomChainComposition.identity_exchange`, with the
five-transposition identity calculation. The public statement and all existing
public definitions are unchanged. The stage-comparison section
locally restores normal transparency checking to avoid expanding coefficient
category constructions during elaboration; no existing definition body changes.

The proof first identifies the two closed presentations. A proved generic
adjunction lemma expresses inverse transposition through the unique identity
mate. A proved closed-category calculation gives naturality of left-tensor
transposition in its contravariant factor. Applying these to the reverse Hom
chain reduces it to the identity projection triangle. The proof then evaluates
the chain on the forward representative, cancels the support isomorphism in the
contravariant Hom factor, and uses naturality of the ordinary identity mate to
obtain the displayed epsilon equation.

The identity projection triangle is isolated in the new module
`Sheaf.Paper.VerdierIdentityProjection`. This is a decomposition: the remaining
statement concerns only the prescribed pullback unit, its ordinary/proper mate,
and the tensor projection. It has no internal-Hom transpose, exceptional
adjunction, dualizing map, or Verdier exchange conclusion. Its existence witness
is used only inside a theorem proof, not to define data.

Updated the parent node's identity proof step and proof dependencies, and added
the node for this projection calculation. No source-library file, target,
existing statement, or existing definition was changed.

## Proved and sorry left

Closed the item module's one original hole:

- `WeilConjectures.VerdierHomChainComposition.identity_exchange`.

Added one strictly smaller hole, in its own module:

- `WeilConjectures.VerdierHomChainComposition.normalized_identity_projection`.

There are zero holes left in the item module and one in the added module.
This is one decomposition, with one upper hole closed and one lower hole added;
it is not a net reduction in holes or a claim of an axiom-free identity theorem.
All new private helpers are proved.

## No longer needed

None. All original imports remain used by the other composition and coefficient
proofs. No original dependency, module, node, unit statement, or unit proof step
is withdrawn. The new projection theorem is imported privately because only the
identity proof uses it.

## Where the brief, the DAG or earlier work was wrong

The identity argument needs a tensor projection normalization at the operation
datum interface. The library's `sixFunctorProjection_identity` has the analogous
ambient conclusion for a full `SixFunctorDatum`; this item supplies only
`SixFunctorOperationDatum`, from which the additional full-datum fields cannot
be obtained. Consequently that existing theorem cannot directly close this
step. The new statement records the operation-only restricted calculation from
the identity paragraph of the projection-coherence blueprint and the parent
node's identity proof step. Its docstring and node give the proof in words,
including the integral and field-stage transport and degenerate inputs.

No existing statement is disputed, weakened, or repaired. The remaining
projection proof is recorded explicitly rather than assuming a new arbitrary
identity comparison for exceptional inverse image or compact support.

## New nodes

- `lem-sf-verdier-identity-projection`, realized by
  `Sheaf.Paper.VerdierIdentityProjection` and its theorem
  `normalized_identity_projection`. Source: the current projection-coherence
  blueprint's identity calculation and step 5 of the parent node. Mathlib
  leansearch, loogle, and grep searches found generic adjunction identities but
  no theorem for the specified restricted projection triangle.

## Second reading by Q6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
