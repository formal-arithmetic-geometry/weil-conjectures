## What changed

Decompose `WeilConjectures.VerdierHomChainComposition.verdier_hom_chain_composition`
by explicitly pasting the reverse Hom chains. The ordinary/tensor transpose calculation
is proved in `Sheaf.Paper.VerdierOrdinaryTensorTransport`. The remaining
projection/exceptional calculation is stated for an arbitrary arrow before the ordinary
transposes in `Sheaf.Paper.VerdierProjectionExceptionalPaste`. This statement has no
ordinary adjunction transposes, chain input, forward-chain inverse, or Verdier conclusion;
it is strictly a part of the argument, not the original theorem under another name.

The main proof combines the calculations, uses the existing test naturality of the
reverse chain to cancel the shared tensor-Hom adjunction on Y, and cancels the direct
image of the f exchange isomorphism. A separate proved private helper derives the
Verdier equation from ChainComposition by the identity test, second-variable naturality,
and naturality of the direct compositor. Generic proved private helpers handle the
isomorphism cancellation and this naturality paste. All existing statement signatures
stay identical.

Move the canonical coordinate definitions, with identical names, signatures and bodies,
to `Sheaf.Paper.VerdierHomChainCompositionData`; the item publicly reexports them.
This makes the two intermediate calculations independent of their consumer without
an import cycle. The new tensorCoordinate is an equality isomorphism only.
See `coord/changes/N3-verdier-hom-composition-coordinates.md`.

The original representing_chain, chain_naturality, stage_specialization,
coefficient_transposes and composition_after_change proofs are retained.
No adopted source module or target statement is edited.

## Proved and sorry left

Original item: two holes.

Validation: the data module, ordinary transport, projection-paste statement and
main item all compile through lcompile.py. The main proof's successful check took
42.0 seconds. The resulting one-line whitespace linter warning is corrected in
the delivered source; deliver3.py performs the final compile and axiom checks.

Closed by decomposition:
`WeilConjectures.VerdierHomChainComposition.verdier_hom_chain_composition`
(node `lem-sf-verdier-hom-chain-composition`). Its assembly proof contains no sorry.

Proved without new holes:
`WeilConjectures.VerdierHomChainComposition.ordinary_tensor_transport`
(node `lem-sf-verdier-ordinary-tensor-transport`), including its two private
adjunction-uniqueness and shared-tensor helpers. This calculation needs no geometric
admissibility or separatedness assumptions beyond the supplied restricted data.

One original hole remains unchanged:
`WeilConjectures.VerdierHomChainComposition.identity_exchange`
(node `lem-sf-verdier-hom-chain-composition`).

One new hole:
`WeilConjectures.VerdierHomChainComposition.projection_exceptional_paste`
(node `lem-sf-verdier-projection-exceptional-paste`). Its source and complete proof
in words are in the module docstring and DAG node. The stated calculation handles
both exceptional counits and projection associativity, but omits the two ordinary
transposes and the tensor transpose on X that ordinary_tensor_transport handles.

Thus one of two original holes is reduced to one smaller obligation; one hole is
added, and two holes remain across the packet. This is a decomposition, with zero
net hole reduction, not a complete proof of geometric composition or the identity law.

## No longer needed

No original public import is removed from the item. Its existing private coefficient
proof import remains necessary. No module is withdrawn or claimed globally pruned.

The moved data needs only PodHomChainCounitFormula and CoefficientGammaRepresentatives
as direct public imports. Its earlier redundant public imports of SixFunctorOperationDatum,
ExceptionalAdjointAdmissibility, TensorAdjunctionExchange, CompactSupportProjectionFormula,
AdmissibleVerdierExchange, VerdierExchangeData and PodCtfPairingMaps are supplied through
these two imports; the item's original public imports still expose the same public API.

No ConstructibleExceptionalCompositor theorem import is needed for the new local proof:
its exact restricted exceptional compositor is defined by rightAdjointUniq, and the
new projection paste uses its defining mate equation. No global compositor node is
withdrawn: it remains cited by the open identity/coefficient plan where appropriate.
The formal part of the new proof does not need another finite-Tor domain existence
lemma: every intermediate object already has the required full-subcategory type.
The existing node dependencies for the still-open identity calculation are retained.

## Where the brief, the DAG or earlier work was wrong

The earlier proof plan described the correct mathematical reduction but had not exposed
the two calculations as independently typed Lean statements. The supplied canonical
restricted compositors permit the ordinary/tensor transport proof directly from
Mathlib adjunction uniqueness and naturality; no separate geometric compositor package
is required for that formal part. The projection/counit paste remains explicit work.

There is no statement correction in this delivery. In particular the previous
stage_specialization naturality repair is preserved. The unit route is unchanged:
projection composition and adjoint mates give Verdier composition.

## New nodes

`def-sf-verdier-hom-composition-coordinates` records the moved canonical data and
the equality tensorCoordinate. No data is chosen from a theorem of mere existence.

`lem-sf-verdier-ordinary-tensor-transport` is the proved ordinary/tensor inverse
transpose calculation, using the canonical source coordinate and exceptional mate.

`lem-sf-verdier-projection-exceptional-paste` is the remaining projection and exceptional
inverse-transpose calculation on an arbitrary b, before ordinary transposition. Its
proof uncurries on Z, uses the exceptional compositor counit equation and the projection
composition equation, then cancels the specified tensor comparison isomorphisms.

Change record: `coord/changes/N3-verdier-hom-composition-coordinates.md`.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
