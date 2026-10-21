## What changed

Filled the four construction proofs in `Sheaf.Paper.SfDerivedDirectImage`, preserving every
public declaration type, definition body, public import and original docstring.
The derived normalization supplies explicit source and target arguments to the same complex
map; these are its existing inferred endpoints, with no change in the elaborated statement.

The completed coefficient map is the limit lift of the natural constant-section coefficient
maps. The fully faithful forgetful functor to ring sheaves retains commutativity. Additivity
is sectionwise. The ordinary restriction comparison consists of identity linear maps, whose
linearity follows from the completed map's projection equation.

For the derived comparison, proved private helpers transport scalar restriction and completed
direct image to the existing small ringed-topos models. The resolution clause of the proved
ringed-topos composition theorem supplies the necessary quasi-isomorphism. A generic proved
private helper then compares the two total right derived functors of the ordinary square,
derives the exact requested resolution normalization, and proves uniqueness by cancellation
on K-injective representatives and naturality. This does not assume that scalar restriction
preserves K-injectives or that inverse image preserves the completed coefficient ring.

Added private proof imports for the existing ringed coefficient-change proof helpers,
continuous and restriction ringed-topos module constructions, and composition with an exact
derived functor. Updated the owning node's proof, proof dependencies and proof origin to
record these arguments. Local irreducibility attributes keep `constantSheaf` and
`completedIntegralCoefficientSheafUnrestricted` and `proEtaleConstantModuleDirectImage`
behind their APIs in the remaining proofs;
this avoids unnecessary unfolding of the limit and sheafification choices. There are no
adapted consumers or definition changes. The explicit endpoint annotation is documented
in `coord/changes/sf-derived-restriction-map-endpoints.md`, as requested by preflight;
its elaborated mathematical statement is unchanged. The downstream declaration-use search
finds only the item module, whose existing chosen-comparison definition compiles unchanged.

Validation: the final complete module compiled cleanly through `lcompile.py` in 38.9 seconds
with all four proofs present. The small-site equivalence instance is proved once from
Mathlib's pushforward equivalence, avoiding repeated unfolding of its construction.
The delivery compilation gates passed; preflight requested the endpoint-annotation change
record. Delivery reruns the final compilation, statement and axiom checks.

## Proved and sorry left

Closed all four original holes, attached to `def-weil-derived-direct-image`:

- `WeilConjectures.sfCompletedCoefficientMap_existsUnique`.
- `WeilConjectures.sfCompletedModuleDirectImage_additive`.
- `WeilConjectures.sfDirectImageRestrictionComparison_existsUnique`.
- `WeilConjectures.sfDerivedRestrictionComparison_existsUnique`.

Holes added: zero. Holes remaining in the item: zero. No results were split off.
All newly added private helpers are proved.

## No longer needed

None. Both existing public imports are used by the unchanged public constructions. The node
originally had no proof steps or proof dependencies to prune. The previously stated notions
and the unit's ambient direct-image construction remain in place; no module is withdrawn and
no source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The owning definition node had an empty proof
plan despite the four auxiliary construction holes; the updated proof now records their
actual arguments. The existing ring-sheaf restriction comparison assumes invertible
inverse-image coefficient identifications, so it cannot be applied directly to the completed
structural map supplied here. Its general small-model composition argument applies without
that additional assumption and is the route used in this delivery.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
