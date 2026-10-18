## What changed

Proved `stonean_cover` in `Sheaf.Topology.StoneanCover`, preserving its complete signature,
universes, visibility, definitions and imports. The compact Hausdorff structure, clopen sets,
density and continuous extension come from the pinned Mathlib ultrafilter API. To obtain
projectivity, lift the map on principal ultrafilters using a right inverse of the given
surjection, extend that lift continuously, and use density to prove the factorization.
Apply the existing Gleason equivalence and its total-disconnectedness consequence.
`ultrafilter_extend_eq_iff` identifies the actual extension with the unique ultrafilter limit.
The explicit preimage `pure t` proves surjectivity, including the empty-space case.

Updated the proof and proof origin of `det-pe-stonean-cover` to this shorter argument.
The unit still uses the discrete ultrafilter cover and the Gleason characterization.
No statement, definition, consumer or public import changed.

Searches through `msearch.py`: LeanFinder for the ultrafilter Stonean cover returned
`CompHaus.projective_ultrafilter` and the Gleason directions; Loogle for
`"ultrafilter_extend"` returned the continuous-extension, principal-value and limit-characterization
lemmas; grep found the corresponding declarations and `denseRange_pure`. Read their pinned
Mathlib source signatures. The categorical projectivity proof supplied the short elementary
lifting argument, expressed directly in `CompactT2.Projective` to avoid category conversions.

## Proved and sorry left

Closed the original hole in `stonean_cover` (node `det-pe-stonean-cover`): 1 of 1.
No holes added or split off. No `sorry` remains in the delivered Lean module.

The complete statement compiles through `lcompile.py`; the required delivery preflight also
checks declaration signatures and axioms. No hidden choices of objects or changed definitions
were introduced: the local lift is constructed from a right inverse of the surjection
hypothesis and the existing explicit ultrafilter extension.

## No longer needed

No imports, nodes or modules pruned: both existing imports are used, and all three declared
proof dependencies remain used. The explicit open-union closure computation and separate
neighborhood uniqueness calculation in the original proof plan are replaced by the shorter
lifting argument and Mathlib's `ultrafilter_extend_eq_iff`, respectively. Neither replacement
removes a unit or one of its required constructions.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition found. The planned long closure computation is unnecessary
because projectivity can be proved directly from the already declared continuous-extension
input and then converted to extremal disconnectedness using the declared Gleason theorem.
The existing declaration docstring is retained as the original seven-step proof plan; the
inline proof comment and updated node record describe the shorter implemented route.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
