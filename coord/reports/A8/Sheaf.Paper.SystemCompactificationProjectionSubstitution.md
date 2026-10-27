## What changed

Proved `WeilConjectures.SystemTensorMate.refinementDirectId_existsUnique` in
`Sheaf.Paper.SystemCompactificationProjectionSubstitution`, preserving every existing
signature, definition, public import, and docstring. The identity base-change graph induces
a comparison of ordinary module pushforwards. The constant-section characterization of
`coefficient` identifies its structural ring map, the graph inverse gives the inverse
comparison, and extensionality on all component sections proves uniqueness.

The proof uses the actual sheaf-module pushforward comparison API, rather than selecting
an unspecified isomorphism. All temporary data are constructed from existing maps and
proved equalities. There are no new declarations, nodes, definitions, or holes.

## Proved and sorry left

Closed one of the item's four holes:

- `WeilConjectures.SystemTensorMate.refinementDirectId_existsUnique`.

The following three existing holes remain unchanged, all attached to
`lem-pur-system-compactification-pf-substitution`:

- `WeilConjectures.SystemTensorMate.refinementGamma_isIso`.
- `WeilConjectures.SystemTensorMate.system_compactification_pf_substitution`.
- `WeilConjectures.SystemTensorMate.system_compactification_refinement_coherence`.

Added zero holes. This is a partial proof delivery, not a decomposition.

Validation: the complete item module compiled through `lcompile.py` with exit code 0
in 11.7 seconds. The file has no lines over 100 characters. A source comparison confirms
that only the body of the identity theorem changed.

## No longer needed

None. No module or node is withdrawn. The existing imports and the planned dependencies
for the three unchanged statements are retained; the identity proof adds no imports.

## Where the brief, the DAG or earlier work was wrong

No statement change or disputed statement. The existing
`VaryingRing.modulePId_existsUnique` gives the same identity section formula in the general
varying-ring presentation. The item uses its own `coefficient` choice; the proof therefore
establishes the needed constant-section equality directly and uses
`SheafOfModules.pushforwardNatIso`, `pushforwardCongr`, and `pushforwardId`.

The declared constructible-domain theorem uses `E : Type u` together with a different
system presentation, while this item uses `E : Type (u + 1)` and arbitrary universal
`TensorOperations`. Its invertibility, tensor-domain, and pasting conclusions cannot be
applied to the three remaining statements without additional presentation and normalization
arguments. No unsupported identification or evaluation-faithfulness assumption was used.

Searches run through `msearch.py`: LeanFinder for the identity direct image, Loogle for
`Functor.map_comp`, and grep for `pullbackId`. LeanFinder found the continuous sheaf
identity and module-pushforward identity APIs; Loogle reported the unqualified name unknown;
grep found the relevant pullback-identity constructions. Local searches located the proved
general varying-ring identity and the existing inverse-mate comparison theorem. The unit
route and all remaining DAG dependencies are preserved.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
