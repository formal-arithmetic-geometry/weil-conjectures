## What changed

The original theorem `AlgebraicGeometry.Scheme.punctured_root_limit_presentation`
now has a complete Lean proof from two auxiliary declarations, with its signature unchanged.
Its two new imports are proof-only imports. The original three-step route is retained.

`PuncturedRootLimitCone` proves `AlgebraicGeometry.Scheme.pointed_etale_ring_colimit`
from the existing strict-henselization construction and structural-map characterization.
It constructs the natural base-ring maps, proves their colimit compatibility, and constructs
each point over y by transporting the zero prime of Omega through the neighbourhood lift.
No data definition or arbitrary unproved existence witness was added.

`PuncturedRootLimitPunctures` states the remaining general continuity calculation for any
cofiltered ring-colimit diagram over R. It has no strict-henselization, geometric-point or
etaleness hypothesis or conclusion. The main theorem combines this calculation with the
proved pointed presentation and explicitly supplies each etale map and point over y.

All three modules compile individually in dependency order via lcompile.py with no warnings.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.punctured_root_limit_presentation`.
Fully proved the new helper `AlgebraicGeometry.Scheme.pointed_etale_ring_colimit`
(node `lem-sbc-pointed-etale-ring-colimit`).

One new hole remains:
`AlgebraicGeometry.Scheme.punctured_root_colimit_continuity`
(node `lem-sbc-punctured-root-colimit-continuity`). This is a decomposition with net zero
holes: the pointed-neighbourhood and base-map layer is proved; the general quotient,
localization and affine-spectrum continuity calculation remains. The remaining theorem
is strictly part of the argument and does not assert etale pointed neighbourhoods.
Its docstring contains the construction, universal-property argument, compatibility
calculation and edge cases n=0, f=0 and zero localized rings.

## No longer needed

None of the original imports or original dependency nodes is pruned globally.
Their roles are localized: the pointed presentation uses the strict-henselization and
structural-map declarations, while the remaining continuity node uses category colimits,
affine spectra and the Spec-of-colimit limit result. No extra planned branch is imported.
Removed the unused AdjoinRoot import from the pointed-presentation auxiliary module,
and the unused strict-henselization and etale imports from the continuity auxiliary module.
These were development imports only and were never part of the original target module.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the original statement or route was found. The second step,
labelled elementary in the DAG, still needs a substantial formal universal-property
calculation for quotients and localization. Its ring-colimit inputs are now explicit.
LeanSearch returned Internal Server Error; LeanFinder, Loogle and source searches were used.
The local Stacks tex paths were absent, so the cited Stacks pages were read online.
No source checkout, target statement, definition, or held consumer module was changed.

## New nodes

`lem-sbc-pointed-etale-ring-colimit` records the fully proved first step, in
`lean/Sheaf/AlgebraicGeometry/Morphisms/PuncturedRootLimitCone.lean`.

`lem-sbc-punctured-root-colimit-continuity` records the remaining general continuity step,
in `lean/Sheaf/AlgebraicGeometry/Morphisms/PuncturedRootLimitPunctures.lean`.
Both nodes inherit the original chapter and unit, and retain the original unit route.
No change record is required: existing signatures and public imports are unchanged.

## Second reading by Y3

1. **Visible changes and statements.** Compared the delivered presentation module with the repository version. The original theorem signature is byte-for-byte unchanged; only two proof-only imports and the proof body were added. The two auxiliary modules are new declarations with their statements recorded verbatim in their DAG nodes. No target, definition, or existing declaration interface was changed.

2. **Compilation and axioms.** Compiled all three modules with `lcompile.py --all`; they compile cleanly. The proved declarations `pointed_etale_ring_colimit` and `punctured_root_limit_presentation` use only `propext`, `Classical.choice`, and `Quot.sound`. The one intentionally open declaration is exactly `punctured_root_colimit_continuity`, with its documented `sorry` and matching split node; no forbidden declarations or hollow definitions occur.

3. **Split-off statements.** Checked that `punctured_root_colimit_continuity` is a genuine lower-level continuity statement: it removes strict-henselization, etaleness, and geometric-point assumptions and supplies precisely the root-chart limit and stage comparison needed by the target. Its docstring gives the quotient/localization universal-property construction and the n=0, f=0, and zero-localization cases. `pointed_etale_ring_colimit` is fully proved and is not a restatement of the target. Searches and repository grep found no existing equivalent declarations.

4. **Route and pruning.** The target follows the recorded three-step unit route: pointed etale ring colimit, root-chart continuity, then assembly. The proof-only imports are minimal for the new proof; the removed development imports are documented in the preceding section. Existing proof dependencies remain represented in the DAG, and both new nodes have proof steps, origins, and matching Lean records.

5. **DAG agreement.** Verified that the node proof descriptions and `proof_deps` match the declarations actually used. The target node records the two auxiliary steps, while the continuity node records the remaining open calculation. The unit and chapter fields are preserved. Verdict: accepted after the changes below.

Changed nothing in the proof after this review; restored the source files after temporary axiom probes. The only review artifact added is this section.
