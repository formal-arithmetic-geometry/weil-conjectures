## What changed

Replaced the sorry in `RingTheory.dvr_abhyankar_normalized_factor_ramificationIdx_eq_one`
with a complete Lean reduction, preserving its signature and public imports.
Added proof-only imports of `Mathlib.FieldTheory.PurelyInseparable.Basic`,
`Sheaf.RingTheory.DvrNormalizedCompositumLocalDiagram` and the new
`Sheaf.RingTheory.DvrAbhyankarLocalMaximalIdeal`.

The proof constructs the tensor-quotient maps, proves compatibility and generation,
derives faithfulness and local tameness, applies the existing proved normalization
local-diagram theorem, and translates maximal-ideal equality into the required
length-one conclusion. The private separability helper is reused from
`DvrTameTensorFactorResidueSeparable`; the private length helper is proved here.
No definition, existing signature, visibility or target was changed.

Both delivered modules compile with the default heartbeat limits. Extracting the
short general length calculation into a proved private helper avoided elaborating
it in the large local-field context. The wall-clock compile limit was unchanged.

## Proved and sorry left

Closed the original hole in
`RingTheory.dvr_abhyankar_normalized_factor_ramificationIdx_eq_one`
(node `lem-sbc-dvr-abhyankar-normalized-factor-index-one`).
There are no sorries left in the assigned module.

Added one hole in `RingTheory.dvr_abhyankar_local_map_maximalIdeal`
(node `lem-sbc-dvr-abhyankar-local-maximal-ideal`), in its own new module.
This is a decomposition: one hole closed, one added, net zero. The remaining
statement concerns an already supplied local DVR compositum diagram, not tensor
quotients, normalization construction, global prime bounds or the length index.
The parent proves all those reductions and the final combination in Lean.

The new statement was checked mathematically on e=1 and n=1, on the identity
base change, and in positive residue characteristic. The unit hypothesis rules
out e=0. The base index n may be divisible by the residue characteristic;
only the tame index e is required to be a unit. Generation of F excludes adding
an unrelated ramified field extension. Both local-map conditions and the common
fraction fields are retained to identify the selected normalization local ring.

## No longer needed

No existing imports were removed: all original public imports support the
unchanged statement. No existing DAG proof dependency was pruned (the old list
was empty), and no module is claimed to leave the targets' closure.

The proof does not use `Sheaf.RingTheory.DvrTameTensorFactorRamificationBound`,
`Sheaf.RingTheory.DvrTameTensorFactorMaximalIdeal`,
`Sheaf.RingTheory.DvrTameTensorFactorUnramified`,
`Sheaf.RingTheory.DvrTameTensorFactorResidueSeparable` or
`Sheaf.RingTheory.DvrAbhyankarLocalResidue`. In particular, using the quantitative
bound here would be circular: that bound already imports this item.
These are not claimed as globally pruned nodes or modules.

## Where the brief, the DAG or earlier work was wrong

The original node's three non-elementary proof steps had no proof dependencies,
so its claim to be split did not expose the source Abhyankar calculation as a
separate Lean input. The updated node records the existing local-diagram theorem
and the new local maximal-ideal theorem. The unit's trait-case route is retained.

LeanSearch returned Internal Server Error; LeanFinder, Loogle and source searches
worked. None supplied a noncircular formalized local Abhyankar index-one theorem.
The source statements and proof were checked at Stacks Tags 0BRM, 09EM and 09E7.

## New nodes

`lem-sbc-dvr-abhyankar-local-maximal-ideal` states the maximal-ideal conclusion
of Stacks 0BRM and 09E7 for a compatible local DVR compositum diagram, parallel
to the existing local residue-separability theorem. Its docstring and DAG carry
the unit-root reduction, normalized base-change and etale descent argument.
Searches found no existing theorem proving this conclusion without a cycle.
There are no change records or forced adaptations.

## Second reading by R4

1. **Interfaces: PASS.** Read the complete diff against the repository module.
   The existing theorem signature is byte for byte identical (also checked by
   extraction), with its docstring, visibility and all public imports unchanged.
   The added imports are proof-only. No definitions or existing statements change;
   no change record or forced adaptation is needed.
2. **Lean proof and axioms: PASS as a decomposition.** Both delivered modules
   compiled through lcompile.py --all, in dependency order, without errors or
   warnings. A scratch copy with #print axioms checked both private helpers,
   the main theorem, the local-diagram theorem and the new local theorem.
   The helpers and local diagram use only propext, Classical.choice and
   Quot.sound. The main theorem and new local theorem additionally use sorryAx,
   exactly as expected from the one reported new hole. The only delivered sorry
   is the named dvr_abhyankar_local_map_maximalIdeal theorem. No prohibited
   declarations/options or data chosen from an unproved existence theorem occur.
   The diagram witnesses destructured in the proof come from the proved theorem.
3. **Split-off statement: PASS.** Read the new module, its verbatim node signature,
   docstring argument, and Stacks Tags [0BRM](https://stacks.math.columbia.edu/tag/0BRM),
   [09EM](https://stacks.math.columbia.edu/tag/09EM),
   [09E7](https://stacks.math.columbia.edu/tag/09E7) and
   [09EQ](https://stacks.math.columbia.edu/tag/09EQ). The field generation and
   compatible fraction-field maps identify the compositum factor; the local maps
   select its valuation center. A and U embed in F: compatibility embeds B,
   integrality of A/B eliminates a nonzero kernel on A, and the U fraction-field
   map is injective. The normalization localized at this center equals T because
   a proper overring of a DVR in its fraction field is a field, whereas T is a DVR.
   Thus the source cancellation argument applies. Checked e=1 (already weakly
   unramified), n=1 (forces e=1), identity base change, and residue characteristic
   dividing n but not e. IsUnit excludes e=0; separability is retained; generation
   excludes an unrelated extra ramified extension of F. This is strictly smaller
   than the original tensor-quotient/normalization/length assertion, not its renaming.
   Repeated LeanFinder with a different maximal-ideal/base-change query, Loogle
   with the unit-degree separability pattern, and source searches for
   map_maximalIdeal and ramificationIdx_eq_one. No noncircular cancellation lemma
   was found. The residue-only local theorem does not imply the new conclusion.
   Closing this source theorem requires the substantial Abhyankar root/descent
   calculation; no short proof was found.
4. **Route and pruning: PASS.** Read the proof top down: tensor compatibility and
   generation, degree-unit separability, the existing proved local diagram, the
   one local Abhyankar input, then the proved length-one translation. Every added
   proof import is used. The original public imports preserve the existing API.
   The old proof_deps list was empty, so no old dependency is omitted from
   No longer needed. The tensor-factor maximal-ideal and unramified results
   depend on the quantitative bound, which imports this item, hence cannot
   replace the local input. The trait-case route of sk-prop-input-spreading stays.
   Its realized lists are already empty in the repository; this delivery neither
   changes nor bypasses a realized step, and does not claim to repair that
   pre-existing blueprint bookkeeping gap.
5. **DAG: PASS.** The only changed fields of the existing node are proof,
   proof_deps and proof_origin. Its two proof dependencies match the actual calls.
   Read every field of the new node: source, natural-language proof steps,
   statement dependencies, search records, origin, created, blueprint, chapter,
   unit and Lean record are present. The recorded Lean signature matches the
   new declaration verbatim. The new hole is listed by name and node in
   Proved and sorry left; the net hole reduction is zero.

Second reading changed only this report, recording the independent checks,
additional searches and the pre-existing empty unit realized lists. No Lean or
DAG repair was necessary; the valid reduction is retained unchanged.
