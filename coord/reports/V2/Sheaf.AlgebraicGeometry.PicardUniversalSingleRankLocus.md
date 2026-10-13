## What changed

Completed the proof body of
`AlgebraicGeometry.Scheme.exists_picardUniversalSingleRankLocus` without changing its
signature, visibility, definitions, or original docstring. The proof chooses Mathlib's
standard derived-category localizations, proves stability of the predicate under further
base change by composing tests, obtains a local perfect chart, applies the existing
`exists_perfectLowestCohomologyLocus` with lowest degree zero, composes the chart's
comparison with its factorization criterion, and applies local-immersion gluing.

Added three separate statement modules:
`Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart`,
`Sheaf.AlgebraicGeometry.PicardSingleRankSourceLocal`, and
`Sheaf.AlgebraicGeometry.LocalImmersionLocus`. Each contains one public named theorem,
with a whole-proof `sorry`, source, proof in words, and matching new DAG node. The main
module imports these three and `Sheaf.AlgebraicGeometry.PerfectLowestCohomologyLocus`
privately for its proof. Its six original public imports are preserved.

Updated the original node's proof, proof dependencies, and proof origin to describe
this concrete Lean reduction. No statement or definition changes, forced adaptations,
or change records are needed. The cube unit route is preserved: reference-bundle fibre
rank strata, perfect direct image, Tag 0BDL, and gluing characterized loci.

## Proved and sorry left

Closed the single original direct hole:
`AlgebraicGeometry.Scheme.exists_picardUniversalSingleRankLocus`
(node `lem-sc-picard-universal-single-rank-locus`). Its proof now compiles with no
internal `sorry`. This is a decomposition, not a completed axiom-clean proof of the
mathematical theorem: it adds three strictly smaller independent parts of the argument.

Every new direct hole, and all holes left in the delivered modules:

- `AlgebraicGeometry.Scheme.exists_picardSingleRankPerfectChart`
  (`lem-sc-picard-single-rank-perfect-chart`): constructs and compares a local perfect
  complex; it constructs no representing immersion and does not invoke the target.
- `AlgebraicGeometry.Scheme.picardUniversalSingleRankMatch_of_source_local`
  (`lem-sc-picard-single-rank-source-local`): transports local rank witnesses across
  open base change; it imposes no geometry assumptions and constructs no locus.
- `AlgebraicGeometry.Scheme.exists_localImmersionLocus`
  (`lem-sc-local-immersion-locus`): generic gluing from already supplied local
  immersion representatives, base-change stability, and source locality; it contains
  no Picard or derived-cohomology construction.

Direct holes closed: 1. Direct holes added: 3. Net holes closed minus holes added: -2.
The existing lowest-cohomology locus theorem is used as supplied; its dependencies
remain future work. All four delivered modules compile together without errors or
non-sorry warnings. The delivery dry run also performs the declaration/axiom probes.

Edge cases checked mathematically: empty test schemes make the rank predicate
vacuous and their module sheaves are free of every rank; source locality applies
vacuously on empty sources; the empty-base gluing family gives the empty scheme.
Rank zero follows the same perfect-cohomology construction. No nonemptiness of a test
scheme, positive rank, quasi-compact base, or global Tor bound is assumed. Nonempty
fibres used to identify witness ranks follow from the universal structure-sheaf unit.

## No longer needed

Removed provisional proof imports from the earlier helper skeletons:
`Mathlib.AlgebraicGeometry.Gluing` from `LocalImmersionLocus`, and
`Sheaf.AlgebraicGeometry.PicardFiberRankClopen` and
`Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange` from
`PicardSingleRankPerfectChart`. Their declarations are not referenced by the current
statement signatures or whole-proof holes. Their mathematical tasks remain in the
new nodes' proof plans; future workers import them when they use them in actual proofs.
No original main-module imports were removed, and no original proof-dependency node
or module is mathematically pruned. The rank-stratum and perfect-direct-image steps remain needed
inside the new perfect-chart node; they were not bypassed. The lowest-cohomology locus
is needed directly in the main proof. No dual direct-image condition, intersection
with a second rank locus, or finite-presentation enhancement of the final immersion is
introduced or proved: the item concerns precisely one direct image and an immersion.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt had the three helper statements but left the main theorem
untouched and supplied no DAG nodes or report. This delivery completes their Lean
composition and supplies the missing metadata. The original mathematical route was
retained. Mathlib's pullback objects make naive rewriting of composite test maps fail
because of dependent chosen-limit arguments; `convert` followed by `congr! 8` proves
the required equality without changing the predicate or any interface.

LeanSearch returned an Internal Server Error for all three new statements; this is
recorded as unavailable, not evidence of absence. LeanFinder, Loogle, source grep,
and whole-blueprint searches were also checked. Mathlib's gluing and local
representability APIs require constructing overlap/cocycle or presheaf data; they do
not directly accept the local predicate hypotheses of the generic gluing theorem.
The source text was checked at Stacks Tags 0BDP, 0BDL, and 0B91. The first two say the
rank-stratum/perfect-complex construction and gluing used here; 0B91 supplies perfect
direct image and arbitrary base change.

## New nodes

`lem-sc-picard-single-rank-perfect-chart`, in
`dag/nodes/sec-abelian-varieties/lem-sc-picard-single-rank-perfect-chart.json`, states
only the local perfect model, its nonnegative finite Tor bound, and comparison of
the universal single-rank condition with universal lowest-cohomology freeness.
Source: Tag 0BDP, first three proof paragraphs, and Tag 0B91(2). Existing rank-stratum
and perfect-direct-image nodes remain its dependencies. Its proof handles arbitrary
further tests and determines the local witness rank using nonempty fibres.

`lem-sc-picard-single-rank-source-local`, in
`dag/nodes/sec-abelian-varieties/lem-sc-picard-single-rank-source-local.json`, states
source locality of the existing predicate. Source: Tag 0BDP's local rank conditions.
The proof pulls a neighbourhood back along a test map, applies its condition,
and transports both witnesses through ordinary open base change and pullback
composition. No strengthened assumptions are needed.

`lem-sc-local-immersion-locus`, in
`dag/nodes/sec-abelian-varieties/lem-sc-local-immersion-locus.json`, states the generic
local-representative gluing step. Source: Tag 0BDL's final proof paragraph, with
scheme gluing from Tags 01JB/01JC. The cocycle follows from uniqueness through
monomorphisms. The two implications of the global criterion use base-change
stability and source locality respectively. All new nodes record three search kinds
(LeanSearch unavailable), proof steps, complete Lean signatures, and the original
blueprint ancestry. No change record is required.
## Second reading by V2

1. I compared the delivered item module with the repository version. The target theorem signature, visibility, definitions, and original docstring are byte-for-byte unchanged; only proof imports and the proof body were added. Verdict: pass.

2. I compiled all four sandbox modules with the prescribed lcompile wrapper. There are no compiler errors or warnings. The item theorem has no sorry; the three explicitly split helper theorems are the only remaining sorries, each named in this report and represented by a DAG node. No forbidden axiom, unsafe, opaque, extern, implemented_by, or debug.skipKernelTC occurs. Verdict: pass subject to the three declared split obligations.

3. I checked each split-off statement against its declaration and node. The perfect-chart, source-locality, and local-immersion-gluing statements are strictly smaller than the item, have unchanged exact Lean signatures in their node records, source and proof prose, and are not duplicate declarations found in the library. Their statements cover the needed intermediate reductions without restating the item. Verdict: pass.

4. I checked the proof route from the target downward. It uses the existing lowest-cohomology locus theorem, the local perfect chart, source locality, and generic local-immersion gluing, while retaining the unit's rank-stratum and perfect-direct-image route. The removed imports are recorded above; no old proof dependency is bypassed in the main route. Verdict: pass.

5. I checked the four node records and their metadata against the Lean declarations, including proof steps, proof dependencies, origins, module paths, unit, chapter, and split status. The delivery adds no statement or definition change and no forced adaptation. Verdict: pass.

Changed during this second reading: appended this review section only; no Lean code or node metadata required repair.
