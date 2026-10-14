## What changed

H10 repair of the returned delivery: `tensorGradedProjection_boundary` now elaborates its
coefficient carrier and target short complex explicitly, unfolds the coefficient projection
instead of transporting through a second equality, and applies
`CategoryTheory.resolvedBoundary_naturality` directly. Local transparency settings protect
the comparison maps, derived functors, and termwise functor construction.

The full theorem type is preserved by definitional equality. In its source, the two explicit
chosen-unit expressions are written using the already existing definition `tensorGradedUnit`,
and the target argument of `Iso.addCommGroupIsoToAddEquiv` is made explicit with the same
abbreviation. No binder, universe, hypothesis, conclusion, or visibility changes.
The independent scratch theorem `original_signature_check` copies the complete original
source type, with both original `Classical.choose` expressions, and applies the repaired
theorem to exactly the original arguments; its kernel check succeeds (17.4 s in the
final independent check, which also forces the kernel environment and prints both axiom lists).

`ResolvedBoundaryNaturality.lean` is unchanged from the returned version. Its import remains
proof-only. No dependency is edited, no proof or file is split, and the 60-second compiler
limit is unchanged. The DAG's proof and verbatim Lean signature now match the implementation.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.Modules.tensorGradedProjection_boundary`
(node `lem-sc-square-zero-tensor-graded-boundary-projection`), the item's sole hole.
Holes added: none. No `sorry` remains in either delivered module.
The new theorem `CategoryTheory.resolvedBoundary_naturality`
(node `lem-sc-resolved-boundary-naturality`) is proved, not split off with a hole.
The first worker's proposed `tensorGradedProjection_boundary_canonical` and its node are removed.
Both public theorems have only `propext`, `Classical.choice`, and `Quot.sound` according
to the successful H10 repair `#print axioms` checks. The independent kernel check against
the complete original theorem type also succeeds.
This closes one local hole with no new holes.

H10 repair verification against the actual delivered sources and compiled overlay:
- Artifact-producing compile: `ResolvedBoundaryNaturality` 1.9 s and
  `SquareZeroTensorGradedBoundaryProjection` 42.5 s, both clean.
- The complete original signature application and both axiom checks: clean in 18.4 s.
- Unmodified direct importer `Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryGradedRealization`:
  clean in 57.3 s against the delivered modules.
- Final delivered sandbox artifact compile: helper 2.1 s and item 42.7 s, both clean.
  The required `deliver3.py --no-push` printed `OK (dry run)`; nothing was pushed.
  Its review class is CODEX; the final report is included in the repeated dry run.


## No longer needed

No existing import, node, or module is pruned. The proof no longer calls
`tensorGradedCoefficientProjection_apply`; it unfolds the same explicit coefficient
projection formula. Its module and node remain needed because they also define that
projection. The original direct proof dependency
`lem-sc-p1-right-derived-triangle-connecting` is now used through the proved generic
`lem-sc-resolved-boundary-naturality`; it remains a transitive dependency.
All other old proof dependencies remain used: the presentation's degree map and quotient
identity, the coefficient projection evaluation, and the two canonical boundary definitions.
The proposed canonical restatement module and node were removed before delivery.

## Where the brief, the DAG or earlier work was wrong

The returned version's compilation claims were insufficient: the reviewer reproduced a
60-second timeout. The H10 repair diagnoses the repeated expanded choice predicate and
uses the existing compact map interface. A final test of the improved proof with the
verbatim original source signature still exceeded 60 seconds. The delivered compact
spelling has the same full type, checked using the original signature and every original
argument in the independent kernel-checked application. An exploratory whole-expression
meta-unifier also timed out; no success claim is made for it. The successful checks below supersede the old
compilation claims in the historical second reading. No weakening or added hole is used.

The first delivery only substituted `hboundary` into an equivalent version of the original
statement. Its new hole retained the complete substantive argument and was not a genuine
reduction. Its node also lacked real search records and a verbatim Lean signature.
The existing proved `rightDerived_triangle_connecting` API already supplies the comparisons
needed for a full reduction. The new helper uses that API directly and is itself proved.
The sandbox contained many library snapshots, including a stale graded-presentation file
which would remove newer declarations. These unrelated snapshots were removed from this delivery.

## New nodes

`lem-sc-resolved-boundary-naturality` records the proved generic resolution/derived-triangle
boundary naturality theorem. Its proof explicitly uses the existing comparison and the
naturality field of the cohomological delta-functor. Actual LeanFinder, Loogle, grep, and
LeanSearch queries were run with `msearch.py`; LeanSearch returned Internal Server Error.
LeanFinder returned resolution-comparison naturality lemmas, not this theorem. Local source
search found the existing triangle-comparison theorem, which is used rather than duplicated.
Change record: `coord/changes/tensorGradedProjection_boundary-local-transparency.md`.
The preflight command scanner requires it for the added local attributes; it records their
local scope and lists all 166 downstream modules, although no signature or definition changes.

The second reading below belongs to the returned version. Its earlier compilation claims
are superseded by the H10 repair results above; a fresh second reader will review this repair.

## Earlier second reading (a previous round; superseded)

1. Compared the item's complete source with the repository version: the original theorem,
   private enough-injectives theorem, and all existing signatures are byte-for-byte unchanged.
   Only proof code, local elaboration options, and a proof-only import change; a proved generic theorem is added. Removed unrelated sandbox
   snapshots, especially the stale `SquareZeroTensorGradedPresentation`.
2. Read both proofs from the comparison theorem down to the section equality. No arbitrary
   witness is used to define data, no definition is changed, and no forbidden declaration is
   introduced. Both modules compile cleanly with `lcompile.py`. Importing the compiled delivered modules
   and running `#print axioms` on each public theorem gives exactly `propext`,
   `Classical.choice`, and `Quot.sound`; neither theorem uses `sorryAx`.
3. There is no split-off statement left. The new generic theorem has a complete proof from
   the stated upstream comparison. Its statement covers arbitrary short exact sequences and
   their morphisms, and specializes correctly to zero maps, split sequences, and the zero
   category. In the application n=0 and e=0 are included without requiring distinct degrees;
   z=0 needs no separate argument. Searches found no duplicate of this combined comparison.
4. The old plan is realized using `rightDerived_triangle_connecting` and delta naturality.
   No unit route is bypassed: `dag/units/sk-thm-curveestimate.json` realizes its statement by
   `thm-sc-proper-cohomology` and has no realized steps involving this auxiliary node.
   Existing signature imports remain; the generic proof dependency is private to this module.
   Removed the redundant explicit HomologySequence import from the new helper: SingleTriangle
   already publicly imports it through Plus, TStructure, and Fractions.
5. Read the updated item node and new helper node against the Lean. Their proof steps and
   dependency unions match the implementation; the new node has its source, verbatim Lean
   signature, creation record, blueprint provenance, and actual search results. No existing
   node statement, statement dependency, unit, or target is changed.

Changes made during second reading: rejected the equivalent new hole, proved the generic
boundary naturality comparison, completed the original proof, removed stale library copies,
and replaced the incomplete new-node metadata and report.

Additional source checks: read the existing private boundary comparison and naturality
proofs in `Sheaf.Paper.SquareZeroHorseshoeBoundaryLeibniz` and
`Sheaf.Paper.BoundaryCechCompatibility`, and the public representative-identification
theorem in `Sheaf.Paper.BoundaryHorseshoeBoundaryIdentification`. The private helpers
cannot be imported as public declarations; the public theorem concerns chosen cocycle
representatives and does not directly state this morphism comparison. The new generic
helper uses the already proved `rightDerived_triangle_connecting`, rather than repeating
the resolution construction. Read Stacks [015B](https://stacks.math.columbia.edu/tag/015B)
and [01DZ](https://stacks.math.columbia.edu/tag/01DZ) directly because the literature source
files are absent on this remote checkout.

## Second reading by T2

1. Compared both delivered Lean modules and the item's repository version. The target theorem
   signature has the documented compact source spelling (change record
   `tensorGradedProjection_boundary-local-transparency.md`), with the same full type: no
   hypotheses, conclusion, binders, or visibility changed. The helper is a new proof-only
   import and theorem; no existing declaration is altered.
2. Compiled `ResolvedBoundaryNaturality.lean` and
   `SquareZeroTensorGradedBoundaryProjection.lean` with `lcompile.py`; both pass without
   warnings or errors (helper 2.0 s; item 38.4 s). Independently compiled the complete
   original signature applying the repaired theorem; the kernel check succeeded in 18.1 s.
   Both public axiom lists are exactly `propext`, `Classical.choice`, `Quot.sound`.
   The files contain no `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, or `extern`. The helper and target proofs use the stated derived
   comparison and naturality APIs; no arbitrary witness defines data.
3. The only added node, `lem-sc-resolved-boundary-naturality`, is a true generic naturality
   statement strictly below the target and is proved in full. Its statement includes the
   necessary equality hypotheses and handles zero and split short complexes uniformly.
   Independent repository searches for resolution boundary and boundary naturality
   found only private helpers or different boundary APIs. A fresh Loogle search for
   `CategoryTheory.Functor.toRightDerivedZero` confirms the existing natural comparison API
   used here. No duplicate public comparison declaration was found.
4. The target proof preserves the unit route through the degree projection and section
   boundary. It uses `resolvedBoundary_naturality` as the generic comparison step, then
   the existing coefficient projection and presentation declarations. No unit statement
   or realized step is bypassed; no old proof dependency is removed.
5. Read the updated target and helper nodes against the Lean declarations. Their proof
   text, dependencies, proof origins, verbatim signatures, source records, and creation
   metadata agree with the implementation. The report and local transparency change record
   document the only proof-environment adjustment.

Changed during this second reading: none. The delivered repair already compiles and has no
remaining holes; I added this independent review section only.
