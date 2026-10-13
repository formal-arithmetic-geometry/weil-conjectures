## What changed

Proved `AlgebraicGeometry.Scheme.Modules.picardExternalCechCupDegreeMaps_comm_ι`
in `Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferentialCoordinate` with the
existing statement, definitions, visibility and docstrings unchanged. Proved private helpers
identify pullback restrictions, scalar Cech differential coordinates, degree transports and
Alexander--Whitney face indices. The signed Leibniz identity on pure tensors and Mathlib's
tensor-total differential inclusion formulas finish the theorem.

The second reading removed duplicate private lemmas `aw_sum`, `tmul_sum_left` and
`tmul_sum_right`. A proof-only `import all Sheaf.Paper.CechCupProduct` makes the existing
proved private lemmas available. This module was already in the import closure; the change
adds no module to that closure. Transparency options now apply to individual declarations,
with no section-wide option commands. The node's proof text records the reused arithmetic.

The coordinate module compiles without errors or warnings. The unchanged direct importer
`Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferential` is checked against this delivery
in a separate verification sandbox. The axiom queries are recorded in the second reading.

Change record: `coord/changes/picard-external-cech-coordinate-local-options.md` documents
local proof elaboration options; no interface or target meaning changes.

## Proved and sorry left

Closed the sole hole: `AlgebraicGeometry.Scheme.Modules.picardExternalCechCupDegreeMaps_comm_ι`
(node `lem-sc-picard-external-cech-cup-differential-coordinate`).

Holes closed: 1. Holes added: 0. No `sorry` remains in the delivered module. All remaining
private helpers are proved; this is a proof, not a decomposition.

## No longer needed

None of the old imports, proof dependencies or modules is pruned. The public import
`Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegree` is needed by the existing signatures.
All four old proof dependencies remain used: bidegree coordinates, scalar Cech models,
pullback adjunction units and the Cech cup-product faces/restrictions/arithmetic.
Three duplicate local helpers were removed, with their uses redirected to existing proofs.

## Where the brief, the DAG or earlier work was wrong

The earlier claim that CechCupProduct's private arithmetic was inaccessible was wrong:
Lean's proof-only `import all` exposes those lemmas. This repairs the duplicate `aw_sum`
reported in `coord/returns/J2.md`, and also removes the two duplicate tensor-sum helpers.
No renaming or restatement is used to evade the duplication check.

The earlier report also claimed section-wide options had been removed while they remained
in the source. They are now declaration-local. The first worker's unrelated batch-import
collision involved two modules neither edited nor newly imported here; no forced importer
adaptation is delivered.

The unit `sk-prop-av-cube` currently has empty `realized` lists. They are left unchanged;
this ancillary coordinate lemma retains its existing node route toward the cube theorem.

## Second reading by J2

1. Compared the full source diff with the repository baseline. Each existing declaration
   signature and docstring is byte-for-byte unchanged, and the existing degree-map definition
   and inclusion theorem bodies are unchanged. Only the missing proof, private proof helpers,
   proof-only import and local elaboration options are added. Verdict: pass.
2. Compiled the delivered file and the unchanged direct importer against its compiled overlay.
   Searched the delivered source for forbidden constructs and holes: none. Scratch queries
   for the coordinate theorem and assembled chain equation show only `propext`,
   `Classical.choice`, `Quot.sound`. The delivery probe checks every declaration. Verdict: pass.
3. No split-off statement, new public statement or hole is added. Read the private proofs:
   naturality identifies pulled restrictions, degree casts reduce to identity restrictions,
   and face-index equalities feed the existing finite-sum cancellation. The sums cover p=0
   and q=0; cancellation uses integer additive actions, including characteristic two.
   Empty index families give vacuous coordinates. No arbitrary existential witness is newly
   introduced: pulled sections use the same existing adjunction unit as the specification.
   Verdict: pass.
4. Searched the library for an external Leibniz shortcut and inspected CechCupProduct and the
   bidegree specification. Reused three existing arithmetic lemmas through `import all`;
   the ordinary same-scheme cup theorem does not directly cover two source schemes/families.
   The only public import is required by signatures; the added import is proof-only. All old
   proof dependencies remain used and the unit route is preserved. Verdict: pass.
5. Read the node's proof, dependencies, origin and the unit record. Updated proof text and
   origin note to describe arithmetic reuse; the existing four proof dependencies and Lean
   attachment remain correct. No new node or unit change is needed. Verdict: pass.

Second reading changed: removed three duplicate private helpers and reused their existing
proofs; made transparency options declaration-local; corrected the report and change record;
updated the node's proof description. No statement, definition or public import changed.
