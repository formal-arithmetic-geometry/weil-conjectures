## What changed

Replaced the first worker's `moduleCohomology_finiteSubsum_core` restatement with a real
reduction. The existing `moduleCohomology_finiteSubsum_representative` signature is
byte-for-byte unchanged. Its proof now applies the existing
`AlgebraicGeometry.openModuleCohomology_directedColimit` to a small finite-subsum diagram,
transports the representative through a proved natural scalar-forgetting comparison,
and identifies the structural map by biproduct component equations.

Added `Sheaf.AlgebraicGeometry.QcqsCohomologySmallSubsumDiagram` and
`Sheaf.Topology.ModuleCohomologyTopComparison`. The first states only the categorical
presentation and universe reduction, without any cohomology or qcqs assumptions.
The second proves the natural comparison on every ringed space using Mathlib's
`ShortComplex.homologyFunctorIso`, `Quotient.natIsoLift`, and
`Functor.mapHomotopyCategoryCompIso`. Removed the proposed core module and its node.
Updated the parent node's proof, proof_deps and proof_origin to the actual Lean proof.
All additional parent imports are proof-only plain imports; its public imports and
all existing statements/definitions are unchanged. No change record is required.

## Proved and sorry left

Existing hole closed:
`AlgebraicGeometry.Scheme.moduleCohomology_finiteSubsum_representative`.

New theorem proved:
`AlgebraicGeometry.RingedSpace.nonempty_moduleCohomology_top_iso`
(node `lem-weil-pbc-module-cohomology-top-comparison`).

New hole added:
`AlgebraicGeometry.Scheme.exists_small_finiteSubsum_diagram`
(node `lem-weil-pbc-module-coproduct-small-subsum-diagram`). This is the only textual
`sorry` in the delivered modules. It has a complete natural-language proof in its
docstring. It isolates the categorical finite-subsum presentation and the reduction
of the nonzero summands to Type u; it makes no assertion about cohomology.

This is a decomposition, not a completed proof of the item without open dependencies:
one existing hole closed and one smaller hole added, net zero local holes. The proof
also uses the pre-existing open directed-colimit theorem, which remains open in the
imported library. The superseded `moduleCohomology_finiteSubsum_core` hole is not delivered
and is not counted as a baseline hole closed. The ledger determines closure-wide net
figures after landing; this report does not claim a whole-library reduction.

## No longer needed

Removed direct imports `Mathlib.CategoryTheory.Limits.Constructions.Filtered` and
`Sheaf.Paper.PQFCohomology` from the parent. The finite-subcoproduct colimit construction
remains in the categorical helper's documented proof plan, rather than an unused import
of the parent. No globally unreachable module is claimed here.

Of the old proof_deps:
- `lem-weil-pbc-qcqs-scheme-spectral` and `def-weil-spectral-space` are no longer needed:
  the parent uses Mathlib's prespectral instance for schemes and
  `PrespectralSpace.isTopologicalBasis` from `Mathlib.AlgebraicGeometry.Properties`.
- `pqf-def-cohomology` is no longer needed as a proof dependency: the established
  `moduleCohomology` definition and the proved top-open comparison suffice.
- `def-weil-sheaf-of-modules-category`, `def-sp-abelian`, and
  `lem-weil-pbc-scheme-modules-coproduct-finite-subsums` cease to be direct parent proof
  dependencies, but are retained in the small-diagram node's argument and statement.
- `lem-weil-pbc-qs-scheme-cohomology-directed-colimit` remains a direct proof dependency
  and its declaration is actually applied.

The original unit `sk-thm-p1` and its `realized` statement/step nodes are unchanged.
No chapter or unit step is bypassed; the changes are internal to this tool lemma.

## Where the brief, the DAG or earlier work was wrong

The first worker's core theorem was equivalent to the entire original theorem: the
component equations force its existential map to equal `biproduct.desc`. Moving that
statement to a new module and proving only map uniqueness is not a strict decomposition.
Its docstring also omitted the substantive directed-colimit and universe-size argument,
and the parent node had not been updated to reflect the new proof dependency.

The replacement applies the existing directed-colimit result explicitly, proves the
scalar-forgetting comparison rather than postponing it, and leaves only the independent
categorical presentation task. The parent report now distinguishes decomposition from
proof completion and lists the actual removed dependencies.

## New nodes

`lem-weil-pbc-module-coproduct-small-subsum-diagram` corresponds to
`AlgebraicGeometry.Scheme.exists_small_finiteSubsum_diagram` in
`Sheaf.AlgebraicGeometry.QcqsCohomologySmallSubsumDiagram`. Its proof separates the smallness
of the nonzero summand index subtype (using coproduct projections and sections), the
finite-subcoproduct colimit construction, and finite-stage reindexing. It is true for
arbitrary schemes, empty index types, arbitrary index universes, and all-zero families.
It is the sole split-off hole.

`lem-weil-pbc-module-cohomology-top-comparison` corresponds to the proved
`AlgebraicGeometry.RingedSpace.nonempty_moduleCohomology_top_iso` in
`Sheaf.Topology.ModuleCohomologyTopComparison`. It packages the natural homology comparison
for exact scalar forgetting; it adds no hole. Both nodes have recorded LeanSearch,
LeanFinder/Loogle, and Mathlib grep searches run through msearch.py. LeanSearch returned
Internal Server Error; the other searches found construction tools, not these full
statements. No change records and no forced adaptations.

## Second reading by H2

1. Compared the parent with the repository using diff and independently compared the
   declaration signature as text: byte-for-byte unchanged. No existing definition,
   hypothesis, conclusion, public import or declaration visibility changed. The only
   existing declaration edited is the item's proof. Verdict: pass after repair.
2. Compiled all three modules with lcompile.py, in import order, without errors or
   warnings. Scanned for prohibited declaration forms and sorry-in-data: none. Ran
   #print axioms on scratch copies for all three declarations. The comparison has only
   standard axioms; the parent and categorical helper additionally use sorryAx, from
   the declared open theorem(s). No other axioms. Verdict: pass with the documented hole.
3. Rejected the core restatement and removed its module/node. The replacement categorical
   theorem contains no cohomology and no compactness assumptions, so it is strictly one
   part of the argument. Checked its projection/section injection, universe reduction,
   empty/all-zero family, and finite reindexing cases. Its docstring supplies the full
   argument and its node agrees. Searched Mathlib by different terms and searched both
   repository roots: the finite-subcoproduct construction exists, but the complete small
   diagram presentation does not; the natural top comparison is proved by composing
   existing Mathlib tools. Verdict: pass.
4. The parent explicitly applies the existing directed-colimit theorem at the whole
   space and uses Mathlib for the basis and a proved natural comparison. Removed unused
   imports, accounted for every original proof_dep above, and checked
   dag/units/sk-thm-p1.json realized: no change to its route. Verdict: pass.
5. Opened the original and new nodes with the Lean modules. Updated the original node's
   proof, proof_deps and proof_origin to the actual argument; the two new nodes have
   self-contained statements, sources, proof steps with their dependency union, search
   evidence, creation/blueprint/chapter/unit fields and verbatim Lean signatures.
   Verdict: pass.

Second reading changed the restatement into a genuine directed-colimit reduction,
proved the scalar-forgetting comparison, replaced the remaining hole by a categorical
small-diagram statement with a full docstring proof, removed unused imports, repaired
DAG metadata, and corrected the progress accounting. Final delivery validation is
through deliver3.py; no hand-run claim, preflight, lake, or repository git command.
