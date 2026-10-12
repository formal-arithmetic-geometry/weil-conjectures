## What changed

Replaced the first worker's invalid two-lemma reduction of
`AlgebraicGeometry.Scheme.ideal_h1_finiteType_representative` with the actual directed-colimit
argument. Its existing signature, visibility, definitions, and public imports are unchanged.
The proof constructs the nonempty directed index of finite-type subideals, invokes a new
algebraic diagram lemma, applies `openModuleCohomology_directedColimit` in degree one, and
uses the existing `RingedSpace.nonempty_moduleCohomology_top_iso` to transport the result.
Stage isomorphisms give the inclusion map and the required cohomology class.

Added `Sheaf.AlgebraicGeometry.FiniteTypeIdealDiagram` with one named algebraic hole.
Removed the tentative modules `FiniteTypeIdealH1Stage` and `FiniteTypeIdealH1Class` and
both of their tentative nodes; they were never part of the repository baseline.
All added imports used only in the target proof are plain `import`.

## Proved and sorry left

Closed the direct hole in `AlgebraicGeometry.Scheme.ideal_h1_finiteType_representative`.
Added one direct hole in `AlgebraicGeometry.Scheme.exists_finiteType_ideal_module_diagram`
(node `lem-pqf-finite-type-ideal-module-diagram`). This is a decomposition: one upper hole
closed and one strictly algebraic lower hole added, net zero direct holes closed in the
import closure. No unconditional axiom-free proof of the item is claimed.

The only sorry in the delivered modules is the whole proof of that named public theorem.
Its docstring gives the source and the full sectionwise construction and colimit proof.
The imported directed-colimit theorem and other upstream proofs remain open as before.
Both delivered declarations were checked with `#print axioms`; each reports only
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.

The first worker's holes `AlgebraicGeometry.Scheme.exists_finiteType_ideal_stage` and
`AlgebraicGeometry.Scheme.exists_h1_class_at_finiteType_stage` are removed, not counted as
baseline holes closed. The latter statement is false.

## No longer needed

Removed the direct proof import `Sheaf.Paper.PQFCohomology`. The old direct proof dependency
`pqf-def-cohomology` is replaced by the existing natural top-open comparison node
`lem-weil-pbc-module-cohomology-top-comparison`; it remains a statement dependency of the
original node, which is unchanged. The other old proof dependencies,
`lemma-nagata-ideal-directed-union-finite-type` and
`lem-weil-pbc-qs-scheme-cohomology-directed-colimit`, are still used.

No whole module is claimed to leave the targets' import closure: PQFCohomology remains
transitively imported by OpenModuleCohomologyDirectedColimit. No unit-realizing node is
pruned. The deleted tentative stage/class modules and nodes are not baseline pruning.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the first worker's `exists_h1_class_at_finiteType_stage` wrongly
quantified over an arbitrary finite-type subideal K. Setting K to zero makes its conclusion
assert x = 0 for every first cohomology class of I. For example, the ideal of a degree-two
effective divisor on the projective line is O(-2), whose H1 is nonzero. A directed-colimit
surjectivity theorem selects a stage depending on x; it does not make a stage selected
without x surjective on H1. The earlier second reading missed this quantifier error.

The algebraic stage lemma alone merely supplies a subideal (zero suffices); it does not
supply a directed colimit diagram. Both old split nodes also used the original target as
a statement dependency while the target used them as proof dependencies, creating DAG
cycles. The replacement algebraic node has no dependency on the target.

The needed top-open cohomology comparison is already in the library and proved. It is
used directly instead of being split off again. The source proof was checked against
https://stacks.math.columbia.edu/tag/01PG,
https://stacks.math.columbia.edu/tag/01FF, and
https://stacks.math.columbia.edu/tag/01XG.

## New nodes

`lem-pqf-finite-type-ideal-module-diagram`: the cohomology-free algebraic part of the old
plan. Its explicit index is the subtype of finite-type subideals, and each diagram object
is identified with that actual ideal's module. Compatibility with the monomorphic
structure-sheaf inclusions forces its transition and cocone maps up to the canonical stage
isomorphisms used downstream. The source is Stacks 01PG. LeanSearch was unavailable;
LeanFinder, Loogle and independent grep searches found general colimit constructions
and the existing ideal-lattice union, but no matching ideal-module cocone theorem.
No definitions are introduced, no arbitrary witness is extracted into a definition,
and no target or existing statement changes. No change record is needed.

## Second reading by E1

1. Interface: compared the delivered target module with the repository by diff and compared
   its entire signature as an exact byte string. PASS: the old declaration is unchanged
   except for its proof; all existing public imports are retained. No definition changes.
2. Proof: compiled both modules in import order with lcompile.py, without errors or warnings.
   Checked both declarations with scratch-copy `#print axioms`. PASS with the documented
   open algebraic hole and imported open theorems; no forbidden axiom or implementation
   construct, no sorry in a definition, and no partial or anonymous sorry.
3. Split statements: FAIL for the original class lemma, repaired by removing it. The new
   diagram lemma is true and strictly algebraic, with no H1 assertion. Checked zero I,
   empty X, and already-finite I: the zero stage exists, and a finite I is a terminal stage.
   Every stage is an actual ideal module up to its specified isomorphism. Its docstring
   supplies a full construction; its matching node records searches and source. The
   existing lattice-union theorem supplies local membership but not this module cocone.
4. Top-down route and pruning: PASS after replacing the invalid split. The proof uses the
   original directed-union and directed-colimit route and the existing proved top-open
   comparison. The unused PQFCohomology direct import and its proof dependency are listed
   above. The unit `sk-prop-av-pqf-finite` has empty realized lists for this ancillary item;
   these and the chapter/unit route are unchanged. No unit step is bypassed.
5. Nodes: PASS after repair. Existing statement/stmt_deps/lean records are unchanged;
   the updated proof and proof_deps describe exactly the four invoked nodes. The new
   node has the complete stage-3 fields, the exact Lean signature, no target dependency
   cycle, and proof_deps equal to the union of the proof steps' uses.

Second reading changed: removed the false fixed-stage surjectivity lemma and vacuous stage
lemma; replaced them by one true algebraic diagram hole; wrote the real directed-colimit
and natural-comparison reduction; repaired DAG dependencies and the pruning/progress report.
