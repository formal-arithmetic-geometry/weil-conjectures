## What changed

Replaced the sole sorry in Sheaf.CategoryTheory.GrothendieckEdgeCocycle with a
complete reduction. The theorem's signature is unchanged. Constructed the cycle
lift with Mathlib liftCycles and proved its inclusion equation. Constructed the
specified filtration for every integer step, then proved finiteness,
exhaustiveness and separation directly from its top and bottom bounds.

Proved the collapse implication using the existing truncation spectral object.
Two private proved helpers induct over the finite truncation intervals, then use
the spectral object's exact sequence to make its left edge an isomorphism.
This uses no additional sorry. The sole remaining step is the fixed-degree CE
cocycle/edge comparison, in a new module with its own node and full proof plan.
It assumes a supplied cycle lift; its existence is proved in the original module.
It contains neither the filtration assertion nor the collapse implication.

Public imports now name GrothendieckComposablePair and Filtration directly.
The comparison is a proof-only import. The import change is recorded in
coord/changes/GrothendieckEdgeCocycleImports.md.
The comparison module retains proof-only imports of CartanEilenbergExists and
GrothendieckSSDoubleComplexModel, the open dependencies used by its proof plan.

Both delivered modules compiled together without warnings via lcompile.py --all.
The read-only import-pruning check passed. The first worker checked the then-direct
importer LerayDegenerateSections; the second reading checks the current direct
importers LerayEdgeCocycleData and LerayEdgeVanishingIso. Small cases checked mathematically:
G=id reduces the comparison to the cohomology quotient; n=0 has no lower
truncation intervals, so the collapse proof applies without a positive-degree
assumption in that degree; X=0 gives zero maps. The filtration proof covers
negative integer steps as well as the endpoints 0 and n+1.

## Proved and sorry left

CategoryTheory.grothendieck_left_edge_cocycle (lem-pc-grothendieck-edge-cocycle)
has no sorry in its body. Its filtration and collapse clauses are proved from
already proved library/Mathlib facts. Its cocycle inclusion equation and the
existence of the lift are also proved.

The only delivered sorry is CategoryTheory.grothendieck_cocycle_comparison,
in Sheaf.CategoryTheory.GrothendieckCocycleComparison, node
lem-pc-grothendieck-cocycle-comparison. Therefore the full theorem still depends
on sorry through this strictly smaller fixed-degree comparison. No private
helper contains sorry. No definition, target signature or universe was changed.

## No longer needed

Removed these imports from the item:

- Sheaf.CategoryTheory.GrothendieckSSDoubleComplexModel (formerly public).
- Sheaf.CategoryTheory.EdgeCollapse.
- Sheaf.CategoryTheory.ExactCouple.
- Sheaf.CategoryTheory.ExactCoupleConvergence.
- Sheaf.CategoryTheory.GrothendieckSpectralSequence.
- Sheaf.CategoryTheory.HypercohomologyFirstPage.
- WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck.
- WeilConjectures.Mathlib.Algebra.Homology.TotalComplex.

The last upstream Grothendieck module remains a necessary transitive statement
import through GrothendieckComposablePair; it is not mathematically pruned.
GrothendieckComposablePair itself is retained, now as a public statement import.

The completed filtration and collapse proofs need none of lem-sp-edge-collapse,
def-sp-exact-couple, def-sp-convergence, thm-sp-grothendieck, thm-sp-if-e1,
thm-sp-double-complex-spectral-sequences or
lem-pc-grothendieck-ss-double-complex-model. The item's direct proof_deps now
record the new comparison, the needed definitions and the proved upstream edge
API. The new comparison's proof plan still needs the CE model and CE resolution
existence, with their existing dependencies: these are moved to that narrower
remaining task, not declared globally unnecessary. No claim is made that any
listed module is unreachable from every other target.

For completeness, the other removed direct proof_deps are
lem-sp-derived-well-defined and def-sp-composite-acyclicity. Their APIs remain
statement dependencies and are used by the comparison's proof plan; neither is
globally pruned. Thus every old proof dependency removed from the item's direct
list is accounted for here.

## Where the brief, the DAG or earlier work was wrong

The plan used the generic exact-couple edge-collapse theorem for an assertion
that follows directly from the already proved truncation spectral-object API.
The old public model import was unnecessary for the theorem's statement.

The docstring called Tag 015K the lemma constructing the two spectral sequences.
Tag 015K is the functoriality remark; that lemma is Tag 015J. The delivered
docstrings correct this reference. Tag 015N supplies the CE construction, but
does not explicitly state the cocycle formula: the new comparison's proof is
marked agent-written and expands the supplied node's step 2. The underlying
Stacks text was read at https://stacks.math.columbia.edu/tag/015N and
https://stacks.math.columbia.edu/tag/015J.

LeanSearch returned HTTP 500 and is recorded as unavailable. LeanFinder, Loogle
and source searches found the derived-functor computations and abstract edge
but no theorem for the remaining cocycle equation. The unit's realized lists
are empty and unchanged; the Riemann--Roch/Leray route above this node is kept.

## New nodes

lem-pc-grothendieck-cocycle-comparison is a fixed-degree equation for any supplied
lift commuting with cycle inclusions, stated in
lean/Sheaf/CategoryTheory/GrothendieckCocycleComparison.lean. Its node records the
CE model, source, complete expanded proof, three search kinds and exact Lean
signature. It isolates the equation from step 2; the cycle lift, filtration and
collapse remain proved in the original module. The public-import change record
is coord/changes/GrothendieckEdgeCocycleImports.md.

## Second reading by N2

1. Interface: compared the complete delivered item with the repository by diff,
   and compared the text from `theorem grothendieck_left_edge_cocycle` to `:= by`
   byte for byte. It is identical: categories, universes, derived-category and
   finite-limit assumptions, hFG, X, I, the existential cycle equations, every
   integer filtration step and the collapse implication are unchanged. No existing
   definition changed. Only the declared public-import change alters visibility.
   The repository has since split the direct Leray importer into
   LerayEdgeCocycleData and LerayEdgeVanishingIso; updated the change record's users.
2. Proof: both delivered modules compile locally without warnings. The only sorry
   is the entire body of grothendieck_cocycle_comparison, with its node and source
   docstring. No definitions, private helpers or anonymous proofs contain sorry;
   no axiom, unsafe, opaque, implemented_by or extern occurs. A scratch-copy
   `#print axioms` for interval_isZero and spectral_left_edge_isIso lists exactly
   propext, Classical.choice and Quot.sound. The main theorem and comparison list
   those plus sorryAx, as reported. Read interval_isZero's base and exact₂ step:
   the two adjacent intervals are zero, so the union is zero. In the collapse
   helper q<n<=m gives p=m-q>0 and p+q=m, including m=n+1. The two zero intervals
   give the first isomorphism, and the first-quadrant upper bound gives the second.
   Both current direct importers compiled in an isolated scratch sandbox against
   the delivered modules, without warnings.
3. Split statement: read the comparison signature and its three node steps,
   CartanEilenbergExists and GrothendieckSSDoubleComplexModel, and Stacks Tags
   015N and 015J (https://stacks.math.columbia.edu/tag/015N and
   https://stacks.math.columbia.edu/tag/015J). Its hypotheses are precisely those
   of the generic cocycle clause, with n and a supplied lift made explicit. hc
   determines c uniquely by monicity of iCycles. The first worker has proved
   existence of this c, the filtration and the collapse, so this remaining
   equation is strictly smaller than the original item. Checked G=id (ordinary
   cohomology quotient), n=0 (kernel of the first resolution differential, no
   negative incoming boundary), and X=0 (zero maps). Injectivity of the CE
   horizontal cycles and boundaries is what splits the relevant sequences;
   G is not assumed exact. Expanded the docstring and node step 3 with the
   augmentation/quotient naturality square and the resolution-degree-zero sign.
   Independent LeanFinder search for mapped cohomology/truncation comparisons,
   Loogle search for homologyπ/map, msearch grep in Algebra/Homology, and rg on
   both library roots and the upstream checkout found no existing edge equation.
   Those hits concern exact functors, ordinary homology naturality or truncations,
   not the needed canonical Grothendieck comparison. This is not a few-minute
   formal proof from an existing lemma; it remains the explicitly named task.
4. Route and pruning: the cycle lift uses liftCycles/iCycles_d directly, the
   filtration uses imageFiltration_mono and its top/bottom bounds, and the collapse
   uses proved spectral-object exactness instead of the open generic edge-collapse
   theorem. Read the upstream definitions of leftEdge and grothendieckLeftEdgeMap
   and the image-filtration bounds; they are the maps and bounds used here.
   sk-thm-picard-rr.realized is {statement: [], steps: [[]]} and remains unchanged;
   the Leray/cohomology passage of the ancestor is retained. The report now lists
   every removed old direct proof dependency, including derived-well-defined and
   composite-acyclicity. CE model dependencies are moved to the comparison, not
   globally pruned. Fixed their missing proof-only imports so the remaining plan
   stays reachable. A fresh read-only import_prune_check passed on this snapshot.
5. Nodes: the existing node differs only in proof, proof_deps and proof_origin.
   The steps match the actual lift, transported filtration and interval induction;
   proof_deps is their union. The new node matches the supplied-c equation and
   has source, full proof steps, searches, blueprint provenance, created, chapter,
   unit and Lean record. Its agent-written origin correctly acknowledges that
   Stacks supplies the construction rather than explicitly stating this formula.
   The new proof-only CE imports now agree with those remaining proof dependencies.

Changed in this reading: retained the comparison's planned CE dependencies as
plain imports; expanded its representative calculation in prose and the node;
completed the pruning accounting; updated the stale downstream users and checks.
The main Lean proof and all declaration signatures were retained.
