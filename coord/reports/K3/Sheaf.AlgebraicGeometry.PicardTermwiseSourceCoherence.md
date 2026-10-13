## What changed

Proved the body of AlgebraicGeometry.Scheme.picard_termwise_source_coherence without
changing its signature. The comparison family is constructed from canonicalSinglePullbackMap
and the inverse tensor-to-ordinary adjunction comparison; invertibility follows from
Modules.isIso_canonicalSinglePullbackMap and invertibility of the structure sheaf.
The final Lean proof applies a map-level composition equation and cancels the pinned
composition isomorphism. Added PicardTermwiseSingleMapComposition for that remaining equation.
Its definition picardTermwiseSingleMap is an explicit composite and contains no sorry.

## Proved and sorry left

Closed the original hole in AlgebraicGeometry.Scheme.picard_termwise_source_coherence.
Added one hole: AlgebraicGeometry.Scheme.picardTermwiseSingleMap_composition
(lem-sc-picard-termwise-single-map-composition). This is a decomposition with net zero holes,
not a complete proof. The residual statement is the composition equation on explicitly
constructed maps for arbitrary modules; it neither chooses a family nor asserts invertibility.
Object construction, invertibility, specialization to the unit, and cancellation of the
composition comparison are proved in the delivered main module.

## No longer needed

Removed the main module's direct proof import of
Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback and replaced its direct proof dependency
lem-pc-flat-complex-derived-pullback by lem-pc-canonical-single-pullback-comparison.
The bounded-flat computation remains an indirect dependency of the existing canonical
single comparison; no claim is made that it leaves the entire target closure.
The old dependency lem-pc-ringed-spaces-derived-pullback-composition remains in
proof_deps: the proof uses its pinned composition isomorphism. The old dependency
def-sc-picard-termwise-models also remains, supplying the source and counit.
Thus the only old proof dependency removed is lem-pc-flat-complex-derived-pullback.
No existing module is claimed globally pruned. All statement imports stay.

## Where the brief, the DAG or earlier work was wrong

The local published cache lacks PicardTermwiseModels.olean. An unchanged copy compiled
successfully through lcompile.py and supplied the sandbox overlay; it is not delivered.
The earlier attempt left the original theorem untouched. The new proof supplies the
canonical object family and isolates the remaining complex-versus-homotopy counit calculation.
Coherence cannot be asserted for arbitrary independently chosen object isomorphisms.
The residual lemma therefore concerns only the explicit canonical maps.
Edge cases (zero modules, empty schemes, identity morphisms and ht reflexive) require no
geometric hypotheses and obey the same counit and single-complex equations. The unit route
is preserved; the node lies below the unit's realized statements and steps.
Stacks Tags 06YJ and 0D5S were read on the Stacks website because the local literature
checkout is absent on this machine. No definition or existing statement changed.

## New nodes

lem-sc-picard-termwise-single-map-composition records the remaining canonical map equation,
with its complete categorical proof in words and searches. Its module is
Sheaf.AlgebraicGeometry.PicardTermwiseSingleMapComposition. This is strictly the coherence
part of the argument, before invertibility or a comparison family; it is not a renamed
existential source-coherence statement. No change record is needed.


## Second reading by K3

1. Compared both delivered modules with the repository: PicardTermwiseSingleMapComposition
   is new; the only existing declaration is picard_termwise_source_coherence.
   Its entire signature is byte-for-byte identical after removing an extra space before
   :=. No existing definition, visibility, statement import, or target changed.
   The existing node differs only in proof, proof_deps and proof_origin. No forced
   adaptation or change record is required. Verdict: pass.

2. Compiled the two modules in import order with lcompile.py --all: both clean.
   A scratch copy with #print axioms showed picardTermwiseSingleMap depends only on
   propext, Classical.choice and Quot.sound. Both picard_termwise_source_coherence
   and picardTermwiseSingleMap_composition additionally use sorryAx, as expected
   from the residual named theorem and open imported results. Source scanning found
   exactly one direct sorry, in the reported new theorem, and no forbidden declarations.
   The map is an explicit composite; the family uses asIso of that composite, with
   invertibility proved from isIso_canonicalSinglePullbackMap and the invertible unit.
   It chooses no arbitrary object witness. Verdict: valid decomposition, net zero holes.

3. Read the new theorem, its node, PicardTermwiseModels, tensorPullbackCompositionIso,
   canonicalSinglePullbackMap, canonicalSinglePullbackComposition and
   homotopySinglePullbackComposition. Read Stacks
   [06YJ](https://stacks.math.columbia.edu/tag/06YJ) and
   [0D5S](https://stacks.math.columbia.edu/tag/0D5S): the former constructs derived
   pullback and the latter computes its composition on K-flat representatives.
   The precise pinned equation is the categorical refinement supplied by the
   leftDerivedLift factorization, rather than a literal equation quoted from those tags.
   The new statement asserts only the map composition part, for explicitly fixed maps;
   it does not assert invertibility or choose the simultaneous comparison family.
   Zero modules and empty schemes need no additional assumptions; identity morphisms
   reduce to the same mate and single-complex equations. Equality induction handles ht.
   Independent LeanFinder and grep searches found generic exact-functor and adjunction
   tools, not this equation; Loogle did not index leftDerived_fac_app. Expanded the new
   docstring to give the evaluated lift equation, the degreewise single identity, the
   counit naturality step, and the quotient coordinate conversion. Verdict: true,
   strictly a part of the original argument, with a complete written proof and node.

4. The main proof constructs the family with the existing invertible-module theorem,
   specializes the new map equation at the structure sheaf, and cancels c.hom by c.inv.
   The closest existing composition theorem ends in an ordinary pullback single;
   tensor targets and the complex counit still require the documented transport.
   This calculation is not a few-minute additional proof, so its named hole remains.
   The new module's public imports supply the public map definition and counit signature;
   its plain composition import supplies the residual proof plan. The main module keeps
   only its original statement import and the new proof import. Corrected the pruning
   inventory and retained the pinned derived-composition dependency. Inspected
   dag/units/sk-prop-av-cube.json: realized.statement and its sole realized step are empty;
   neither delivery node is a realized unit statement or step. This decomposition stays
   below that unit and changes no chapter or unit route. Verdict: pass; no global prune.

5. Matched the DAG proof steps to the explicit construction, invertibility theorem,
   specialization, and inverse-hom cancellation. The new node's Lean statement is the
   exact theorem signature, with source, proof steps, their union in proof_deps,
   proof_origin, searches, creation metadata, blueprint ancestry, chapter and unit.
   Added the missing tensor-pullback-composition definition to stmt_deps and its citation
   to the statement, added lean_audit states, recorded independent searches, and retained
   the pinned derived-composition theorem in both proof plans. Verdict: pass.

Second reading changed signature whitespace and an extra blank line, expanded the new
lemma's proof docstring, completed node dependencies/audit/search metadata, and corrected
pruning documentation. No mathematical statement or definition changed. The delivery
closes one original hole and adds one residual hole; it is a decomposition, not a net proof.
