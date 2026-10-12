## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.Modules.exists_restrict_chainMap_pair_of_stalk`
with a complete Lean proof. The signature and existing public imports are unchanged.
The proof checks the boundedness and finite freeness of the single complex,
applies one-map extension twice, and takes the intersection of the resulting opens.
Both extensions use the same explicitly constructed natural comparison, so their
conjugacy equalities have exactly the common isomorphisms required by the conclusion.

Added `Sheaf.AlgebraicGeometry.StalkRestrictionComplexIso`, with the actual construction
`stalkRestrictionComplexIso`: termwise application of restriction-to-pullback,
pullback composition, and equality of the composite scheme map with the stalk map.
This definition contains no postponed proof or choice from an existence statement.

Replaced the earlier sandbox-only `FiniteFreeStalkChainMapLift` draft with the
one-map theorem `exists_restrict_chainMap_of_stalk_eventually`. It asserts extension
of one map between bounded complexes with zero or finite free terms, on every
sufficiently small neighbourhood, using that fixed comparison. It has one named
sorry with a complete proof in words. The original DAG's finite-matrix argument
applies to one map; restriction gives the hereditary conclusion. The pair theorem
uses this genuinely one-map statement twice, with reversed source and target.
Updated the parent node's proof, proof_deps, and proof_origin to this route.

All three delivered modules compile in import order through lcompile.py.
The second reader narrowed the comparison module to Mathlib.Algebra.Homology.Additive
and placed the public Embedding.CochainComplex import in the one-map module,
whose signature actually uses IsStrictlyGE and IsStrictlyLE.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.exists_restrict_chainMap_pair_of_stalk`
(node `lem-pc-finite-free-stalk-chain-map-pair-lift`). Its proof has no sorry.
The canonical comparison `AlgebraicGeometry.Scheme.Modules.stalkRestrictionComplexIso`
(node `def-pc-stalk-restriction-complex-iso`) is an explicit construction from Mathlib.

Added exactly one remaining hole:
`AlgebraicGeometry.Scheme.Modules.exists_restrict_chainMap_of_stalk_eventually`
(node `lem-pc-finite-free-stalk-chain-map-lift`). No other delivered declaration
contains sorry. The earlier sandbox draft was never delivered and is replaced,
not retained as another dependency.

This is a decomposition: one upper hole closed, one one-map hole added, net zero
holes removed. The pair assembly and the comparison construction are checked Lean.
No claim of an axiom-free proof of the entire pair theorem is made while the
one-map theorem remains sorry.

Edge cases checked against the new statement: zero ranks and zero complexes have
unique zero maps; empty support intervals force zero complexes; arbitrary integer
bounds allow the single complex in any degree, including outside [0,d]. The new
statement requires only opens containing y, so no empty-open witness is used. The
intersection argument retains y and works without assuming intersections are affine.

## No longer needed

Removed the proof-only import `Sheaf.Topology.PresheafModuleStalkFunctor` from the item.
Neither the pair assembly nor the canonical comparison uses its module stalk functor.
The underlying germ representation and equality criterion of
`def-weil-pbc-module-stalk` remain part of the one-map theorem's proof plan; that node
is therefore not claimed to be mathematically pruned. The other old dependencies,
`def-weil-pbc-free-module` and
`lem-weil-pbc-open-immersion-module-pullback-restriction`, remain needed indirectly
by the one-map argument and canonical comparison. No additional nodes or modules
are claimed pruned, and the unit's route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt introduced an isolated one-direction theorem with arbitrary
comparison isomorphisms, then stopped at the common-neighbourhood problem. Such
isomorphisms need not be the same between separate lifts. The repair fixes a
canonical comparison and requires the one-map extension on all smaller opens.
The two applications can then be combined by an actual intersection proof.

The original plan's representation of finitely many coefficients, shrinking for
chain equations, and comparison step is preserved within the one-map theorem.
This proof does not introduce a second version of the pair statement. No existing
statement or definition was changed, and there are no forced adaptations.

LeanFinder found ring-morphism spreading and germ results, not chain-map extension;
Loogle with fromSpecStalk and mapHomologicalComplex had no hits; source searches
found no one-map theorem. The existing internal-Hom finite-presentation theorem
addresses linear stalk maps, and does not directly give a chain map between these
scheme-pullback complexes. LeanSearch was unavailable (Internal Server Error),
recorded as unavailable rather than as evidence of absence. Whole-blueprint searches
for 'finite free chain map' and 'stalk restriction complex' returned no matches.

## New nodes

`def-pc-stalk-restriction-complex-iso` records the explicit natural comparison in
`Sheaf.AlgebraicGeometry.StalkRestrictionComplexIso`. Its source is the parent
node's comparison step (step 3); its construction uses Mathlib's
restrictFunctorIsoPullback, pullbackComp, pullbackCongr, fromSpecStalkOfMem_ι,
and mapHomologicalComplexCompIso. No sorry is introduced by this node.

`lem-pc-finite-free-stalk-chain-map-lift` records hereditary extension of one
prescribed stalk chain map in `Sheaf.AlgebraicGeometry.FiniteFreeStalkChainMapLift`.
Its source is the parent's finite-matrix extension argument (steps 1--3), applied
once, followed by restriction. The complete matrix, chain-equation, comparison,
and restriction-coherence argument is in both the node and the theorem docstring.
Both new nodes inherit the parent's chapter, unit, and blueprint ancestor.
No change record is needed because existing interfaces are unchanged.


## Second reading by Q1

1. Existing interfaces: PASS. Read the complete diff against the repository module.
   The only changes there are the private proof dependency and the theorem body.
   The declaration comparison reports `statement_changed []`; the existing signature
   is byte-for-byte unchanged. No existing definition or public import changed, and
   no forced adaptation or change record is required.

2. Proof and data: PASS as a decomposition, not an axiom-free completion.
   All three modules compile locally in import order without warnings. A scratch
   copy with explicit `#print axioms` shows that stalkRestrictionComplexIso uses only
   propext, Classical.choice and Quot.sound; the one-map theorem and pair theorem
   additionally use sorryAx. The only textual sorry is the named one-map theorem.
   No forbidden declarations or attributes occur. The comparison is an explicit
   composition of Mathlib natural isomorphisms, with no arbitrary witness selected
   from an unproved existence theorem. The scratch copy was removed.

3. Split statement: PASS. The remaining statement extends one prescribed map, with
   fixed comparisons and stability under further restriction. This is strictly the
   one-direction coefficient-extension part of the pair argument, not a renamed
   pair theorem: the delivered proof verifies the single complex's bounds and free
   terms, invokes the lemma twice in opposite directions, and intersects the opens.
   Finite support leaves finitely many matrix coefficients and chain equations;
   germ representation and germ equality suffice. The restriction coherence follows
   from the canonical adjunction and pullback-composition comparisons. Checked zero
   ranks, zero terms, disjoint or empty support intervals, arbitrary integer bounds,
   and non-affine intersections; none requires an additional assumption. The full
   proof in words and matching node are present. Independent searches used LeanFinder
   for "Morphisms of finite presentation sheaves spread from germs to an open
   neighbourhood", Loogle for `"stalk", "HomologicalComplex"`, and source searches
   for restriction chain maps, finite presentation and internal Hom. Results included
   germ_exist and germ_eq, but no direct bounded-complex extension theorem. The
   remaining formalization is substantial and was not replaced by speculative tactics.

4. Route and pruning: PASS. The pair proof takes the direct intersection route;
   no inverse or homotopy equations are introduced. The item privately imports the
   one-map lemma; its comparison appears in the latter's public signature. The
   report accounts for all three original proof_deps: free modules and restriction
   comparison remain indirect, and germ representation/equality remain in the
   one-map proof plan, while the unused bundled module-stalk functor import is
   removed. No whole module is claimed unreachable from all targets. Read
   dag/units/sk-thm-picard-perfect.json: its realized statement and step arrays are
   already empty in the repository; this delivery leaves that pre-existing record
   unchanged and retains the unit's finite-matrix spreading route.

5. DAG correspondence: PASS. Read all three delivered nodes and the original
   parent node. Their recorded Lean signatures occur verbatim in the corresponding
   sources, and each proof_deps list equals the union of its proof steps' uses.
   The parent records the actual two applications and intersection. The new
   comparison node records a definition, and the new one-map node has source,
   proof, searches, creation metadata, blueprint ancestry, chapter, unit and Lean
   record. The report counts one upper hole closed and one lower hole added, net
   zero, and names both declarations.

Changes by the second reader: retained the correct proof and statements; narrowed
StalkRestrictionComplexIso's homology import from Embedding.CochainComplex to
Additive, and imported Embedding.CochainComplex directly in FiniteFreeStalkChainMapLift
for its strict-bound signature. Recompiled the full delivered set successfully.
Added this review and the independent search and axiom-check evidence to the report.
