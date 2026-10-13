## What changed

Replaced the only hole in
`AlgebraicGeometry.exists_standardSingle_stalk_flat_counit_model` with a compiling
source-open induction. Its existing signature, universe binders, public imports
and docstring are unchanged. The proof uses `quasiCompactOpen_induction`: over
affine bases the source is compact and quasi-separated; affine presentations and
union gluing establish the presentation at the top open; localization converts
that presentation to the original scalar-extension stalk coordinates.

Added the real Prop definitions
`AlgebraicGeometry.StandardSingleFlatCounitPresentation` and
`AlgebraicGeometry.StandardSingleFlatCounitOnOpen` in
`Sheaf.AlgebraicGeometry.StandardSingleFlatCounitPresentation`.
The first records a bounded flat **sheaf** complex on the base, its identification
with the original direct image, its ordinary pullback target identification and
its pinned sheaf counit equation. It has no stalk, no scalar-derived pair, and no
selected data. The second quantifies over all relatively flat quasi-coherent
modules on a source open, allowing their restrictions in the induction.

Added three strictly separate steps in their own modules: the affine source
calculation, Mayer--Vietoris gluing of presentations, and affine-base localization
with exact-stalk/counit transport. The target proof imports these four proof
modules privately, including the existing open-induction module. Updated the
original DAG node and wrote nodes for both predicates and all three steps.
There are no statement changes or forced adaptations, and no change record.
The second reader removed four redundant imports from the new union and
localization modules and clarified that chain-map lifting in the union argument
uses projective section modules through the affine derived equivalence.

Validation: all five delivered Lean modules compile in dependency order via
`lcompile.py --all` (about 3--6 seconds each). No warning or error was emitted.
The original target signature was compared byte for byte with the repository.
The final delivery dry run supplies the per-declaration axiom probes and preflight.

## Proved and sorry left

Holes closed in the original item: 1 of 1,
`AlgebraicGeometry.exists_standardSingle_stalk_flat_counit_model`, node
`lem-pc-standard-single-stalk-flat-counit-model`.

Holes added, each as the entire proof of a public named theorem:

- `AlgebraicGeometry.standardSingleFlatCounitOnOpen_affine`, node
  `lem-pc-standard-single-flat-counit-affine`;
- `AlgebraicGeometry.standardSingleFlatCounitOnOpen_union`, node
  `lem-pc-standard-single-flat-counit-union`;
- `AlgebraicGeometry.standardSingleFlatCounit_localization`, node
  `lem-pc-standard-single-flat-counit-localization`.

This is a decomposition, not a sorry-free proof: one upper hole is replaced by
three strictly smaller geometric steps, net holes closed minus added = -2 before
any import-closure pruning. None is the original theorem with its hypothesis
repackaged. The affine step covers only affine source charts over affine bases;
the union step assumes presentations on three smaller opens and constructs the
one on their union; the localization step assumes affine-base sheaf presentations
and only transports them to stalk coordinates. Real Lean combines these steps by
source-open induction. No hole remains in the original module or in a definition.

Edge cases checked when stating the steps: the empty affine open uses the zero
single complex; zero modules use zero complexes; repeated and empty members of
a two-open cover yield redundant or zero cones; a negative degree is treated by
the same complexes; an empty new base has no point. The source can be qcqs and
nonseparated: the overlap with the next affine chart is quasi-compact separated,
exactly the case handled inside the existing open induction. No flatness of the
new-base morphism, properness, finite presentation, or global compactness of the
original base is added.

## No longer needed

No original public import is removed. No original geometric dependency is claimed
pruned: affine alternating Cech flatness remains below the affine step,
derived Mayer--Vietoris remains below the union step, and the canonical comparison,
relative flatness and module stalk definitions remain below the new steps.
The original node's immediate proof dependencies are replaced with the three new
steps and `lem-sc-invert-s-cohomology-induction`; this is subdivision, not removal
of those geometric tasks. The earlier rejected scalar-pair and geometric-part
nodes are not delivered. No downstream base-change isomorphism is imported.

Redundant imports removed by the second reader: from
`StandardSingleFlatCounitUnion`, `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
and `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`; from
`StandardSingleFlatCounitLocalization`, `Sheaf.Algebra.Homology.ModuleStalkFunctor`
and `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`.
Their declarations are already publicly available through the presentation module;
all four modules remain reachable, so no module is claimed pruned.

Every old immediate dependency remains in the new lower plans:
`def-pc-derived-base-change-map`, `def-pc-module-stalk-functor`,
`def-pc-scheme-module-flat-over`, `def-pc-standard-single-base-change-map`,
`lem-pc-affine-alternating-cech-model-flat`, and
`lem-pc-derived-mayer-vietoris-triangle`. None is a pruned mathematical task.

## Where the brief, the DAG or earlier work was wrong

The earlier split moved the entire geometric conclusion into a helper taking a
universal scalar pair. That helper did not expose a step of the construction.
This attempt instead writes the source-open induction in Lean, with a pre-stalk
presentation property that includes the base direct-image iso needed to lift
restriction arrows. Arbitrary unrelated stalk-cohomology isos do not suffice to
glue complexes, which is why the new predicate retains that iso and pins its
source factor to derived pullback of it.

The available `AffineAlternatingCechBaseChangeFactorization`,
`AffineAlternatingCechPinnedMate` and `AffineAlternatingCechExchangeResolution`
modules cannot be imported into this item: `import_direction.py may` reports that
each already reaches the item and would close a cycle. The new affine step is a
smaller independent entry point into the affine construction. Its proof in words
uses the existing flatness and affine acyclicity declarations and explicitly
spells out the pinned mate calculation that must be proved. The union and stalk
steps retain the original route through relative Mayer--Vietoris and localization.

LeanSearch was unavailable (Internal Server Error) for every query; those records
are failures of that service, not absence findings. Loogle, Lean Finder and local
Mathlib/library/blueprint searches were also performed and recorded in the nodes.
The literature checkout is absent on this machine, so the Stacks pages for Tags
0A1D, 0DJ9 and 08DR were read online. The coordinate-expansion arguments are marked
agent-written in proof_origin, rather than claimed to be literal source proofs.
The existing unit `sk-thm-picard-coherence` has empty realized entries; it and its
statement and steps were left unchanged.

## New nodes

`def-pc-standard-single-flat-counit-presentation` defines the bounded flat sheaf
presentation with a canonical counit equation, before stalks, in
`Sheaf.AlgebraicGeometry.StandardSingleFlatCounitPresentation`.

`def-pc-standard-single-flat-counit-presentation-on-open` defines its property for
all relatively flat quasi-coherent modules on an open, in the same predicate module.

`lem-pc-standard-single-flat-counit-affine` is the affine initial case, in
`Sheaf.AlgebraicGeometry.StandardSingleFlatCounitAffine`.

`lem-pc-standard-single-flat-counit-union` is the two-open Mayer--Vietoris
construction from three presentations, in
`Sheaf.AlgebraicGeometry.StandardSingleFlatCounitUnion`.

`lem-pc-standard-single-flat-counit-localization` is base locality and
exact-stalk/counit transport from affine-base sheaf presentations, in
`Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalization`.

Every new node has the source, statement dependencies, complete proof steps (for
the theorems), actual search records, blueprint provenance and verbatim Lean
signature. No change record is needed because no existing interface changes.

## Second reading by R1

1. Interface: PASS. Compared the only existing delivered module by `diff -u`,
   then compared its declaration signature byte for byte with the repository.
   Only four private proof imports and the theorem proof were added. The existing
   docstring, universe binders, options and public imports remain unchanged.
   The other four modules and five definition/lemma nodes are new. No target or
   existing definition changes; no adaptation or change record is required.

2. Proof and axioms: PASS as a decomposition. All five modules compile in import
   order using `lcompile.py --all`, without errors or warnings. A scratch copy
   with explicit `#print axioms` probes for all six delivered declarations shows
   only `propext`, `Classical.choice` and `Quot.sound` on the two Prop definitions;
   the original theorem and three named lower holes additionally use `sorryAx`.
   The only textual holes are the entire proofs of the three reported public
   theorems. No forbidden declaration or holed data construction occurs. The two
   predicates quantify over witnesses and select none. Thus the original hole
   is closed conditionally on three lower holes; net -2 is not a completed proof.

3. Lower statements: PASS. Read each predicate, theorem and natural-language
   proof and checked empty source/open, zero module, repeated covering opens,
   identity and nonflat base morphisms, and negative degrees. The affine theorem
   restricts the geometry; the union theorem assumes exactly the three smaller
   presentations and retains their direct-image isos, permitting transport of
   restriction arrows; localization assumes the affine-base presentation, not
   the desired stalk coordinates. None is an unconditional restatement of the
   original item. The universal scalar pair is used only inside the existence
   proof. Independent Lean Finder, Loogle and grep queries, recorded in the new
   nodes, and reads of the relevant upstream/library statements found no direct
   replacement or lower hole closable by a short application.

   Checked the mathematical route against Stacks
   [0A1D](https://stacks.math.columbia.edu/tag/0A1D),
   [0DJ9](https://stacks.math.columbia.edu/tag/0DJ9) and
   [08DR](https://stacks.math.columbia.edu/tag/08DR).
   These support flat base change and source-open induction; the coordinate
   expansions are correctly marked agent-written rather than literal quotations.
   Clarified the union proof: projective chain-map lifting occurs in modules over
   the affine section ring, followed by sheafification, not by assuming free
   quasi-coherent sheaves are projective in the category of all sheaves.

4. Route and pruning: PASS. Read the actual induction and its compactness and
   quasi-separatedness instances. It supplies affine and union premises and
   applies the existing open-induction theorem to the compact top open. The
   unit `sk-thm-picard-coherence` has empty realized entries and is unchanged;
   the chapter/unit route through affine computation and Mayer--Vietoris stays.
   Removed the four redundant imports listed above and recompiled. No original
   dependency is geometrically pruned. Independently confirmed source import
   paths from the three affine Cech mate/exchange candidates back to this item,
   preventing their use here. The existing affine acyclicity module also reaches
   this item through an unrelated public finiteness import in the upstream
   AffineMorphism module: its theorem is already proved, but using it in the
   eventual affine proof requires upstream import separation. This is an import
   organization limitation, not a missing mathematical acyclicity argument or
   a cycle in the new DAG proof dependencies; no workaround was introduced.

5. DAG: PASS. Read all six delivered node files. Their Lean names and signatures
   match; every proof dependency is exactly the union of step uses and every
   referenced node exists. The original proof record follows the actual
   localization-plus-open-induction proof. The new nodes carry sources,
   provenance, chapter/unit, three search methods and complete proof plans.
   Updated the union node to match the corrected projective-module explanation.

Changes by this reader: four redundant imports removed; union docstring and node
clarified; independent search evidence and this review added. No additional hole
was closed or added and no Lean statement or definition body changed.
