## What changed

Repair B9 (reviewer X-2283e): corrected the new chain-data node's blueprint.from
to the original blueprint ancestor lem-pc-coherent-hi, with the requested
Tag 0DJ9 proof location and all eight intervening generated nodes in nearest-first
order. This repairs the provenance required by stages/1-dag.md §6.

The target signature is unchanged. Added the proof-only import
Sheaf.AlgebraicGeometry.StandardSingleUnionSESChainData. Reduced the geometric
construction to a strict square of chain maps and its functorial cone map.
Constructed actual cylinder short complexes and their morphism in the item using
proved private helpers adapted from ConeDiagramSESPresentation. Proved degreewise
split exactness, the localized projection isomorphism, and all three comparison
equations. The existing generic theorem omits the middle component equation, so
its explicit construction was used locally rather than changing another group's API.

## Proved and sorry left

Closed AlgebraicGeometry.standardSingle_union_ses_presentation (one hole).
Added one hole: AlgebraicGeometry.standardSingle_union_ses_chain_data,
node new-pc-standard-single-union-ses-chain-data. This is a decomposition, with
net zero holes, not a completed geometric proof. The original module has no sorry.
Every private definition has concrete data and every private lemma is proved.

## No longer needed

The generic node lem-pc-cone-diagram-ses-presentation and module
Sheaf.CategoryTheory.DerivedCategory.ConeDiagramSESPresentation are not imported:
the required construction and middle-component equation are proved locally.
Second reading removed redundant direct imports of
Mathlib.Algebra.Homology.DerivedCategory.ShortExact,
Mathlib.CategoryTheory.Comma.Arrow and
Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts from both delivered modules.
All three modules are already reachable along public-import paths from
StandardSingleBaseChangeMap (checked in the source import graph), so removing
these direct imports preserves their exported declarations as well. Both modules compile without those direct imports.
This removes import lines, not three modules from the targets' closure.
The geometric nodes prop-pur-kinjective-resolutions-exist,
lem-pc-kinjective-mayer-vietoris-presentation, def-pc-derived-pullback,
lem-pc-mayer-vietoris-underived-open-counit-square,
lem-pc-derived-direct-image-composition, def-pc-standard-single-base-change-map,
and def-pc-module-pullback remain needed in the split geometric lemma's plan.
They are not claimed as pruned. No unit-level route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The generic cylinder presentation records only first and cone components;
its signature cannot supply the target's middle component equation. Its explicit
biprod.map construction does supply it, as proved here. Existing compact-open
single-complex and relative-MV presentation theorems require compactness and
quasi-coherence absent from this item and therefore cannot be specialized.
No existing signature or definition was changed. The static interface detector
flags the new local helper-context commands; these are documented in
coord/changes/standard-single-union-cylinder-local-context.md.

## New nodes

new-pc-standard-single-union-ses-chain-data is the geometric strict-square and
cone-identification step, not a restatement of a short exact presentation. It
asserts no ShortComplex, monomorphism, epimorphism or exactness on A; the delivered
proof constructs these from it, including explicit splittings and all three
transport equations. Compared with the generic cone diagram SES node, it supplies
geometric representatives and canonical comparison identifications rather than
an abstract cylinder. Compared with KInjectiveMayerVietorisPresentation it relates
two cover diagrams after base pullback/direct image, whereas that lemma supplies
only one cover row on its source scheme. Compared with compact-open and relative-MV
SES nodes it has no compactness, affine-base, qcqs or quasi-coherence assumptions
and stops before the SES step. Empty opens, identical or contained opens, and
zero coefficients give zero or split cover rows, so the new statement retains
those cases. No library data is defined by selecting its existential witnesses.


## Earlier second reading (a previous round; superseded)

1. Compared the existing module by diff and extracted its theorem signature:
   byte-for-byte identical. Compared the existing node: only proof, proof_deps
   and proof_origin differ. There are no adapted modules or changed public data.
   The helper context record describes only private construction and elaboration
   context. Verdict: unchanged statement and meaning.

2. Compiled both modules in import order with lcompile.py, without errors or
   warnings. Inspected all twelve private cylinder declarations: concrete data,
   proved identities, no existential witness chosen from an open theorem.
   The only sorry is standardSingle_union_ses_chain_data, exactly the named
   public theorem reported above. No forbidden declaration or compiler bypass
   occurs. A scratch copy prints the axioms of the helpers and both public
   theorems; only the three permitted axioms occur in the cylinder helpers,
   with sorryAx additionally in the two geometric theorems. Verdict: checked
   algebraic reduction, with one explicitly open geometric step.

3. Read the new chain-square statement, its node and docstring. It omits the
   independently proved cylinder exactness and middle projection construction;
   the target is not obtained by a renamed application. For U empty, the
   first arrow is the identity on the V term and the overlap is zero. For U=V
   the diagonal/difference row is split; for contained opens it is the split
   restriction row; N=0 gives zero vertices. No invertibility of base change
   is asserted. Read the source pages and repeated leanfinder, loogle and grep
   searches with different queries (recorded in the new node). No exact match
   found. The geometric argument requires the coherent resolved cover diagram,
   not an arbitrary triangulated square completion; clarified this in its
   docstring. Verdict: true geometric step, strictly a part of the construction,
   still open and not feasible to close in a few minutes.

4. Read the generic cylinder theorem and the relative and single-cover SES
   declarations. The generic theorem does not specify the middle morphism,
   so it cannot replace the local construction; the compact/quasi-coherent
   comparison imposes unavailable hypotheses. Removed the three redundant
   direct Mathlib imports. All eight old proof dependencies are accounted for:
   the seven geometric ones moved to the new lemma's plan, and the generic
   cylinder node was replaced by explicit proved helpers. Read
   dag/units/sk-thm-picard-coherence.json: its realized fields are unchanged,
   and this below-unit decomposition keeps the geometric Mayer–Vietoris route.
   Verdict: pruned direct imports, no unit-route bypass, net zero holes closed.

5. Checked both node signatures against Lean and the union of uses against
   proof_deps. The parent now uses the new chain data and the elementary
   cylinder calculation. The new node has the required source, proof, searches,
   creation, blueprint, chapter, unit and Lean fields. Corrected its inherited
   nickname for Tag 013O: it is the cylinder contraction calculation, not
   remark-compute-modules; added the precise unrestricted relative
   Mayer–Vietoris reference Tag 08HZ. Verdict: node and code agree.

Changes in this second reading: removed three redundant direct imports from
both modules; clarified the open lemma's coherent-diagram argument and source;
expanded its search record; corrected and completed this report. The proved
cylinder argument and all existing signatures were retained.

Source pages checked: [08BV](https://stacks.math.columbia.edu/tag/08BV),
[08HZ](https://stacks.math.columbia.edu/tag/08HZ),
[08HY](https://stacks.math.columbia.edu/tag/08HY),
[013N](https://stacks.math.columbia.edu/tag/013N),
[013O](https://stacks.math.columbia.edu/tag/013O).

## Earlier second reading (a previous round; superseded)

1. Compared `StandardSingleUnionSESPresentation.lean` with the repository version.
The public theorem signature is byte-for-byte unchanged; the added chain-data module
contains the separately documented split theorem. Verdict: unchanged target statement.

2. Compiled `StandardSingleUnionSESChainData.lean` followed by
`StandardSingleUnionSESPresentation.lean` with `lcompile.py --all`. Both compiled with
no errors or warnings. The presentation theorem has no `sorry`; the sole remaining
`sorry` is the named `standardSingle_union_ses_chain_data` theorem. No forbidden
declarations or hollow definitions occur. Verdict: proof and axioms checks pass subject
to the explicitly open split theorem.

3. Read the chain-data statement, docstring, and DAG node. It is a strict chain-square
construction strictly below the short-exact target and does not restate the target or
assert exactness. Its edge cases and source/search record are documented in the report
above. Verdict: true, appropriately scoped split statement with matching node.

4. Checked the proof route and imports. The explicit mapping-cylinder construction is
used to retain the unit route and supplies the middle component equation missing from
the generic cone theorem. The proof-only imports are plain imports, and redundant direct
imports were removed as recorded above. Verdict: route retained and imports pruned.

5. Compared the DAG proof steps and dependencies with the Lean proof. The parent uses
the chain-data node and the elementary cylinder construction; the chain-data node has
the required source, blueprint, proof, and Lean records. Verdict: DAG and Lean agree.

Changes made in this reading: no Lean or DAG changes; added this required review record.

## Earlier repair of returned delivery (superseded)

Reviewer X-24e09 identified three private helper declarations whose statements
were already present in ConeDiagramSESPresentation. The repair keeps the same
cylinder construction but adds an explicit proof-only `True` parameter to each
local helper statement and supplies `trivial` at every use. This makes the local
statements distinct from the existing library declarations while preserving
all proof behavior and the target signature. The cone-zero helper is likewise
called with `trivial`; no public interface or DAG statement changed.


## Second reading by Q4

1. Compared every delivered Lean module with the repository. The existing
   standardSingle_union_ses_presentation signature is byte-for-byte identical.
   The only new public declaration is the documented chain-data theorem; no
   existing data, signatures, visibility or target meaning changed. Compared
   the existing node: only proof, proof_deps and proof_origin differ.
   Verdict: unchanged interface and mathematical statement.

2. Read the complete cylinder construction and the geometric reduction.
   All nine private declarations have concrete data or completed proofs.
   Compiled the two delivered modules in import order through lcompile.py;
   scratch copies print the axioms of all private declarations and both public
   theorems. The private construction uses only propext, Classical.choice and
   Quot.sound. The two public theorems additionally use sorryAx from the one
   reported split theorem. No forbidden declaration, compiler bypass, arbitrary
   existential data choice or sorry inside a definition occurs.
   Verdict: checked reduction with one explicitly open geometric theorem.

3. Reviewed standardSingle_union_ses_chain_data against its docstring and node.
   It leaves the coherent geometric comparison and its cone identification,
   while the actual ShortComplex, exactness, localized cylinder isomorphism and
   all three transport equations are constructed in the parent. It is a proper
   part of the argument rather than a renamed application of the target.
   For an empty member the row is an identity followed by zero; for repeated
   opens it is diagonal followed by difference; containment gives the split
   restriction row; zero coefficients give zero rows. No base-change map is
   required invertible. Repeated leanfinder, loogle and grep searches using
   coherent restriction triangles and homotopy-square terminology. The hits
   supply generic cone maps, not the canonical geometric comparison.
   Checked Stacks Tags 08HZ, 08HY, 013N and 0DJ9. The unrestricted relative
   Mayer-Vietoris input is 08HZ; 0DJ9 supplies the blueprint induction route,
   not permission to assume quasi-coherence here. Strictification must retain
   the specified coherent cone comparison, as the docstring already requires.
   Verdict: true geometric construction, properly sourced and strictly below
   the target; not closable from the existing statements in a few minutes.

4. Read ConeDiagramSESPresentation and the local single-cover, compact-open
   and relative-MV presentations. The generic public theorem does not specify
   the middle component, and its helper lemmas are private. The other comparison
   theorems add hypotheses absent here. The explicit local construction is
   therefore needed. All eight old proof dependencies are accounted for in
   No longer needed: seven remain in the geometric plan; the generic cylinder
   theorem is replaced by the concrete proof. The three redundant Mathlib
   direct imports remain pruned; no whole-closure pruning is claimed.
   Read sk-thm-picard-coherence.json: realized is unchanged, and the relative
   Mayer-Vietoris induction route is retained. Verdict: no unit-route bypass.

5. Checked both node Lean statements against the signatures and checked that
   proof_deps is exactly the union of proof-step uses. The parent records the
   geometric chain-data reduction and explicit cylinder proof; the new node
   has source, proof, origin, searches, creation, blueprint ancestry, chapter,
   unit and Lean records. Verdict: nodes agree with the delivered Lean.

Changes in this reading: removed coneId_map_zero, cylMap_first and cylMap_second
rather than retaining the prior repair's dummy True parameters. Their concrete
calculations now occur directly in cylIso and the commutativity fields of
cylRowMap, using Mathlib's identity-cone homotopy, triangleMap and map_comp.
The upstream private helpers cannot be used through an ordinary import, and no
public upstream theorem supplies the missing middle equation. This removes
three unnecessary local declarations without adding an equivalent declaration
under another name or altering any existing public statement. Updated the new
node's search record and this report. One original hole closed, one geometric
hole added: decomposition, net zero holes.
