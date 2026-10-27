# Stage-1 delivery: lem-sfb-noetherian-space-chevalley-image

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-noetherian-space-chevalley-image.json: item, split with six proof steps; statement and statement dependencies unchanged; not a Mathlib leaf.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-constructible-affine-etale-test.json: new statement-only, unsplit geometric lemma; no Mathlib match.
- citations.json: eighteen citations, each quoting the cited statement verbatim.
- searches.jsonl: actual msearch output log; write_split.py: sandbox-only JSON generation script; report.md: this report.

## Attachments

None. I searched the whole live lean/WeilConjectures tree for the item tag and algebraic-space terminology, as well as the algebraic-geometry and six-functor directories for constructible images and Chevalley. There is no project declaration establishing this algebraic-space assertion. The actual Mathlib scheme theorem is AlgebraicGeometry.Scheme.Hom.isConstructible_image, Mathlib/AlgebraicGeometry/Morphisms/FinitePresentation.lean:165-169, already carried by lem-weil-pbc-chevalley-constructible-image. It is used through that existing leaf.

## WANTED

None. All mathematical sources read are in literature/stacks-project/.

## Findings and changes

The imported item is true as written and is not statement-disputed. Its proof was empty. I retain its separatedness hypothesis, although the atlas argument only uses the stated finite-type condition and the target hypotheses. I do not add source quasi-separatedness or properness. In particular, I do not assert that an arbitrary continuous map preserves constructibility: inverse images of finite unions of locally closed sets are constructible here only after proving the source chart is Noetherian.

The item cited 0ECX and 06G4 as sources. Rather than introducing a second node that restates the algebraic-space Chevalley conclusion, the proof performs the affine-atlas argument of 0ECX. Local finite presentation is obtained separately on each scheme map by pqf-lem-lft-fp-locnoeth; no unnecessary global finite-presentation or source quasi-separatedness assertion is used. A new lemma is needed only for 0ECZ, the comparison of topological constructibility with affine etale tests.

I read the current chapter and unit records and the newest blueprint file literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3). This is a supporting Chevalley tool below the incidence-space argument described by the item's inherited blueprint.from.place, rather than a replacement of any unit step. I changed no chapter or unit file.

The read-only command tools/blueprint_refs.py ancestor reports a null ancestor for this item. Following created.item explains it: the chain ends at lem-sfb-admissible-direct-image, created for a Lean module string rather than a DAG id, although that root's own blueprint.from.node records det-thm-sf-ctf-stability-direct-images. I preserve the existing null ancestry and put exactly that computed null in the new node; its via list prepends this item to the inherited list and its place names the actual supporting input. No immutable ancestry record was repaired or invented. The item and new node have same_as=[] following the whole-blueprint searches for Chevalley, constructible subset, etale locally constructible, and 0ECZ. The blueprint's affine-over-a-field Chevalley node is not the same assertion.

## New node and searches

lem-sfb-space-constructible-affine-etale-test states a general test for subsets of a qcqs algebraic space: constructible in its point topology if and only if every affine etale scheme test has constructible inverse image. It does not mention a finite-type morphism or its image. I read decent-spaces.tex 0ECZ (lemma-locally-constructible), including both directions and the entire quasi-compact reduction and finite-stratification argument. The reverse-direction proof explicitly proves global constructibility when X is qcqs. I also read spaces-properties.tex 0ECT (lemma-locally-constructible), its three equivalent conditions and their proof, and 0ECU (definition-locally-constructible); 0ECT(2) is exactly the affine test. These sources justify the new node without silently equating two notions of constructibility.

Actual msearch queries used both a description of affine etale detection and the alternative description comparing etale-local and topological constructibility; all four search methods were run. The search records are copied from searches.jsonl, not reconstructed. Loogle and the grep of Topology expose ordinary topological constructibility; LeanFinder and LeanSearch expose scheme Chevalley, scheme preimages and topological gluing, but no algebraic-space comparison theorem. The grep in AlgebraicGeometry finds only the scheme image declarations and no AlgebraicSpace declaration. I read FinitePresentation.lean:165-173 and Topology/Constructible.lean:374 onward to confirm that none of these is an algebraic-space comparison in one specialization. Thus the new node is unsplit, with empty proof and proof_deps. The item's earlier logged searches were preserved and the searches from this attempt appended.

## Not duplicates

lem-sfb-space-constructible-affine-etale-test vs lem-sfb-noetherian-space-chevalley-image: both cite 0ECZ, but the new statement is an atlas detection criterion for an arbitrary subset of a qcqs space; the item is a theorem about images under a separated finite-type map with Noetherian target. Neither the new statement nor one of its clauses asserts constructibility of such images.

The whole DAG source-tag search for 0ECZ, 0ECT and 0ECU found only the item before this delivery. Keyword and blueprint searches also found no existing atlas constructibility criterion. I examined the existing affine-over-a-field Chevalley node, the general scheme Chevalley leaf, and the point/atlas/open-image nodes: the first two concern schemes; the latter concern openness or point lifting and do not state a constructibility criterion. These were reused where they actually apply.

## Review by NQ

I read coord/delivery-errors.md sections B through E in full, and checked the files against those substantive failure modes. The new node introduces S, X, the subset E and every affine chart; it defines quasi-compactness and quasi-separatedness and cites the actual definitions of spaces, points, spectra and constructibility. Its source has the Stacks tags and TeX labels. It has no proof or disguised proof in its statement. Its Mathlib records contain only executed searches. It is a genuine separate comparison lemma, not a relabelling of the image theorem. No new Mathlib leaf is claimed and no definition is hollow.

For step 1 I read the statement of lem-trf-space-fibre-products-etale-covers: it supplies the algebraic space W, not an invented assertion that its underlying points are a Cartesian product. Representable etale base change is checked directly on the scheme tests of def-trf-algebraic-space. Quasi-compactness of W is exactly the item's affine-test definition for f. The reference is the first paragraph of the proof of spaces-morphisms.tex 0ECX.

For step 2 I read def-trf-algebraic-space and the complete statements of lem-weil-pbc-etale-composition-cancellation and lem-a1-space-finite-affine-subatlas. The first provides a scheme atlas; the second states that open immersions are etale and that etale scheme maps compose, permitting affine refinement after scheme testing; the third really gives a finite subfamily of an atlas by disjoint affine schemes when the point space is quasi-compact. It is not being cited for local finite type. The latter is precisely the compatible etale chart condition in the item's finite-type hypothesis, applied to U_i and V. I read spaces-properties.tex 03H6 and its finite-subcover proof and used the finite-family construction, not the erroneous word 'finite' in its last sentence: the constructed map is etale surjective, not generally a finite morphism. Our node statements and proof make no such finiteness assertion about the atlas.

For step 3 I opened pqf-lem-locnoeth-lft, lem-sfb-noetherian-space-topology, lem-weil-pbc-affine-scheme-qcqs, lem-a1-space-point-open-calculus and def-weil-constructible-subset. The first is a theorem about scheme sources locally of finite type over a locally Noetherian scheme, so it applies to U_i over V and to every etale chart T of U_i over V. The scheme composition lemma ensures T is still an etale chart of Y. The topology lemma assumes quasi-compactness and local Noetherianity on charts, both now verified; it needs no separation. Affine quasi-compactness comes from its existing Mathlib leaf. The point calculus explicitly states continuity of every morphism. The constructibility definition explicitly gives both the finite locally closed decomposition and its converse under Noetherianity. Pulling back each open and closed piece gives the needed elementary argument, rather than using an uncited preimage theorem for spaces.

For step 4 I read pqf-lem-lft-fp-locnoeth and lem-weil-pbc-chevalley-constructible-image. They really assert local finite presentation over a locally Noetherian scheme, and constructible images for a quasi-compact locally finitely presented scheme morphism into a qcqs scheme. Each h_i has these hypotheses. I wrote the quasi-compactness verification for affine-to-affine morphisms via principal opens, so no quasi-compactness of an arbitrary etale atlas map is assumed. The target is affine and hence qcqs by the cited existing leaf. I read the source proof of 06G4 and the scheme theorem at FinitePresentation.lean:165-169. The source subset A_i is constructible by step 3.

For step 5 I read again the actual point-calculus assertion: the point map of the fibre product is surjective onto the fibre product of point sets. It supplies the lift of a pair (y,t), not a bijection or a false set-theoretic Cartesian identification. Joint surjectivity of the finite atlas then supplies u. I wrote both containments of the image equality. Only finite union closure is taken from the constructible-subset statement. This is exactly the point identity in the proof of 0ECX, citing spaces-properties.tex 03H4.

For step 6 I checked that the new lemma says precisely the affine-test criterion used, and that the target is both quasi-compact and quasi-separated by the hypotheses already in the unchanged item. The all-space subset is constructible directly from the definition: the whole space is open and retrocompact in itself, without needing source quasi-compactness for that observation. This proves the 'in particular' clause as well.

Small cases checked: A empty, Y empty, W empty with an empty finite atlas, Z empty, identity morphisms, a closed immersion, and non-surjective charts. The point lifting proof handles all of these without selecting a point from an empty set. For the new criterion, X empty and E empty or full satisfy both conditions; quasi-separatedness is retained exactly as in 0ECZ, and quasi-compactness is needed for the global conclusion. I did not extend it to an arbitrary non-qc space. I also checked a constant map from a positive-dimensional affine scheme: the atlas need not be a finite morphism, illustrating why the typo in the source of 03H6 must not be repeated.

C1/C4 audit: every non-elementary assertion used by the six steps is explicitly in a cited node's statement. Every such cited statement was opened and copied verbatim into citations.json; no quotation is bent to fit a use. The routine open/closed inverse-image argument, affine quasi-compactness check, finite unions and two image containments are written out. No step is longer than 2000 characters (the longest is 1010), and there is no 'standard identification' hiding a separate lemma. Generic off-unit point, atlas and Noetherian-topology tools are declared in split_report.tool_uses; no six-functor, trace-formula or purity theorem is used. No SGA source is used.

## Unfinished work

No missing part of the item's natural-language proof. The one new statement-only lemma remains intentionally unsplit for a later worker. No Lean was written, no compiler or build tool was run, and no repository or launcher file was modified.

## Validation

Server review_split and the required delivery dry run are being run; their final results will be recorded below before the actual push.

Server review_split exited 0 with PASS. The required deliver.py --no-push invocation exited 0: `OK (not pushed) deliver/NQ/lem-sfb-noetherian-space-chevalley-image at 17103048438: preflight passed`. The eighteen citation entries were independently checked locally for verbatim membership in the cited live/new statements. No repair was required by the dry run. A final dry run follows this report update before the push.
