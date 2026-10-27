# Q142 stage-1 delivery: lem-sfb-cubical-partition-graded-equivariance

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-cubical-partition-graded-equivariance.json`: completed split with six explicit elementary steps, no mathematical change to the statement; not a Mathlib leaf.
- `citations.json`: eight entries containing verbatim parts of the four existing dependency statements.
- `report.md`: this report. No new nodes and no new Mathlib leaves. No repository, launcher, chapter, unit or Lean files were written. `write_split.py` is only the sandbox-local preparation script; `searches.jsonl` is the search command's log.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact item id and the concepts `cubical`, partition diagonal, signed tensor and front/back faces. No project declaration states this lattice subset formula. Read `AlgebraicGeometry/ModuleCupAWComponents.lean`: its front/back maps concern cosimplicial sheaves on a scheme, not integral lattice cubes, so they cannot attach this item. No compiler or Lake command was run.

## WANTED

WANTED: an external reference giving the integral lattice cubical partition diagonal with the exact inversion sign and translation formula, for lem-sfb-cubical-partition-graded-equivariance. The current blueprint supplies the surrounding direct-image route, not this algebraic assertion. The construction here is explicitly agent-written. Stacks 00CW/00CX and 010V support only the elementary tensor and chain-complex notions, not the cubical diagonal.

## Corrections and scope

The live item was unsplit, with an empty proof and no Lean attachment. There was no earlier sandbox node, report or search log to resume. There is no released repair note for this item. Its mathematical statement, all four statement dependencies, inherited citations and historical Mathlib searches were retained. The source pointer was updated to `literature/blueprint/latest/` and the formerly missing proof was written out. There is no statement dispute or change in hypotheses.

Read GOAL.md, the three levels in SETUP.md, the chapter and unit records, and the current chapter, unit statement and direct-images proof under `literature/blueprint/latest/`. In the latest direct-images proof paragraph (3) the quasi-compact-open case goes through the recorded constructibility/coefficient comparison; there is no explicit cubical formula there. The split therefore does not attribute the formula to the blueprint. It supplies only the existing lower-level algebraic input, with the same inherited unit and chapter. The ancestor tool returns no imported ancestor for the existing creation chain; this null value and the chain were preserved, with a precise route description in `blueprint.from.place`.

## Searches and reuse

Before writing the split, searched the whole DAG and current blueprint for cubical, lattice and tensor-differential statements; ran `tools/blueprint_refs.py search` for cubical, lattice, and tensor differential and ran its ancestor lookup. Read the item and the parent `lem-sfb-integral-cubical-chain-diagonal`: the parent cites this item, so using its stronger conclusion would be circular. The boundary-expansion and counit-evaluation siblings concern the later chain-map and counit assertions. They are neither needed nor used here. No candidate justified a new node.

Ran the required msearch command for this item with two LeanFinder phrasings, Loogle, LeanSearch and a source grep, and read every returned hit. The semantic hits concern box-additive maps, standard/bar chains, abstract tensor signs or diagonal representations; none gives the signed cubical partition formula together with its translation equation. The grep's single hit, `GroupTheory/Perm/Cycle/Basic.lean:913`, concerns partitioning a square of a finite set into shifted diagonals, not cubical chains. The Loogle cubical query had zero hits. All newly recorded queries are exactly the queries in `searches.jsonl`; earlier item search records were retained as history, not represented as searches run by Q142. This item is not a one-line specialization of the returned hits.

## Not duplicates

No new nodes were created. The existing cubical-diagonal parent is strictly stronger and depends on the item; the other partition siblings address its boundary and counit clauses. Free extension, finite subset counting, tensor bilinearity, the four-term square-zero expansion and equality on generators were kept as steps, rather than repackaged as new nodes.

## Review by Q142

I read delivery-errors B through E in full and checked the split with the four cited statements open. I also read Stacks `algebra.tex`, definition-bilinear and lemma-tensor-product (Tags 00CW and 00CX, including the quotient-by-bilinearity construction), and `homology.tex`, section-complexes (Tag 010V). The free-module node itself expressly says that every element has a unique finite expansion, so no separate free-extension theorem is being silently imported. There are no new-node sources or unreviewed statements to check.

Step 1 uses exactly the universal property in `def-weil-pbc-module-tensor-product`: the displayed sum of two bilinear maps takes values in the two stated summands of total degree n-1. A finite-support family defines the direct sum, so componentwise summation needs no theorem about infinite convergence or tensor distributing over a direct sum. The domain degrees are fixed when checking bilinearity; the sign is consequently a scalar independent of x and y.

Step 2 uses the actual conclusion `partial_(a-1) partial_a = 0` of `lem-sfb-integral-lattice-cubical-contraction`, not its construction of a homotopy or its proof. The two tensor mixed terms have coefficients (-1)^(a-1) and (-1)^a; their cancellation is explicitly displayed, and the outer terms vanish by that cited conclusion. The tensor node explicitly says pure tensors generate, so equality there extends by additivity and finite support. The chain-complex definition node explicitly identifies this square-zero condition with being a chain complex. The calculation includes a=0, where dx=0, and zero source factors; no boundedness or flatness hypothesis is needed.

Step 3 has no cited theorem: selecting A determines its complement B, each coordinate independently has two choices, and |A|+|B|=|I| gives the degree. These are elementary finite-set calculations, not an appeal to a hidden partition theorem. Each generator image is a finite sum in a single total degree even though there are infinitely many lattice vertices.

Step 4 uses exactly the unique finite expansions in `def-weil-pbc-free-module`. The formula on the coefficients defines the extension, coefficientwise addition proves additivity, and the same expansion forces uniqueness. This both constructs the map and proves the claimed uniqueness without choosing unknown data from an existence theorem. An empty source basis gives the unique zero homomorphism, including negative n and n>r.

Step 5 again uses the free-module statement to construct the translation maps. The tensor node's universal property applies directly to the bilinear map (x,y) -> tau_w(x) tensor tau_w(y); no unsupported assertion that tensoring a translation is available is required. The calculation tau_w tau_z[v,I]=[v+z+w,I]=tau_(w+z)[v,I] uses commutativity of Z^r, and establishes the action identities. Summing on finite-support families constructs the action on T.

Step 6 writes out the entire translation equality on a generator. The index partitions and inversion signs depend only on I,A,B and stay fixed, while v+u_A+w=v+w+u_A. The free-module node's finite expansions then prove equality of the two homomorphisms on all elements. There is no unproved transport or compatibility with the differential: this item only needs a graded map, and no chain-map assertion is used.

As small cases, for r=0 there is one vertex, one empty partition with coefficient 1, d_T=0, and P(1)=1 tensor 1. For I empty in any rank the formula is [v,empty] tensor [v,empty], and both sides translate both vertices by w. For r=1 and I={1}, the two summands are [v,empty] tensor [v,{1}] and [v,{1}] tensor [v+u_1,empty], both with positive sign. For r=2, I={1,2}, the middle choices A={1},B={2} and A={2},B={1} have signs +1 and -1; translation changes neither. These checks agree with the stated inversion convention. For source degrees outside [0,r], P is zero even when T has nonzero terms in higher total degrees. The boundary a=0 in the tensor differential gives zero in degree -1 as required. These cases revealed no false statement or missing hypothesis.

No proof step exceeds 2000 characters (all are under 700), and none hides a separately named comparison or auxiliary lemma. All non-elementary input is the cited d-squared-zero assertion of the existing cubical-contraction node; the surrounding bilinearity, finite-support, sign and generator arguments are supplied explicitly. I corrected no mathematical claim and created no clause-restatement node. The only repairs to the imported material were filling the missing argument and making its agent-written provenance and current blueprint location explicit.

## Unfinished work

No stage-1 proof obligation remains in this item. Dependencies retain their own independent proof status. Lean formalization is outside this stage-1 brief. The external-reference request remains explicit and is not used as evidence for the proof.
