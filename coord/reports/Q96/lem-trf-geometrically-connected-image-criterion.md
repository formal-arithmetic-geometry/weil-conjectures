# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-geometrically-connected-image-criterion.json`: statement, split into seven steps; Mathlib searches found no exact match.
- `citations.json`: verbatim statements for every node citation in every step.
- `report.md`: this report and signed review.

No new nodes; zero new Mathlib leaves. Search records are in `searches.jsonl`; `write_split.py` is sandbox-only working material.

## Attachments

None. Searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint tag, the id, geometric connectedness and its image criterion found no declaration with this statement. The project file `WeilConjectures/Mathlib/AlgebraicGeometry/Geometrically/Connected.lean` has a rational-section criterion and an open-immersion criterion, not this arbitrary-morphism criterion. Their extra hypotheses cannot be supplied here. The upstream master checkout is not used as evidence of a completed proof.

## WANTED

None. The Stacks sources used are present locally.

## Findings and changes

The item statement agrees with Varieties Tag 056R, `lemma-geometrically-connected-criterion`: arbitrary schemes over an arbitrary field, a morphism over that field, geometrically connected source, connected target. There is no surjectivity, dominance, finite-type or quasi-compactness hypothesis. Connected means nonempty, as the existing definition explicitly states; this is essential.

The initially empty proof is replaced with the Galois-intersection argument underlying the source's reference to Tag 038C, `lemma-tricky`. I use the already existing Tag 0389 finite-separable test first, and a finite Galois extension containing that extension. Consequently the intersection in 038C is finite globally; there is no unjustified infinite intersection of opens and no implicit assumption that X is quasi-compact or quasi-separated. The partition, its invariance, and nonemptiness of both descended parts are proved in the item's steps. This is an agent-written finite-case expansion of the source argument, recorded as such, rather than an assertion that the source prints these seven steps verbatim.

The blueprint's nearest ancestor remains `lem-trf-local-term-locality`, via the existing alteration/component chain. I read the chapter `sec-trace-formula` and unit `sk-i-curve-zero`, their current realization, the current blueprint ancestor, and the immediate parent `lem-trf-connected-point-geometrically-connected`. This item is a generic geometric tool used in that parent's Tag 04KV argument, not a new proof route for the contracting-local-term unit. The inherited blueprint location is already specific and is retained. Searching the whole blueprint for geometric connectedness and the criterion name found no other blueprint node with this statement. No unit realization is changed: this item is not the unit key node.

Three off-unit statements are declared in `split_report.tool_uses`: the finite-separable test, a finite Galois extension receiving a finite separable extension, and invariant closed-set descent. They are generic black-box tools, and the local-term unit contains no substitutes. The remaining off-unit citations are definitions or Mathlib leaves.

I searched the existing DAG by the Stacks labels/tags and geometric-connectedness, field-extension, Galois and surjectivity terminology; in particular, the existing 038B and 0389 nodes already supply the non-elementary inputs. No new node is needed. All original fields, statement and statement dependencies, ancestry, inherited searches and audit data are preserved. New actual searches are appended. The two LeanFinder phrasings and LeanSearch gave unrelated scheme/morphism results; Loogle exposed the geometric-connectedness definition and basic properties, which I read in Mathlib. Neither that file nor the project extension file proves the criterion.

## Unfinished work

None at the level of this split. Existing dependencies retain their own statuses and proofs. No Lean was written and no compiler, Lake or local DAG/preflight checker was run.

## Review by Q96

I checked the item against the local Varieties text at 056R and its sole proof citation 038C, and read 038C in full. I also read the actual source statements of 038B (`lemma-closed-fixed-by-Galois`) and 0389 (`lemma-characterize-geometrically-disconnected`); the field-theory input is Fields 09DT (`lemma-normal-closure`), 0EXM (`lemma-normal-closure-galois`) and 09I1 (`lemma-finite-Galois`). Morphisms 01S1 (`lemma-base-change-surjective`) supplies stability of surjectivity. I opened every existing node cited by a step and copied its statement verbatim into citations.json; no step invokes a construction buried in another node's proof.

Step 1 uses the receiver lemma with a family of size one. Its statement gives a finite, separable, normal extension L/k and an actual k-embedding E into L, precisely what is needed. A unital field embedding is injective, so it supplies the L/E structure; no identity of abstract fields is presumed. The base-change definition gives the actual induced morphism f_L.

Step 2 applies the geometric-properties definition to T and the field extension L/k; the resulting connected T_L is nonempty. Thus X_L is nonempty without a separate claim about f being surjective. The field-extension-spectrum lemma and the base-change-surjectivity lemma give the two projections p and q; I checked the direction of both projections and used the iterated-base-change identification explicitly present in the base-change node's statement.

Step 3 uses only the connected-space definition and the functoriality stated in the spectrum and base-change definitions. The inverse images of a separation under f_L are a separation of T_L. The image is G-invariant because f is defined over k: the proof compares the two projections of the two composites, rather than asserting an unexplained transport. This yields that the same nonempty set S lies in every translate of A. Nothing here needs the image to be dense or closed.

Step 4 takes only finiteness of Aut(L/k) from the finite-Galois fixed-field node, whose statement expressly includes it. The intersection is finite and contains S, and its complement contains B. Translation permutes every index of the intersection, including in the opposite-group convention. This is an explicit finite set calculation, not a separately hidden geometric lemma.

Step 5 uses exactly the statement of the invariant-closed-subset node, twice: L/k is Galois and P,Q are closed and invariant. That node permits any degree, so finite degree is allowed. It returns closed sets with exact inverse-image equalities, not merely image inclusions. Surjectivity of p from step 2 then proves the disjointness and covering downstairs; the actual points in P and Q establish both nonemptiness assertions. Taking complements shows that the descended closed subsets are open. Thus the contradiction uses the given connectedness hypothesis on X, with no added condition.

Step 6 is the elementary two-inverse-images argument for connectedness under a continuous surjection. The projections are scheme morphisms, hence continuous, and q is surjective by step 2. Step 7 invokes the finite-separable test with Y=X, whose full quantified condition has been proved for the arbitrary E chosen in step 1. This is exactly its stated converse, not the algebraically-closed test applied to a merely separably closed field.

For small cases I checked L=k (the finite intersection has one factor), X or T a point, nonreduced schemes, positive and imperfect characteristic, and arbitrary non-quasi-compact schemes. The proof does not assume a perfect field. Empty T is excluded by geometric connectedness; if that nonemptiness were omitted, the empty source mapping to Spec C over R would give a counterexample. Empty X cannot receive a map from this nonempty T. The non-surjective case is allowed throughout: only the field-extension projections p and q are asserted surjective. No new statement requires a separate small-case audit.

Against delivery-errors B--E: there are no new nodes or relocated clauses, no proof inside an unsplit node, and no definitions introduced. Each non-elementary input is a cited existing statement with the correct hypotheses; each purely topological or functorial assertion has its argument written out. Every step is shorter than 2000 characters (the longest is 786); there is no long hidden comparison. The source argument is fully expanded in the item, not moved to a renamed copy of the criterion. The only alteration of the source's presentation is the explicitly reported finite-Galois reduction using existing 0389. No mathematical statement correction or dispute was necessary.
