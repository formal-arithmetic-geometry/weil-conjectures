# Stage-1 report: lem-trf-surjective-qis-simplicial-group-trivial-kan

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-surjective-qis-simplicial-group-trivial-kan.json`: statement, split into an explicit indexing comparison and application of an existing same-tag theorem; Mathlib verdict no match.
- `citations.json`: five verbatim statement excerpts for the five step/node citations.
- `report.md`: this report. No new nodes or Mathlib leaves.

## Attachments

None. Searched the read-only slopmaster2 project source for the exact item tag, simplicial abelian groups and trivial Kan/fibration terminology. The hits concern Cech cosimplicial objects and a different model structure, not this theorem. The exact master source likewise gives no attachment. The item has no recorded Lean declaration or open Lean frontier. Nothing was compiled or written in either source checkout.

## WANTED

None: all mathematical source text used here is available.

## Errors and corrections

STATEMENT-DISPUTED: read literally, the imported differential formula at n=0 invokes a simplicial face d_0:X_0 -> X_{-1}, but a simplicial object has no degree -1 term or such face. This is a typing omission, not a counterexample to the intended theorem. I restricted the alternating-face formula to n>0 and explicitly set the degree-zero differential to X_0 -> 0. Stacks simplicial.tex, Section 0194 (section-complexes), lines 3613–3623, displays exactly the chain complex ending X_1 -> X_0 -> 0. No hypothesis or conclusion changed.

The existing node `lem-trf-simplicial-abelian-surjective-quasi-iso-boundary-lifting` already states the same Stacks 08P1 theorem, using nonpositive cochain indices rather than nonnegative chain indices. This delivery reuses it, as the brief requires for existing duplicates. It does not introduce a new node for an equivalent clause or transfer the proof into a freshly created restatement. The maintainer may later consolidate these two existing ids; neither the other node nor its users were edited here.

## Unfinished work

None for this split. The cited, pre-existing boundary-lifting theorem is unsplit and remains the existing queued mathematical input. This delivery does not claim to have proved that theorem in Lean or to have completed its own split as a separate item.

## Not duplicates

No new nodes. Existing pair: `lem-trf-surjective-qis-simplicial-group-trivial-kan` vs `lem-trf-simplicial-abelian-surjective-quasi-iso-boundary-lifting`: mathematically identical after r=-n, as proved in Step 1. The latter is cited instead of duplicated. Searches of the whole DAG for 08P1 and simplicial abelian groups found this pair; blueprint_refs searches for 'simplicial abelian', 'Kan fibration', and '08P1' found no imported blueprint theorem to replace them. The ancestor command confirms `lem-trf-local-term-locality`; the existing precise from.place and via list are retained, and same_as is [].

## Mathlib searches

All five new searches were run with the required msearch.py Q72/item command, and their unaltered summaries/digests are retained in searches.jsonl and in the item. The two LeanFinder phrasings address both surjective quasi-isomorphisms and acyclic kernels. I read all hits returned by LeanFinder, LeanSearch and Loogle. Loogle returned zero hits. LeanSearch returned boundary and generic homology lift constructions. The first LeanFinder returned SSet horn-fibration definitions and unrelated surjectivity results. The second returned generic projectivity lifting, simplex-category epimorphisms, injective-kernel complex predicates and DoldKan projections. None has the required simplicial-abelian-group hypotheses and boundary-lifting conclusion. The grep returned only NCompGamma.lean:60–65, where surjectivity refers to maps of finite ordinals. I read that source at lines 40–76 and CategoryWithFibrations.lean at lines 35–105. No service was unavailable. The inherited earlier grep record was retained unchanged, not claimed as a newly run query.

## Review by Q72

I read coord/brief-stage1.md, stages/1-dag.md, the three blueprint levels in SETUP.md, GOAL.md, coord/dag-sync.md, the worker role, the chapter and unit records, and delivery-errors B–E. This item is an auxiliary input to the already recorded cotangent-complex branch; it is not the unit's key node and requires no realized-field change. Reusing the theorem already in the same unit leaves the route intact. No SGA source is used.

For the item I read Stacks simplicial.tex, Tag 08P1 (lemma-qis-simplicial-abelian-groups), its full proof at lines 5837–5881, Section 0194's associated-complex construction at lines 3608–3639, and Definition 08NL's full boundary-lifting definition at lines 5514–5545. I checked the tag/label mappings in tags/tags. The source itself reduces to the kernel, uses Kan filling and normalized-complex acyclicity; I did not create additional nodes for those facts because the existing same-tag node already supplies the whole theorem. There are no new nodes whose sources need independent auditing. The indexing comparison here is agent-written and proof_origin says so.

For Step 1 I opened the complete statement of the boundary-lifting node, including its explicit terms s(X)^{-n}=X_n, alternating differential for n>0, zero positive terms, and definition of quasi-isomorphism. I also opened both homology-definition nodes. The chain homology formula has kernel d_n modulo image d_{n+1}; the cochain formula has kernel d^r modulo image d^{r-1}. At r=-n these are literally the same two homomorphisms. Their induced maps send [x] to [f_n(x)] in both conventions. The entire comparison is this elementary substitution, with no normalization theorem, derived equivalence, sign shift or exactness lemma hidden in it. The cited derived-category node is used only for its explicitly stated cohomology/quasi-isomorphism definitions, not for its attached Lean declaration. Step 1 is under 2000 characters.

For Step 2 I reopened the boundary-lifting node's statement, rather than relying on its proof: it assumes precisely simplicial abelian groups, degreewise surjective component maps and quasi-isomorphism of the specified complexes, and concludes fillers for all boundary squares, with degree 0 explicitly included. The given f already satisfies the first two assumptions; Step 1 gives the last. I opened def-weil-pbc-trivial-kan-fibration: it asks for surjective vertices and boundary fillers for n>=1. The n=0 empty-boundary filler is a preimage of any specified vertex. Thus every part of the conclusion is supplied by the cited statement. This is the only non-elementary input, and it is an existing node cited explicitly in both proof_deps and uses. Step 2 is also under 2000 characters. All five quotes in citations.json were tested as verbatim substrings of the corresponding node statements.

I tested degree 0: H^0 is X_0/im(d_1), the incoming differential is unchanged, and the outgoing differential must be zero. For positive cochain degrees both terms and cohomology are zero. For the identity map and for zero simplicial groups the indexing equations and lifting conclusion are immediate; for constant simplicial abelian groups a quasi-isomorphism forces the degree-zero map to be an isomorphism, consistent with boundary lifting. No added hypotheses, multiplicative structures, finiteness or injectivity assumptions enter the application.

Against B–E: no new node can be non-self-contained, duplicate, elementary or a restated clause; the two actual proof steps use exactly the statements cited; every non-elementary input is named; the pre-existing cited theorem has no proof edges and its statement dependencies do not refer back to the item; there is no self-citation or intended cycle. I corrected the degree-zero typing omission and verified the source's conventions rather than importing an unmentioned face map. The dry run will check graph closure and route metadata independently on the server.
