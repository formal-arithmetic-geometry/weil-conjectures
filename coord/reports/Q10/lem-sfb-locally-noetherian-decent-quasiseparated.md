# Q10: lem-sfb-locally-noetherian-decent-quasiseparated

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-locally-noetherian-decent-quasiseparated.json: item, statement unchanged, seven-step split following Stacks 0BB6. Mathlib verdict: no match for algebraic spaces.
- dag/nodes/sec-six-functors-basics/lem-sfb-flat-lfp-lqf-degree-superlevel-open.json: new statement-only node, Stacks 086R restricted to finite fibres, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-etale-affine-pairs-test-quasiseparated.json: new statement-only node, the etale-chart variant of Stacks 0AHR established in its proof, unsplit; no Mathlib match.
- citations.json: verbatim statement quotations for every step/node pair.
- searches.jsonl: the actual msearch log, retained unchanged. The JSON records copied to mathlib_searches identify the tool, exact query, count, returned declarations and response digest. All services answered.

Two new nodes, zero Mathlib leaves. No Lean source was written or compiled. Only this sandbox was written.

## Attachments

None. Searched WeilConjectures/ for the item id, its blueprint docstring tag, decency, locally-Noetherian/quasi-separated assertions and degree/openness terminology. The locally-Noetherian scheme instance occurs in existing proofs, but no project declaration states the algebraic-space item. FiberDegree.lean and FlatFpLqfMaximalDegreeLocus.lean concern finite degree and the maximum locus with an already supplied bound, not unrestricted superlevel openness. No sorry-containing declaration was treated as finished.

## WANTED

None: all mathematical sources used are present in literature/stacks-project/.

## Corrections and scope

The imported item was statement-only. Its statement is correct and has been kept byte-for-byte, with its original stmt_deps. No STATEMENT-DISPUTED issue was found. Decency is already explicitly quantified over all field-valued maps, so finite fibres can be obtained directly by testing Spec(kappa(u)) against V. There is no need to introduce a residual-field monomorphism or to assume quasi-separatedness in order to bound fibres.

Stacks 0BB6 uses the separated hypotheses of 086R and 07RY without spelling out why W -> U is separated. Step 1 now proves that from the monomorphism W -> V x_Z U and the closed-diagonal conclusion of the existing monic-diagonal-tests node, using separatedness of the affine source V. The source's final displayed coproduct is used only as a partition of points; step 7 proves compactness by pulling back covers to the strata, without claiming the strata form a scheme coproduct or are open-and-closed.

The source's bounded-stratification input 07RY already has a node; it is reused rather than recreated. In particular, the existing maximum-degree-locus theorem, which assumes a uniform bound, cannot be used circularly to produce that bound. The new 086R node supplies the missing openness before a bound is known.

The blueprint ancestor command reports null for this inherited created-node chain. Its explicit historical provenance and via list are retained and extended for the two new nodes. I read the current latest blueprint unit and the direct-image proof: the item remains a geometric descent prerequisite of the existing alteration branch of det-thm-sf-ctf-stability-direct-images (3). Neither the chapter nor the unit route or realization was changed; this is not the unit's key node.

## Not duplicates

lem-sfb-etale-affine-pairs-test-quasiseparated vs lem-sfb-locally-noetherian-decent-quasiseparated: the new theorem is a general test criterion for arbitrary algebraic spaces, with no local Noetherianity or decency, and proves no chart product compact. The item proves those chart products compact from its substantive hypotheses by the generic-degree bound and stratification argument. The criterion merely turns that separately proved compactness into diagonal compactness; it does not restate the implication being split. Its secondary 0BB6 source citation identifies where that generic criterion is invoked, not a second proof of the item.

lem-sfb-etale-affine-pairs-test-quasiseparated vs def-sfb-space-absolute-quasi-separated: the existing definition tests ALL affine scheme maps to X; it does not assert that one may restrict those maps to representable etale charts. The new theorem is the descent criterion for that restriction, extracted from the proof of 0AHR, with no Noetherian or decent hypothesis.
lem-sfb-etale-affine-pairs-test-quasiseparated vs lem-sfb-space-qs-atlas-criterion: the existing sufficient criterion requires one surjective scheme atlas U -> X with U quasi-separated and U x_X U -> U quasi-compact; the new criterion tests separate affine etale pairs and does not presuppose a quasi-compact atlas projection. Neither finiteness of such an atlas nor its projection's quasi-compactness is available here.
lem-sfb-flat-lfp-lqf-degree-superlevel-open vs lem-weil-pbc-flat-fp-lqf-maximal-degree-locus: the existing 07RY lemma assumes a global bound m and treats only the degree-m locus. The new 086R lemma assumes only that individual fibres are finite and gives every superlevel open, which is needed to construct the bound.
lem-sfb-flat-lfp-lqf-degree-superlevel-open vs lem-weil-pbc-flat-fp-lqf-bounded-stratification: the latter assumes a uniform fibre-degree bound and gives finite-locally-free strata. The new lemma precedes that bound and has a different conclusion. The existing stratification is used in step 4, not duplicated.

Before creation I searched all DAG nodes for 086R, 0AHR, the source labels, fibre-degree/open-locus wording and affine-etale quasi-separatedness tests; blueprint_refs search also found no imported node for either fact. Only the definition above shares source tag 0AHR. Mathlib searches used two semantic phrasings per new node, Loogle, grep, and LeanSearch. The degree searches returned flat universally open maps, openness of the etale locus, generic semicontinuity definitions, and locally constant rank of a finitely presented flat module. Reading the source showed the first two are different assertions and the module theorem has a finite-module presentation unavailable for this possibly non-quasi-compact morphism. Scheme quasi-separatedness and affine-target constructors do not state algebraic-space chart descent.

## Review by Q10

I read the complete proof of Stacks decent-spaces.tex Tag 0BB6, more-morphisms.tex Tags 086R and 07RY (their statements, the superlevel argument, and the bounded-degree stratification), and spaces-properties.tex Tag 0AHR (all three conditions and its descent proof). For the new degree node I retained every hypothesis required by 086R, including separatedness and local finite presentation, and restricted to finite fibres to state ordinary integer degree without an infinite-degree convention. For the new etale-pair node I checked that the proof of 0AHR uses only affine open pieces of an etale atlas; it really proves this variant, although condition (3) is phrased for arbitrary affine maps. Both new nodes have statements only, no proof steps or proof dependencies.

Step 1 uses def-trf-algebraic-space for representability and the etale scheme test, def-weil-etale-morphism for flatness, local finite presentation and unramifiedness, and unramified-quasi-finite-at-points for local quasi-finiteness. The affine-source separated lemma applies to V -> Spec Z. I checked monic-diagonal-tests with X=V, T=S=Spec Z, B=U and Y=W: its monomorphism condition follows because X in the item is a sheaf of sets, and its conclusion is exactly closedness of the diagonal of W/U. This supplies separatedness without assuming the item's conclusion. I replaced an implicit affine-to-affine inference with the more direct existing affine-source separated node.

Step 2 applies the stated decency hypothesis to the actual composite Spec(kappa(u)) -> X and the actual affine test V. It obtains quasi-compactness of precisely W_u. The etale-fibre node states the disjoint spectra of finite separable extensions, and the finite-affine-coproduct-spectrum node identifies their finite union with the spectrum of their product. Compactness makes the component family finite; a finite product of finite-dimensional vector spaces has finite dimension. The empty product is the zero algebra and gives the empty fibre. This is not an application of the bounded-chart lemma, which would require quasi-separatedness and be circular.

Step 3 uses the affine compactness leaf and the chart hypothesis to make U Noetherian. The cited finite-components leaf, component-coverage leaf and scheme-sobriety node respectively supply finiteness, coverage and generic points, each read from its statement. The new degree-superlevel lemma applies with all hypotheses from steps 1 and 2. If an open set meets a component, its generic point belongs to it; this follows immediately from density of the generic point. It proves that no fibre degree can exceed the finite maximum, including the empty-U convention n=0.

Step 4 uses the exact universal property in the existing bounded-stratification node, not an unstated construction from its proof. Its finite-fibre and uniform-bound assumptions are now available. I added reduced-induced-closed-subscheme explicitly for the structures on the closed subsets. The open strata carry their usual open-subscheme structures, so their images are exactly the sets S_r and the universal property applies to their inclusions. There is no assumption that a finite partition is clopen.

Step 5 expands the Noetherian compactness argument from the minimal-condition node: complements give maximal members of any family of opens, then maximal finite unions show every subspace is compact. In particular the locally closed S_r have compact underlying spaces. This is an elementary finite-cover argument from the quoted statement, not a new lemma to queue.

Step 6 uses the definition of finite locally free to get finite, then the finite-morphism definition to get affine. The affine-open-basis leaf and compactness of S_r provide a finite affine cover. The affine-morphism permanence statement gives affine pullbacks, and the affine compactness leaf makes them compact. Combining their finite subcovers proves W_r compact. All cited clauses were read; no theorem about Noetherianity of a finite extension was silently used.

Step 7 combines the finitely many continuous images of the W_r by pulling back an arbitrary open cover, then applies exactly the new etale-pair criterion. The index set is 0,...,n and may contain empty strata; zero degree and empty X, U, V or W give the same proof. No finite type over a base, dimension bound, global quasi-compactness, separatedness of X, or restriction on its number of components was introduced.

I checked delivery-errors B-E against the files: each new statement introduces its objects and cites its notions; source places use checked Stacks tag/label pairs; all node citations have verbatim quotations in citations.json; no new node is a clause of the item, and the existing 07RY node is reused. No step is longer than 2000 characters (the largest is about 1100), and I reviewed their arguments for hidden facts. The separatedness, component-coverage, finite-product-spectrum and reduced-structure citations above are corrections made during this review. Both new facts are strictly smaller tools: neither includes the Noetherian/decent implication that the item's steps prove. No SGA source is used.

The off-unit declarations in split_report.tool_uses are generic scheme fibre, diagonal, reduced-structure and stratification tools, used inside the fixed 0BB6 argument; none replaces a step of the six-functor unit. The report requests the maintainer's routine assessment of those tool uses rather than setting maintainer-owned tool_uses.

## Unfinished work

No part of this one-level split is left unfinished. The two supporting statements remain unsplit by the worker contract and join the stage-1 queue. No WANTED literature or statement dispute remains.

## Validation

The preliminary server review_split check passed. Final full dry-run and direct-delivery results are recorded by the delivery tool.
