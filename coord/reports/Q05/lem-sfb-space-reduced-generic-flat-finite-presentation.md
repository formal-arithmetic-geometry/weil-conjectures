# Worker report: lem-sfb-space-reduced-generic-flat-finite-presentation

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-reduced-generic-flat-finite-presentation.json`: existing statement, unchanged; five-step split following Stacks 06QS.
- `dag/nodes/sec-six-functors-basics/lem-sfb-reduced-affine-generic-flat-finite-presentation.json`: one new statement-only node, unsplit; generic flatness for a locally finite type map between affine schemes over an arbitrary reduced affine target (052B). Mathlib searches found no match.
- `citations.json`: one entry per proof-step citation, quoting the actual statement of each cited node.
- `searches.jsonl`: actual msearch.py output records, retained as produced. `prepare.py` is a sandbox-only JSON preparation script, not part of the delivery.

## Attachments

None. Searched the project `lean/WeilConjectures/` for the exact blueprint tag, generic-flatness names, and reduced-base variants. The existing theorem `AlgebraicGeometry.exists_nonempty_open_flat_finitePresentation_restrict` in `AlgebraicGeometry/GenericFlatFinitePresentation.lean:45` assumes `IsIntegral` of a scheme base. It does not handle an arbitrary reduced base or algebraic spaces, so it is not an attachment to either delivered node. Mathlib predicates, smooth-implies-flat and descent results likewise do not construct the required dense open.

## WANTED

None. All mathematical sources needed here are present under `literature/stacks-project/`.

## Problems and changes

The item was unsplit and had no sandbox node or earlier report to resume. No repair note exists. Its statement agrees with Stacks 06QS and is preserved verbatim, with every statement dependency retained. In particular it says **locally** of finite presentation; it does not add quasi-separatedness or assert finite presentation for arbitrary algebraic spaces. The counterexample following 06QS explains why that distinction matters.

The latest blueprint unit and its direct-image proof were read in `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`. This is a supporting algebraic-space input far below the direct-image argument, not a replacement for that argument. The inherited blueprint ancestry is null: `tools/blueprint_refs.py ancestor` prints `None`. I preserve that computed ancestry, retain the full inherited chain, and give the precise 06QS affine-input place in the new node. Searches of the whole imported blueprint for `052B`, `generic flatness`, and `generic flat` found no matching blueprint statement; broader `reduced` and `flat` searches produced only other results. DAG searches by source tag, generic-flatness language and reduced affine schemes found the integral-base siblings listed below, not the required reduced-base input. A new node is therefore necessary.

The new node deliberately restricts **both endpoints to affine schemes** and contains no algebraic-space descent or global density argument. It is the scheme input in the last paragraph of 06QS, taken from 052B with the structure sheaf. A map between affine schemes is affine and quasi-compact, so its locally finite type hypothesis meets 052B's finite-type hypothesis. Its source statement has no proof sketch, its proof/dependency list is empty, and its statement dependencies introduce all the notions it uses. It will be split independently later; this delivery does not pretend to prove it.

Mathlib searches were run with msearch.py, using scheme, algebraic-space, reduced-ring and affine-scheme phrasings. All services responded. The new node records two scheme/affine phrasings, the reduced-algebra phrasing, Loogle's Flat/LocallyOfFinitePresentation pattern, LeanSearch and greps of both AlgebraicGeometry and RingTheory. The actual hits were read. Flat.lean:36–49 and FinitePresentation.lean:42–65 give predicates and locality; UniversallyOpen.lean:146–150 assumes flatness and local finite presentation. None is generic flatness. The two RingTheory grep hits (FreeCommRing.lean:40,83) use “generic” for generic polynomials. They do not concern generic freeness. Existing item searches were preserved, and the newly run searches were appended.

## Not duplicates

lem-sfb-reduced-affine-generic-flat-finite-presentation vs lem-sfb-space-reduced-generic-flat-finite-presentation: the new lemma concerns maps between affine schemes only. It supplies one chart calculation; the item's proof still constructs the target open, handles a possibly infinite atlas, performs source-and-target descent, and proves density on an arbitrary algebraic-space base. The two statements have different source tags, 052B and 06QS.

lem-sfb-reduced-affine-generic-flat-finite-presentation vs lem-sbc-generic-flat-finite-presentation: the latter assumes an integral scheme base and gives a nonempty open, whereas the new node allows an arbitrary reduced, possibly disconnected affine base and requires density throughout that base. The integral theorem does not specialize to this case.

lem-sfb-reduced-affine-generic-flat-finite-presentation vs lem-sbc-generic-flatness: the existing node assumes integrality and provides only flatness; the new node permits all reduced affine bases and also provides local finite presentation.

lem-sfb-reduced-affine-generic-flat-finite-presentation vs lem-trf-generic-flat-reduced-base-model: the existing node assumes an irreducible base and first changes it to its reduction; the new node neither assumes irreducibility nor changes the reduced base before taking a dense open.

## Review by Q05

I read `spaces-morphisms.tex`, Tag 06QS, label `proposition-generic-flatness-reduced`, its complete proof and the following warning about quasi-separatedness. For the new affine-scheme input I read `morphisms.tex`, Tag 052B, the statement and complete reduced-case proof (including its use of 051Z), and read the statement of algebra.tex, Tag 051Z. The generic-flatness source needs no Noetherian hypothesis. Reduced is not replaced by integral. The locally finite type affine-scheme formulation is valid because a morphism between affine schemes is affine, hence quasi-compact. I also checked `spaces-properties.tex`, Tag 03H6, for the affine source atlas, and the source-and-target/local flatness/local finite-presentation passages in spaces-morphisms.tex.

For step 1 I opened every cited statement. `lem-a1-space-affine-etale-cover` actually supplies the disjoint union of affine target charts and a surjection on point spaces. `lem-weil-pbc-open-immersion-etale` makes the summand inclusions etale; `lem-trf-space-representable-etale-scheme-tests` supplies composition. `lem-trf-space-fibre-products-etale-covers` supplies the algebraic spaces X_i. `lem-weil-pbc-affine-scheme-qcqs` gives quasi-compactness of each V_i, and `def-sfb-stack-qcqs-morphism` explicitly defines quasi-compactness by pullback over every quasi-compact algebraic space. Thus each X_i is quasi-compact in the atlas sense needed by `lem-trf-space-qc-finite-affine-atlas-refinement`. `def-trf-algebraic-space` supplies its initial atlas. The refinement lemma explicitly allows a non-quasi-separated space and the empty family, so no separation or nonemptiness enters at this step.

For step 2 the scheme-locality node explicitly says that locally of finite type is etale local on source-and-target. The presentation criterion says that the extended property holds for **every** presentation diagram, without requiring its target chart to be surjective. This is the precise fact needed for U_i → V_i; a weaker chart-test node requiring a globally surjective target chart would not justify applying it separately to V_i. The new node then applies with both schemes affine and V_i reduced, since V_i is an etale scheme chart of the reduced Y. I do not substitute an integral-base theorem here.

For step 3 `lem-a1-etale-scheme-map-open-image` gives the actual open image and factorization, and `lem-a1-space-etale-open-image` states the open-subspace/open-subset correspondence, which permits the union D. The scheme-test and fibre-product nodes say exactly that etale morphisms compose and remain etale under base change, and that an etale covering family remains a covering after base change. Each E_i is the pullback of the chosen **surjective** source atlas to D_i; the D_i cover D by construction. This proves joint surjectivity of E_i → X_D. It does not incorrectly factor arbitrary scheme maps through a closed subspace merely from point containment: D is an open subspace and all factorizations are those of the open-image or pullback constructions.

For step 4 I checked the actual scheme morphisms, rather than citing flatness's definition for a descent assertion. In an arbitrary presentation A → X_D, B → D, the schemes C_i=A×_(X_D)E_i and B_i=B×_D D_i exist by the scheme-source representability clause. The maps C_i → E_i and B_i → D_i are etale, so the scheme locality node transports P from E_i → D_i to C_i → B_i. The C_i → A jointly cover A. At each point of A the resulting square is the exact pointwise test (iii) stated in that same node. Thus A → B has P; the algebraic-space presentation criterion then proves P for X_D → D. Both P=flat and P=locally of finite presentation are explicitly listed in the scheme locality node. There is no invocation of fpqc descent on a non-quasi-compact cover and no hidden finite-presentation assertion. This step is an explicit application of the cited pointwise criterion, not a new independent comparison theorem.

For step 5 the atlas node explicitly provides continuity and surjectivity on point spaces. Pull back a nonempty open of Y to a nonempty open in some V_i, then intersect it with the dense D_i and map a point back. That is the complete elementary topological argument. No Noetherian space, finiteness of the atlas, or finite collection of irreducible components is used.

I checked edge cases: V=Spec(0), U empty, disconnected reduced affine targets, and bases with infinitely many components. Empty targets give an empty dense open and vacuous chart conditions; empty sources need no nonempty charts. For nonempty disconnected bases the new statement requires a dense open, not merely a nonempty open on one component. The proof makes a separate dense choice on every affine atlas component and takes their images, so infinitely many components do not require intersecting infinitely many dense opens. Non-quasi-separated sources remain permitted: no global finite presentation is asserted.

Against B–E: the only new node is self-contained and statement-only, with exact Stacks tag and label, complete definition dependencies, real recorded searches and no claimed Mathlib match. Searches preceded its creation; the four possible duplicates are distinguished above. Every non-elementary input is a cited existing node or the new affine input. `citations.json` quotes statements, not proofs, for all uses. No new node depends on the item. The proof is not relabelled 06QS: its atlas, open-image and descent arguments remain in the item. All five proof steps are below 2000 characters (693, 729, 867, 1089, 652 respectively), and none hides an uncited auxiliary lemma. Generic off-unit atlas and scheme-locality inputs are declared in `split_report.tool_uses` for maintainer review.

## Unfinished work

No part of this one-level split is left unfinished. The new affine-scheme theorem is intentionally an unsplit future item. No Lean was written or compiled, no git command was run in the shared repository, and all authored files are in the assigned sandbox.
