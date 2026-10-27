# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-inertia-etale-affine-charts.json: unchanged statement, six-step split following Stacks 0DUE; direct definition dependencies added for algebraic stacks, sizes, flatness and finite presentation.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-inertia-pointwise-groupoid-chart.json: statement-only, unsplit; no Mathlib match. Pointwise affine finite-flat groupoid chart, identifying one stabilizer.
- dag/nodes/sec-six-functors-basics/lem-sfb-proper-inertia-stabilizer-preserving-open.json: statement-only, unsplit; no Mathlib match. Open locus of stabilizer preservation with its inertia isomorphism.
- dag/nodes/sec-six-functors-basics/lem-sfb-flat-groupoid-quotient-open-presentation.json: statement-only, unsplit; no Mathlib match. Flat groupoid quotient, kernel pair, finite presentation and invariant open restriction.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-flat-affine-groupoid-separated.json: statement-only, unsplit; no Mathlib match. Absolute proper diagonal of a finite-flat affine groupoid quotient.
- dag/nodes/sec-six-functors-basics/lem-sfb-separated-source-finite-inertia-target.json: statement-only, unsplit; no Mathlib match. Separated-source cancellation using a separated target diagonal.
- citations.json: verbatim cited statements for every step/citation, including definitions. report.md: this signed review. searches.jsonl and search-*.txt retain the actual search records/results; scratch scripts remain only in this sandbox.

## Attachments

None. Searched project WeilConjectures/ by the blueprint tag, finite inertia, AlgebraicStack/algebraic stack, stabilizer preservation, groupoid and finite-flat charts. No project declaration states the item, let alone a closed proof. The InertiaIndEtale.lean hit is ring-theoretic inertia, not algebraic stacks. No Lean file was written or compiled.

## WANTED

None. All mathematical sources used are present in literature/stacks-project/. The inherited coord/dag-sync.md reference names a file absent from this read clone; the direct delivery tool supplies current live-base synchronization. No repository or launcher file was changed.

## Findings and route

The item is Stacks 0DUE in full, not just its Deligne--Mumford special case. Its statement is correct, and is preserved byte for byte. In particular finite inertia is not replaced by finite etale or smooth inertia. The existing lem-sfb-finite-inertia-local-affine-covers assumes Deligne--Mumford, so cannot prove this item. The existing invariant-open-substack-descent and smooth-groupoid-fppf-quotient require a smooth atlas/groupoid. A finite locally free groupoid is generally not smooth; I therefore supplied the general flat-groupoid presentation interface instead of citing either stronger-hypothesis statement. I did not duplicate the existing 03JE invariant-affine lemma or 01ZY common-affine lemma.

The current blueprint was read at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md (of=det-thm-sf-ctf-stability-direct-images), especially clause (3). Its current direct-image paragraph is shorter than the inherited long ancestry description. I retained the recorded ancestry as history and recorded the current place in split_report; no unit/chapter route or target was changed. blueprint_refs.py ancestor returns None for this created item, as it does for its existing neighbouring support nodes; new from.node values preserve that actual result. All new from.place fields name the exact sentences of the 0DUE proof they support.

Whole-DAG source/tag and keyword searches and whole-imported-blueprint searches were made before node creation: finite inertia, well-nigh, invariant affine, stabilizer, flat groupoid, separated inertia, invariant open, finite flat, separated stack, affine charts. No equivalent blueprint statement was found. The same-tag statements were opened; distinctions are below. The sources of generic 01ZY, finite-fibre and finite-affineness citations are tools rather than a change of unit route; requested tool uses are in split_report.tool_uses only, not the maintainer's top-level tool_uses.

The item's old recorded Mathlib searches are retained. Its concept was also searched afresh with the logged commands. For each new node a dedicated plain-language LeanFinder query, a differently phrased LeanSearch query, Loogle and source grep ran through msearch.py. The raw LeanSearch/Loogle/grep outputs are retained in search-*.txt; the initial LeanFinder hits were read and their actual names are summarized in mathlib_searches. Every recorded query is in searches.jsonl. All services responded. Hits concerned IsEtale and finite/proper scheme maps, ordinary categorical kernel pairs, topological stabilizers, or unramified algebra loci. They do not quantify over algebraic stacks or their groupoid presentations; none is a one-line specialization giving these statements. No Mathlib leaf is claimed.

## Review by Q76

I read stacks-more-morphisms.tex, labels lemma-etale-local-finite-inertia (0DUE), definition-well-nigh-affine (0DUL) and lemma-well-nigh-affine (0DUM), including their proofs, against the unchanged item. Its four chart conditions and affine finite-flat presentation match these sources, over a field as allowed by the general source. I also read stacks-morphisms.tex 0DU4, 0DUA, 0CL0(1),(5), 050M(3) and 0DTY(6); criteria.tex 06FH and 06FI; spaces-groupoids.tex 04M9; algebraic.tex 04WY; stacks-properties.tex 0507; and groupoids.tex 03JE and properties.tex 01ZY. These supply each new statement: the pointwise chart only preserves a single stabilizer, the open-locus theorem upgrades that to an inertia isomorphism, the flat quotient theorem handles the nonsmooth presentation, and the two separate diagonal results establish absolute then relative separatedness.

Step 1 uses exactly the new pointwise-groupoid statement, not 0DUE itself under a different name. Finite inertia implies the locally-quasi-finite separated inertia required by 0DU4 and its finite stabilizer assumption, via 0CL0 and scheme tests; this specialization is stated in the source field of the supporting node. The pointwise theorem supplies h and v but neither the global stabilizer isomorphism nor separatedness of h; those are proved later.

Step 2 uses the finite-target-inertia etale special case explicitly included in the open-locus node. It gives an open substack containing v AND the inertia isomorphism, not merely an open set of topological points. The quotient-presentation node states invariant-open correspondence and point lifting, so the lifted u exists and its entire orbit remains in the pulled-back open. The statement of finite-closed-map-finite-fibres gives finiteness of the actual scheme fibre of s; taking its image under t gives a finite orbit. No dimension, reducedness or closed-point argument is hidden here.

Step 3 uses def-pc-proj to check directly that Spec A is the sole standard chart of Proj A[T]. In 01ZY apply the existing locally-closed-Proj node to X=O=U-circle with the identity closed immersion; its finite set E is precisely the orbit from Step 2. No quasi-compactness of U-circle is needed by that statement. This avoids inventing a prime-avoidance or common-affine node. The existing 03JE node applies to the restricted groupoid because the presentation node explicitly preserves finite locally free projections under invariant restriction. Its conclusion supplies an affine W containing the orbit, not just u, with equality of the two open inverse images. These are exactly the claims used in the next step.

Step 4 uses the new flat-quotient node for the equivalence with an open substack, finite flat finitely presented cover, and kernel-pair identification. It uses the chartwise calculus node only for restriction of the given representable etale h; its statement allows checking on open sources and stability under base change. Restriction of inertia is elementary here because the open substack is strictly full: the automorphism group of every retained object is unchanged. The finite-morphism-permanence statement, clause (b), gives affineness of R_W from its finite projection to affine W. No assertion from the proof of a cited node is substituted for its statement.

Step 5 uses the proper-diagonal statement of the new finite-flat-affine-groupoid-separated node, applied to the actual W,R_W from Step 4. It then uses the new separated-source cancellation statement with A=X_x, B=X; its hypotheses are absolute separatedness of A and finite inertia of B, both verified. This distinguishes proper relative diagonal from the closed-immersion diagonal convention for schemes. In particular the target stack need not be separated over k. The source of this supporting node is exactly 050M(3), with 0CL0(1) giving separatedness of the target diagonal from finite, hence separated, inertia.

Step 6 only collects the choices over the set of points supplied by stack-point-topology, in the size convention's larger universe. Each constructed point maps to its chosen x, so surjectivity is literal coverage, with no compactness or finite-cover claim. The empty stack uses an empty indexing set. All geometric input was established in Steps 1--5; this collection step is marked elementary. Every step is shorter than 2000 characters, and proof_deps is the union of all uses.

I tested all five new statements on schemes with trivial inertia, identity groupoids, disjoint unions with varying finite ranks, and empty sources. For the genuinely non-DM case take B(mu_p) over characteristic p: Spec k -> B(mu_p) is finite flat but not smooth, so the general flat quotient node is needed, and the finite-inertia chart statement must not require an etale scheme atlas. The identity of B(mu_p) is an allowed chart. The pointwise statement identifies group schemes after a common field, never merely rational automorphism groups. For the open-locus theorem a disjoint empty stabilizer-preserving locus is allowed; the selected v is in it by the pointwise conclusion. For separation, finite group scheme classifying stacks have proper diagonal even if nonreduced, whereas B(G_m) is excluded by the finite-inertia hypothesis. No Noetherianity, perfection, smooth inertia, absolute target separatedness or constant-degree hypothesis was inserted.

B1--B7: new statements introduce their own objects and definitions, contain no proof sketches, and retain TeX with single semantic backslashes; all new proof/proof_deps lists are empty. C1/C4: the statements used by each step were opened and quotations in citations.json are verbatim, not strengthened paraphrases. D1/D2: no new theorem states the complete chart conclusion; even the pointwise chart lacks the global inertia isomorphism and relative separatedness, and the other new nodes are general groupoid or diagonal tools. E: no field-valued point was used as a rational point without field extension, no arbitrary affine-open intersection was assumed affine, and no descent via a smooth atlas was applied to a merely flat atlas. I corrected the initially tempting smooth-atlas citation and reused the more general 01ZY statement, as described above. No statement dispute or source error remains.

## Unfinished work

No work on the requested stage-1 split remains other than the required delivery checks and push. The five new supporting nodes deliberately remain statement-only stage-1 items; they are not claimed proved or Lean-closed.

## Validation

The preliminary sandbox review_split server check passed. The required full deliver.py --no-push invocation then exited 0: OK (not pushed) at cf99e1f29e9, preflight passed. It constructed the delivery on the live base and passed citation, search-log, duplicate and server preflight checks. This report update records that result; the final dry run and push use the updated report.

## Not duplicates

lem-sfb-finite-inertia-pointwise-groupoid-chart vs lem-trf-finite-locally-free-composition: the new theorem constructs an etale affine groupoid neighbourhood of a stack point with its stabilizer; the existing node instead states Composition of finite locally free morphisms and does not give that conclusion.

lem-sfb-finite-inertia-pointwise-groupoid-chart vs lem-sfb-smooth-atlas-automorphism-diagonal-test: the existing statement is the unramified diagonal/inertia criterion; the new statement uses separated or locally-quasi-finite inertia to obtain a pointwise finite groupoid chart.

lem-sfb-finite-inertia-pointwise-groupoid-chart vs lem-sfb-affine-proper-finite: the new theorem constructs an etale affine groupoid neighbourhood of a stack point with its stabilizer; the existing node instead states A morphism of schemes is finite if and only if it is affine and proper and does not give that conclusion.

lem-sfb-finite-inertia-pointwise-groupoid-chart vs lem-sfb-finite-etale-clopen-restriction: the new theorem constructs an etale affine groupoid neighbourhood of a stack point with its stabilizer; the existing node instead states Finite etale restriction to a nonempty clopen source over an irreducible base and does not give that conclusion.

lem-sfb-finite-inertia-pointwise-groupoid-chart vs lem-sfb-proper-orbit-pair-finite-norm: the new theorem constructs an etale affine groupoid neighbourhood of a stack point with its stabilizer; the existing node instead states Finite invariant norm pencils from affine orbit-separated pairs and does not give that conclusion.

lem-sfb-finite-inertia-pointwise-groupoid-chart vs lem-sc-proper-affine-finite-general: the new theorem constructs an etale affine groupoid neighbourhood of a stack point with its stabilizer; the existing node instead states A proper affine finite-type scheme over a field is finite and does not give that conclusion.

lem-sfb-finite-inertia-pointwise-groupoid-chart vs lem-per-affine-proper-finite: the new theorem constructs an etale affine groupoid neighbourhood of a stack point with its stabilizer; the existing node instead states Finiteness is equivalent to affineness and properness and does not give that conclusion.

lem-sfb-finite-inertia-pointwise-groupoid-chart vs lem-weil-pbc-finite-morphism-permanence: the new theorem constructs an etale affine groupoid neighbourhood of a stack point with its stabilizer; the existing node instead states Base change, affineness and properness for finite morphisms and does not give that conclusion.

lem-sfb-finite-inertia-pointwise-groupoid-chart vs lem-weil-pbc-finite-closed-map-finite-fibres: the new theorem constructs an etale affine groupoid neighbourhood of a stack point with its stabilizer; the existing node instead states A finite morphism is separated, universally closed and has finite fibres and does not give that conclusion.

lem-sfb-finite-inertia-pointwise-groupoid-chart vs lem-weil-pbc-etale-splits-off-isolated-points-technical: the new theorem constructs an etale affine groupoid neighbourhood of a stack point with its stabilizer; the existing node instead states An elementary etale neighbourhood splits off finite pieces through given isolated fibre points of a separated morphism (Stacks 02LN) and does not give that conclusion.

lem-sfb-finite-inertia-pointwise-groupoid-chart vs lem-weil-pbc-finite-geometric-point-lift: the new theorem constructs an etale affine groupoid neighbourhood of a stack point with its stabilizer; the existing node instead states Geometric points lift along a finite morphism (over every point of the fibre) and does not give that conclusion.

lem-sfb-flat-groupoid-quotient-open-presentation vs lem-sfb-finite-formal-quotient-pullback: the new theorem concerns arbitrary flat groupoid quotients, finite covers and invariant open substacks; the existing node instead states Finite representable pullbacks of a formal quotient chart and does not give that conclusion.

lem-sfb-flat-groupoid-quotient-open-presentation vs lem-sfb-representable-stack-fppf-locality: the new theorem concerns arbitrary flat groupoid quotients, finite covers and invariant open substacks; the existing node instead states Fppf target tests for representable stack morphisms and does not give that conclusion.

lem-sfb-flat-groupoid-quotient-open-presentation vs lem-sfb-invariant-open-substack-descent: the existing statement requires a smooth atlas; the new theorem permits a flat locally finitely presented, possibly nonsmooth, groupoid and states its quotient and finite-cover properties.

lem-sfb-flat-groupoid-quotient-open-presentation vs lem-sfb-smooth-groupoid-fppf-quotient: the existing theorem assumes smooth source/target projections; the new theorem applies to general flat lfp projections, including nonetale finite group schemes, and includes invariant-open restriction.

lem-sfb-flat-groupoid-quotient-open-presentation vs lem-sfb-flat-affine-action-stack-presentation: the existing theorem concerns the action groupoid of one affine finite-type group acting on a finite-type affine; the new theorem allows an arbitrary flat scheme groupoid and controls invariant opens and finite covers.

lem-sfb-flat-groupoid-quotient-open-presentation vs def-sfb-formal-moduli-quotient: the new theorem concerns arbitrary flat groupoid quotients, finite covers and invariant open substacks; the existing node instead states Formal quotient presentations with their coherent atlas actions and does not give that conclusion.

lem-sfb-flat-groupoid-quotient-open-presentation vs lem-sfb-invariant-closed-substack-descent: the new theorem concerns arbitrary flat groupoid quotients, finite covers and invariant open substacks; the existing node instead states Invariant closed subspaces of a smooth atlas descend to closed substacks and does not give that conclusion.

lem-sfb-flat-groupoid-quotient-open-presentation vs lem-sfb-finite-inertia-etale-affine-charts: the item constructs stabilizer-preserving separated etale charts for arbitrary finite-inertia stacks; the new theorem is the general flat-groupoid presentation and open-restriction input and gives no such charts.

lem-sfb-flat-groupoid-quotient-open-presentation vs lem-sfb-stack-representable-unramified-descent: the new theorem concerns arbitrary flat groupoid quotients, finite covers and invariant open substacks; the existing node instead states Unramifiedness of representable stack morphisms descends along flat covers and does not give that conclusion.

lem-sfb-flat-groupoid-quotient-open-presentation vs lem-sfb-finite-group-quotient-atlas-torsor: the new theorem concerns arbitrary flat groupoid quotients, finite covers and invariant open substacks; the existing node instead states Finite-group quotient atlas pullbacks are the defining torsors and does not give that conclusion.

lem-sfb-flat-groupoid-quotient-open-presentation vs lem-sfb-finite-flat-affine-stack-invariant-quotient: the existing theorem assumes a DM stack with an already supplied finite-flat affine cover and constructs its invariant moduli space; the new theorem constructs flat groupoid quotients and restricts arbitrary invariant opens without DM.

lem-sfb-flat-groupoid-quotient-open-presentation vs lem-sfb-affine-action-stack-presentation: the new theorem concerns arbitrary flat groupoid quotients, finite covers and invariant open substacks; the existing node instead states Presentation and diagonal of an affine action quotient stack and does not give that conclusion.

lem-sfb-flat-groupoid-quotient-open-presentation vs lem-sfb-finite-flat-affine-groupoid-moduli: the existing statement constructs the invariant-ring categorical moduli morphism and its topological/functions properties; it does not state the flat atlas, finite atlas or invariant-open quotient correspondence of the new theorem.

lem-sfb-finite-flat-affine-groupoid-separated vs lem-trf-finite-locally-free-composition: the new theorem asserts a proper diagonal for an algebraic-stack quotient of a finite-flat affine groupoid; the existing node instead states Composition of finite locally free morphisms and does not give that conclusion.

lem-sfb-finite-flat-affine-groupoid-separated vs lem-sfb-affine-proper-finite: the new theorem asserts a proper diagonal for an algebraic-stack quotient of a finite-flat affine groupoid; the existing node instead states A morphism of schemes is finite if and only if it is affine and proper and does not give that conclusion.

lem-sfb-finite-flat-affine-groupoid-separated vs lem-sfb-finite-etale-clopen-restriction: the new theorem asserts a proper diagonal for an algebraic-stack quotient of a finite-flat affine groupoid; the existing node instead states Finite etale restriction to a nonempty clopen source over an irreducible base and does not give that conclusion.

lem-sfb-finite-flat-affine-groupoid-separated vs lem-sfb-proper-orbit-pair-finite-norm: the new theorem asserts a proper diagonal for an algebraic-stack quotient of a finite-flat affine groupoid; the existing node instead states Finite invariant norm pencils from affine orbit-separated pairs and does not give that conclusion.

lem-sfb-finite-flat-affine-groupoid-separated vs lem-sc-proper-affine-finite-general: the new theorem asserts a proper diagonal for an algebraic-stack quotient of a finite-flat affine groupoid; the existing node instead states A proper affine finite-type scheme over a field is finite and does not give that conclusion.

lem-sfb-finite-flat-affine-groupoid-separated vs lem-per-affine-proper-finite: the new theorem asserts a proper diagonal for an algebraic-stack quotient of a finite-flat affine groupoid; the existing node instead states Finiteness is equivalent to affineness and properness and does not give that conclusion.

lem-sfb-finite-flat-affine-groupoid-separated vs lem-weil-pbc-finite-morphism-permanence: the new theorem asserts a proper diagonal for an algebraic-stack quotient of a finite-flat affine groupoid; the existing node instead states Base change, affineness and properness for finite morphisms and does not give that conclusion.

lem-sfb-finite-flat-affine-groupoid-separated vs lem-weil-pbc-finite-closed-map-finite-fibres: the new theorem asserts a proper diagonal for an algebraic-stack quotient of a finite-flat affine groupoid; the existing node instead states A finite morphism is separated, universally closed and has finite fibres and does not give that conclusion.

lem-sfb-finite-flat-affine-groupoid-separated vs lem-weil-pbc-etale-splits-off-isolated-points-technical: the new theorem asserts a proper diagonal for an algebraic-stack quotient of a finite-flat affine groupoid; the existing node instead states An elementary etale neighbourhood splits off finite pieces through given isolated fibre points of a separated morphism (Stacks 02LN) and does not give that conclusion.

lem-sfb-separated-source-finite-inertia-target vs lem-trf-finite-locally-free-composition: the new theorem is separated-source cancellation for arbitrary algebraic-stack morphisms with finite target inertia; the existing node instead states Composition of finite locally free morphisms and does not give that conclusion.

lem-sfb-separated-source-finite-inertia-target vs lem-sfb-smooth-atlas-automorphism-diagonal-test: the existing statement is the unramified diagonal/inertia criterion; the new statement uses separated or locally-quasi-finite inertia to obtain relative separatedness of every map from a separated source.

lem-sfb-separated-source-finite-inertia-target vs lem-sfb-affine-proper-finite: the new theorem is separated-source cancellation for arbitrary algebraic-stack morphisms with finite target inertia; the existing node instead states A morphism of schemes is finite if and only if it is affine and proper and does not give that conclusion.

lem-sfb-separated-source-finite-inertia-target vs lem-sfb-finite-etale-clopen-restriction: the new theorem is separated-source cancellation for arbitrary algebraic-stack morphisms with finite target inertia; the existing node instead states Finite etale restriction to a nonempty clopen source over an irreducible base and does not give that conclusion.

lem-sfb-separated-source-finite-inertia-target vs lem-sfb-proper-orbit-pair-finite-norm: the new theorem is separated-source cancellation for arbitrary algebraic-stack morphisms with finite target inertia; the existing node instead states Finite invariant norm pencils from affine orbit-separated pairs and does not give that conclusion.

lem-sfb-separated-source-finite-inertia-target vs lem-sc-proper-affine-finite-general: the new theorem is separated-source cancellation for arbitrary algebraic-stack morphisms with finite target inertia; the existing node instead states A proper affine finite-type scheme over a field is finite and does not give that conclusion.

lem-sfb-separated-source-finite-inertia-target vs lem-per-affine-proper-finite: the new theorem is separated-source cancellation for arbitrary algebraic-stack morphisms with finite target inertia; the existing node instead states Finiteness is equivalent to affineness and properness and does not give that conclusion.

lem-sfb-separated-source-finite-inertia-target vs lem-weil-pbc-finite-morphism-permanence: the new theorem is separated-source cancellation for arbitrary algebraic-stack morphisms with finite target inertia; the existing node instead states Base change, affineness and properness for finite morphisms and does not give that conclusion.

lem-sfb-separated-source-finite-inertia-target vs lem-weil-pbc-finite-closed-map-finite-fibres: the new theorem is separated-source cancellation for arbitrary algebraic-stack morphisms with finite target inertia; the existing node instead states A finite morphism is separated, universally closed and has finite fibres and does not give that conclusion.

lem-sfb-separated-source-finite-inertia-target vs lem-weil-pbc-etale-splits-off-isolated-points-technical: the new theorem is separated-source cancellation for arbitrary algebraic-stack morphisms with finite target inertia; the existing node instead states An elementary etale neighbourhood splits off finite pieces through given isolated fibre points of a separated morphism (Stacks 02LN) and does not give that conclusion.

