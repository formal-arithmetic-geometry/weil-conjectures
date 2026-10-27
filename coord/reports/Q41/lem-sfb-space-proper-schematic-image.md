## Worker report

Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-space-proper-schematic-image.json` (statement, split; Mathlib no match). Supporting delivery files: `citations.json`, this report, and the command-owned `searches.jsonl`. No new nodes and no Mathlib leaves.

Attachments: none. Searched `lean/WeilConjectures/` for the exact blueprint id and AlgebraicSpace, and for scheme-theoretic/schematic image. There are no AlgebraicSpace or item-id hits. Image declarations concern schemes, hence do not state the space theorem. No Lean was written and no compiler was run.

WANTED: none.

The item statement agrees with Stacks 0AGD, specialized from an algebraic-space base B to the scheme T; minimality is precisely 082X. No statement dispute or change is needed. The previous item had no proof. All its original fields and historical searches are retained. I added five searches actually run with msearch.py, read the hits, and inspected Mathlib/AlgebraicGeometry/IdealSheaf/Subscheme.lean lines 658–730 and Morphisms/Proper.lean lines 38–48: the image and properness declarations there have Scheme arguments. The second LeanFinder phrasing again found only scheme universal-closedness declarations. The Loogle finite-image-neighbourhood hit is also for schemes and imposes a finite-fibre condition, not the present statement. All services answered, so none is recorded unavailable.

Nothing remains mathematically unfinished in the item's one-level split. Its cited existing nodes remain independent work items, as the stage-1 contract intends.

## Sources and route

Read spaces-morphisms.tex, 0AGD lemma-scheme-theoretic-image-is-proper, 082X lemma-scheme-theoretic-image, 082Z lemma-quasi-compact-scheme-theoretic-image, 04NX lemma-universally-closed-permanence, and 08AJ lemma-image-proper-is-proper, including their proofs. Also read the definition of proper and its closed-immersion and base-change lemmas. These supply the exact route: quasi-compact map, schematic image with dense point image, closed image, surjectivity, and properness of the image.

Read the existing stack schematic-image node in full, plus stacks-morphisms.tex 0CPU lemma-scheme-theoretic-image-existence, 0CMK lemma-existence-plus-flat-base-change and 0CML lemma-topology-scheme-theoretic-image. This existing theorem explicitly states the minimal closed subspace and closure identification needed here; it is not merely a definition or a proof sketch. Applying it to discrete algebraic spaces avoids duplicating 082X/082Z. The identification uses the stack/space finite-type compatibility and point-topology compatibility in the statements cited in step 1.

Read the chapter and unit records and latest blueprint sk-thm-sf-ctf-stability-direct-images.proof.md (3). The current blueprint no longer displays the old alteration/moduli subargument in the inherited blueprint.from.place; its direct-image route is shorter. I retain the inherited helper role and null ancestor. `blueprint_refs.py ancestor` explicitly reports None. Whole-blueprint searches for schematic image, scheme theoretic image and 082Z found none; proper image found pqf-lem-image-proper, which treats schemes and a finite-type target, whereas the item treats arbitrary spaces and only a locally finite-type target. No unit or chapter record was edited.

The off-unit generic tools are lem-trf-space-fibre-products-etale-covers and lem-a1-space-point-open-calculus: only the construction of space fibre products, continuity, and the point-image formula under base change are taken from them. They replace no direct-image theorem or part of the unit route, and no node of this unit provides these foundations. They are declared in split_report.tool_uses for the maintainer to judge; no maintainer tool_uses field is set.

## New nodes

None. In particular there is no new node restating existence, surjectivity or properness of the item. The properness descent argument is written out in steps 5–6 from existing inputs.

## Not duplicates

No new-node/existing-node pairs arise. The whole DAG was searched by 0AGD, 082X, 082Z, the cited Stacks labels, schematic-image phrases and proper/surjective phrases. Reused lem-sfb-stack-schematic-image-qc, not a new space specialization; reused lem-sfb-space-proper-cancellation, not a new closed-graph lemma. The open-immersion-only lem-sfb-space-qc-open-schematic-closure and the scheme-only pqf-lem-image-proper cannot be used as if they stated the general space theorem.

## Review by Q41

I checked B–E with the actual node statements and Stacks sources open. No new nodes are introduced, so the new-node form/search/hypothesis checks introduce no extra obligations. The item keeps every hypothesis, all conclusions, and the empty case. Every proof step is below 2000 characters. The dependency union equals proof_deps; citations.json contains a verbatim statement quote for every step/node pair. I traversed the statement and proof dependencies of the existing schematic-image, proper-cancellation and separation tools to rule out a path back to this item.

Step 1: lem-sfb-space-proper-cancellation says exactly that a proper composite and a separated post-map make the first map proper, so it applies to qh=p with no representability or Noetherian assumption. The discrete-groupoid convention is explicit in def-sfb-stack-qcqs-morphism. An algebraic space is a stack because object descent is sheaf descent and its diagonal and atlas are supplied by its definition. lem-sfb-stack-chartwise-smooth-etale-calculus says etale is smooth. lem-sfb-stack-finite-type-calculus explicitly identifies the space and stack finite-type notions, hence their quasi-compactness conditions for the finite-type map h; this is enough to apply the existing stack image theorem. lem-sfb-stack-point-topology states agreement of point topologies on spaces, rather than requiring a new comparison theorem.

Step 2: opened lem-sfb-stack-schematic-image-qc and checked its statement gives both the factorization through the smallest closed subspace and the closure of the image on points. Its only relevant hypothesis is quasi-compactness, proved in step 1. I use neither its proof nor its flat-base-change clause. Defining r=qi makes ru=p by h=iu and qh=p. Minimality concerns subspaces with their full ideal structure; it is not inferred from closed point sets.

Step 3: def-sfb-space-morphism-properties defines universal closedness on all space base changes, so the identity base change makes the image of the whole source closed. lem-sfb-stack-closed-immersion-calculus states that a closed immersion gives a homeomorphism onto a closed subset and thus an injective point map. Given i(z)=h(x)=i(u(x)), injectivity yields z=u(x). This elementary set argument proves surjectivity from the existing closure identity; no extra lemma is hidden.

Step 4: lem-sfb-space-closed-subspace-proper explicitly makes every space closed immersion proper with no finite-presentation hypothesis. Its properness includes separatedness and local finite type by def-sfb-space-morphism-properties. lem-sfb-space-separated-fp-composition explicitly gives composition of separated morphisms (I do not take local finite type from its finite-presentation clause). Local finite type composition instead comes from lem-sfb-stack-finite-type-calculus, which covers representable maps of spaces and identifies the space notion. Thus r is separated and locally finite type even when i is not finitely presented.

Step 5: lem-trf-space-fibre-products-etale-covers supplies the actual sheaf fibre products and universal property, giving X'=X times_Z Z'. The point-image formula in lem-a1-space-point-open-calculus shows u' is surjective without assuming points preserve fibre products bijectively. That same statement gives continuity. lem-sfb-space-proper-base-change has no representability, Noetherian or finite-presentation restriction, so it applies to every algebraic-space T' over T. The explicit equality r'(C)=p'(u' inverse(C)) for closed C proves closedness of r' from p' and surjectivity. This is the elementary closed-set calculation in the proof of 08AJ, not an invocation of an unstated properness-descent theorem.

Step 6: the all-quasi-compact-test description in lem-sfb-stack-finite-type-calculus gives quasi-compact X_A for every quasi-compact space A over T. def-sfb-stack-qcqs-morphism explicitly describes such a space by an etale atlas W with W a quasi-compact scheme. The continuity and surjectivity criteria in lem-a1-space-point-open-calculus apply to that representable atlas; composing with the surjection u_A gives a continuous surjection W to Z_A on points. An open cover of Z_A pulls back to W and has a finite subcover by the exact definition in def-weil-pbc-quasi-compact-scheme. Surjectivity makes the original finite family cover Z_A. lem-sfb-qc-space-affine-etale-atlas explicitly turns this topological quasi-compactness into an affine etale atlas, with no separation assumption, so Z_A is quasi-compact in the space sense. This establishes exactly the all-test criterion for r. Properness now follows from the local finite type and separatedness in step 4 and universal closedness in step 5. I replaced an earlier version using stack quasi-compact-surjection by this direct open-cover argument to avoid leaving an implicit comparison of stack and space quasi-compactness predicates. The stronger stack surjection theorem was read (including its source 04YC) but is not used in the final split.

I tested empty X (empty schematic image and all conclusions hold), h a closed immersion (its image retains the full possibly nonreduced structure), q the identity, nonreduced/non-Noetherian bases, and a target with infinitely many disjoint finite-type components. The last case checks why quasi-compactness of Y is neither needed nor assumed. I corrected no statement; the substantive refinement beyond the short source proof is the explicit separate quasi-compactness check. No SGA source is used.


## Validation

The first server dry run passed (receipt 4e7558a7835). Final self-review then added the fibre-product citation for the diagonal in step 1 and replaced the last quasi-compactness argument by the direct finite-subcover argument just described. A new dry run is required for these changes.
