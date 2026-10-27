# Stage-1 report: lem-sfb-finite-constant-torsor-map-etale-stack

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-constant-torsor-map-etale-stack.json: item, statement unchanged, split into seven proof steps; no Mathlib match.
- citations.json: verbatim statement quotes for every step/node citation.
- searches.jsonl: actual searches recorded by msearch.py, read before recording verdicts.

No new nodes; zero Mathlib leaves created. No Lean files written, compilers invoked, or repository files modified.

## Attachments

None. Searches in lean/WeilConjectures for the blueprint tag and for torsors, quotient groupoids and descent found finite-etale descent and specialized abelian/sheaf torsor results, not the full scheme-torsor-with-map stack statement. finiteEtaleDescent in AlgebraicGeometry/FiniteEtaleDescent.lean:66 supplies the underlying finite-etale result, already represented by lem-galois-descent; it does not justify attachment of this item.

## WANTED

None. All mathematical sources used are present locally.

## What was wrong or changed

The item had a statement and searches but no proof. Its statement is correct and retained without strengthening or weakening. Stacks 0370 supplies the route, with its omitted arrow descent written out. We use finite-etale scheme descent rather than arbitrary effective scheme descent (which would be false), then glue the additional structures explicitly. We do not identify a nonabelian finite group with a finite abelian sheaf.

The inherited blueprint ancestry is broken: tools/blueprint_refs.py ancestor reports None because the created.item chain ends at the missing node Sheaf.SixFunctors.CtfStabilityDirectImages. The existing blueprint.from.node is null and its detailed place already names det-thm-sf-ctf-stability-direct-images, proof (3). I retained this metadata rather than inventing an ancestor or modifying another node. I read the current latest blueprint sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md: this supplies a supporting quotient-descent input far below the direct-image argument, not an alternative unit route.

## What remains unfinished

Nothing in this one-level split. The existing non-leaf dependencies retain their own independent proof work. There are no new obligations.

## Review by Q28

I read examples-stacks.tex Tag 0370 (lemma-group-quotient-stack-in-groupoids), including the precise torsor-with-equivariant-map category before the lemma and its descent proof. Its group can be more general and its torsors algebraic spaces; our finite constant scheme version is proved with finite-etale scheme descent. I also read Tag 0BLZ (lemma-finite-etale-stack), which explicitly delegates effectivity to affine descent and property descent. Descent Tag 023Q gives morphism gluing with arbitrary scheme targets, without separatedness or finite type; Tags 02LA and 02VN descend finiteness and etaleness. Topologies Tag 022C converts etale families to fpqc families. Morphisms 02GJ, 02GO, and 01WI and Mathlib Limits.lean:604--647 support the constant-scheme calculation and cover bookkeeping. There are no new nodes requiring additional sources.

For step 1 I opened the fibre-product, etale-cover-base-change and moduli-groupoid definition nodes: their statements give the universal property, stability of jointly surjective etale families, and the CFG/stack conventions actually used. The coherence is checked by the projections, not by an unproved general pseudofunctor theorem.

For step 2 I opened lem-weil-pbc-fpqc-finer-than-etale, lem-weil-pbc-etale-covering-base-change and lem-weil-pbc-fpqc-representable-descent. The first is phrased for a small site: I apply it to the small site of the scheme being covered and its identity object, so it applies to every big-site covering under discussion. The second allows an arbitrary base change; the third gives unique gluing into an arbitrary scheme. Base compatibility follows by uniqueness into the base scheme. No quasi-compactness of an individual etale arrow is assumed.

For step 3 I read each of the six cited statements. Finite coproduct etaleness applies to identity maps. The finite affine-coproduct spectrum node supplies the product ring model; the module generators are written out rather than hidden behind a new lemma. The coproduct node supplies the open disjoint pieces, and finiteness-local-on-target permits this affine check. The two property-descent statements require fpqc families, exactly supplied in step 2. A torsor's finite-etale nature is proved here; it is not smuggled in by citing a torsor definition.

For step 4 the sole new input is the full gluing and uniqueness statement of representable fpqc descent. The underlying maps and their inverses glue on the covers of P and Q. I explicitly check inverses, the map to V, and each constant h-action by uniqueness. Repeating this after an arbitrary test-scheme base change gives the presheaf sheaf assertion, including uniqueness.

For step 5 I opened the coproduct, Zariski-local finite/etale, fibre-product and lem-galois-descent statements. The descent node asserts equivalence, not merely fully faithful pullback: it actually supplies the finite-etale scheme with the specified descent isomorphisms. Its statement explicitly allows the coproduct of an etale covering as the single surjective etale map. Finite/etale locality handles the possibly infinite disjoint union componentwise. The pair and triple overlaps are identified by disjoint open decompositions and the universal property; no affine-intersection or quasi-separated hypothesis is used.

For step 6 morphism gluing descends each h-action map. Its inverse and group law follow by uniqueness. Coproducts and fibre products turn these maps into the constant group scheme action. The composition-of-etale-covers node has exactly the two-level family conclusion used to retain etale-local triviality. This is a direct calculation from the cited statements, not an extracted lemma repeating the item.

For step 7 morphism gluing supplies f into arbitrary V, and uniqueness into V and S checks equivariance and the S-structure. The moduli-groupoid node defines precisely the two required stack conditions. The specified overlap maps are retained from step 5. I checked every uses entry against its node statement; citations.json copies actual statement text verbatim. Every non-elementary input has a node; each direct calculation is marked elementary. Every step is below 2000 characters, so no long-step hidden lemma remains.

I tested H trivial (the assertion becomes descent of maps into V), nonabelian H (only the order-sensitive law a_g a_h = a_gh is used), characteristic dividing |H| (a finite constant scheme remains etale), nonfree actions on V, empty V, empty T with its empty cover, and infinitely indexed coverings on non-quasi-compact non-quasi-separated bases. The empty-base descended scheme is empty and all maps are unique; no argument requires a chosen point of a torsor. I checked no unit route or target statement was changed, no general scheme effectivity was assumed, and no new nodes duplicated an existing lemma or an item clause. Mathlib searches were run with msearch.py, in two semantic phrasings, both IsStack and torsor Loogle queries, and grep searches; I read the generic IsStack/IsPrestack declarations and type-torsor hits, which do not prove scheme descent. Prior imported search records are retained as required, and the fresh logged records are appended.

The off-unit inputs in split_report.tool_uses are generic topology, locality and scheme-descent tools. The unit supplies no other finite-etale scheme descent result; using them preserves its route and does not replace the moduli argument.
