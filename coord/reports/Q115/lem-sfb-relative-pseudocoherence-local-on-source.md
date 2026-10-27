## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-relative-pseudocoherence-local-on-source.json: statement, split; statement unchanged, four proof steps, no Mathlib match.
- citations.json: five step/node entries with verbatim quotations from the current cited statements.
- report.md: this report. searches.jsonl is the search command's existing log; its eight completed results were read and reused after resumption.

New DAG nodes: 0. New Mathlib leaves: 0. The existing lem-sfb-relative-pseudocoherence-all-affine-charts now supplies exactly the theorem that otherwise would have needed a new supporting node.

## Attachments

None. Searched lean/WeilConjectures both for the blueprint tag and for relative/pseudo-coherent terminology. No project declaration states the item. Generic pseudofunctor descent declarations do not assert this property of a derived structure-module complex. No Lean file was written or compiled.

## WANTED

None. All sources needed here are present locally.

## Problems found and changes

The item was unsplit, without proof steps, and its old Mathlib searches covered only grep. I preserved its statement, existing search entries, source and all other inherited metadata, and added the eight searches actually logged for this item. Their results concern generic locality of scheme morphism properties or affine ring-map conditions, not relative pseudo-coherence of E. The only broad grep hit, SmallAffineZariski.lean:297, defines relative gluing data for a quasi-coherent algebra. Loogle and the narrower pseudo-coherence/strictly-perfect grep have no hits. The second semantic phrasing gives generic affine morphism-property infrastructure, not the required theorem; no instance supplying the relative derived-complex property exists there.

On resumption I checked the interrupted blueprint-search session: its process id no longer exists, and it had no mutating work. There was no report, delivery invocation or previous split in the sandbox. I read searches.jsonl and retained every completed query instead of repeating it. A fresh DAG search found the recently landed all-affine-charts node; I read its full statement and reused it. No supporting node was created.

The latest blueprint direct-images proof and unit were read under literature/blueprint/latest/. They place this auxiliary argument below the inherited direct-image/cohomology-and-base-change route; this is not the unit's key node. The inherited unit record is historical, so neither it nor the chapter record was edited. blueprint_refs.py ancestor returns None, consistent with the inherited null ancestor; its detailed from.place and via chain remain intact. Whole-blueprint searches for relative pseudo, pseudo-coher and 09UJ find no duplicate statement.

## Not duplicates

No new nodes. Reused lem-sfb-relative-pseudocoherence-all-affine-charts (09UJ with 09VC) and lem-weil-pbc-affine-opens-basis (01IT); did not create alternate names for either. The all-affine-charts criterion characterizes relative pseudo-coherence of a single complex by its polynomial embeddings on arbitrary affine chart pairs. The item instead assembles hypotheses about restrictions to an arbitrary given open cover. Its steps perform that assembly and are not merely an application of a renamed source-locality assertion.

## Review by Q115

I read Stacks more-morphisms.tex, definition-relative-pseudo-coherence (09UI), lemma-relatively-pseudo-coherent (09VC), and lemma-relative-pseudo-coherence-characterize (09UJ), including the latter's proof. I also read the first paragraph of lemma-characterize-pseudo-coherent (0CSL): it explicitly reduces the conclusion to proving the relative condition near each point. The item provides that assembly argument. Its fixed-m form holds for arbitrary E in D(O_X); neither 09UJ nor the reused affine-chart node assumes quasi-coherent cohomology. The final all-m form is a separate quantifier step. There is no need to claim one finite cover, one common embedding dimension or one cohomological bound for all m.

For step 1 I read schemes.tex lemma-basis-affine-opens, Tag 01IT, and the exact statement of lem-weil-pbc-affine-opens-basis. It provides an affine neighbourhood inside any open subset, precisely what is used for X_k intersect f^{-1}(V_a). That intersection is open since f is a scheme morphism. I index by the entire set of qualifying affine opens, so the resulting covering family is a set even for infinite I. A point of f^{-1}(V_a) lies in some X_k and then in such an affine neighbourhood. I do not assume affine intersections are affine; the warning immediately after 01IT in schemes.tex emphasizes this distinction. The cited node is already a Mathlib leaf, so its use across units is a tool already permitted by the contract.

For step 2 I opened lem-sfb-relative-pseudocoherence-all-affine-charts and checked that it states both existence of the closed affine-space embedding for each pair and m-pseudo-coherence of its derived pushforward for every such embedding. The hypotheses are checked on f_k and E restricted to X_k: the relative condition is exactly the assumption, U is an affine open of X_k as well as of X, V_a is affine in S, and f_k(U) lies in V_a. The restricted map f_k is locally of finite type: its local finite-type affine charts may be refined to principal opens inside X_k, whose algebras are obtained by adjoining one inverse to the original finite set of generators. This is also implicit in the assumed relative condition, which is defined for locally finite type maps. No finite-type hypothesis on all of X_k is substituted. The source 09UJ has precisely these hypotheses, and 09VC supplies the equivalent polynomial-chart formulations. I also read def-pc-derived-pullback. Its displayed derived tensor formula reduces to termwise restriction for open inclusions because the two ring sheaves agree and tensoring over that ring with itself is the identity. Consequently nested open restrictions are the same derived object as direct restriction. This checks the object passed to the embedding, rather than silently identifying unrelated pullbacks.

For step 3 I read the full current statement of def-sfb-relative-pseudo-coherent-complex. It asks for an affine cover of S, affine covers of each inverse image, and closed embeddings with the derived pushforward property. Steps 1 and 2 supply exactly those data, so this step is elementary existential assembly from the cited definition. There is no descent/gluing theorem being hidden here: no compatibility data is required by that definition.

For step 4 the same definition explicitly says pseudo-coherent means m-pseudo-coherent for every integer m, allowing covers and embeddings to depend on m. Apply the fixed-m result separately for each m; this proves the consequent with no uniformity claim. I quoted this definition again in citations.json for this separate use.

I checked delivery-errors B--E against the node and the open source texts: every non-elementary input is a cited statement, every step citation is supported by that node's statement, proof_deps is exactly the union of uses, and citations.json quotations are literal substrings. No new definition, statement-only node, duplicate node or Mathlib-leaf claim is being introduced. The statement needs no dispute or correction. The longest step is 737 characters; all four steps together have 2155 characters, and there is no hidden long-step lemma. No SGA source is used.

Edge cases checked: X empty (including empty I), S empty (which forces X empty), empty members of the cover, an infinite disjoint union of affine schemes over a base, non-affine intersections and a non-quasi-separated scheme, E=0, arbitrary positive or negative m, and arbitrary complexes without a global upper cohomological bound. Empty inverse images have an empty affine cover; infinite covering families are retained rather than made finite. Thus the argument does not add quasi-compactness, quasi-separatedness, boundedness, a Noetherian condition or a quasi-coherence hypothesis.

## Unfinished work

No mathematical part is left open in the item's proof. Supporting nodes are reused in their current status; the delivery is a one-level stage-1 split. Required server dry run and direct delivery follow this report.
