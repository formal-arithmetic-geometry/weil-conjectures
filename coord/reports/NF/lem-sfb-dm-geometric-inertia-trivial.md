# Stage-1 report: lem-sfb-dm-geometric-inertia-trivial

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-dm-geometric-inertia-trivial.json: item split into six proof steps; statement unchanged; original source, creation record, searches and inherited blueprint chain retained.
- dag/nodes/sec-six-functors-basics/lem-sfb-dm-isom-space-unramified.json: new statement-only prerequisite; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-unramified-space-open-diagonal.json: new statement-only prerequisite; no Mathlib match for algebraic spaces.
- dag/nodes/sec-six-functors-basics/lem-sfb-etale-sheaf-space-atlas-bootstrap.json: new statement-only prerequisite; no Mathlib match.
- citations.json: eight verbatim statement quotations, covering every step/node citation.
- searches.jsonl: actual search-command log for the new prerequisites. The inherited item searches were read and retained; none was invented or relabelled as a search performed by NF.

## Attachments

None. Searches of lean/WeilConjectures by the exact blueprint tag, Deligne--Mumford terminology, algebraic-stack terminology, geometric stabilizers and trivial inertia found no declaration stating this item. Hits on trivial inertia concern fundamental groups or lisse sheaves, not automorphisms of objects of a stack. The additional read-only search of lean/Sheaf gave no matching declaration either.

## WANTED

None for this split. All needed Stacks sources are present locally. The source PDF of the moduli-groupoid definition is not needed here: only its explicitly written general stack, groupoid and atlas conventions are used.

## What was wrong or incomplete

The item was statement-only, not already split. Its conclusion is correct as written. Geometric automorphism triviality cannot be treated as automorphism triviality over arbitrary schemes without using the Deligne--Mumford hypothesis. Its source mentions an open identity section of unramified inertia. The split instead pulls back the open diagonal of the automorphism space along the automorphism and identity sections, so every equality being used has its full scheme structure.

There is also a topology issue to handle explicitly. The project's moduli-groupoid convention requires etale descent, whereas def-trf-algebraic-space requires an fppf sheaf. The split constructs only an etale sheaf of isomorphism classes at first; Tag 0BH4 is the precise theorem that supplies the fppf algebraic space. No fppf stack hypothesis is silently added to the item.

The blueprint ancestor command returns null for this inherited newly created chain. The item keeps that value and its complete inherited via chain. Every new node prepends the item to that chain and specifies the exact role of its sublemma in the inherited direct-image/alteration prerequisite. The current blueprint direct-images proof (3), its chapter, and the recorded sk-thm-sf-ctf-stability unit were read. This split stays below the level-rigidification prerequisite and changes no unit or chapter route or target statement.

## Mathlib searches and duplicate searches

All new nodes were searched with msearch.py using LeanFinder twice, LeanSearch, Loogle and source grep, with actual query strings and returned names recorded from searches.jsonl. All services answered successfully. For the Isom-space node, the hits were scheme-level formal unramifiedness and etale morphisms. For the diagonal node, the concrete candidate AlgebraicGeometry.FormallyUnramified.isOpenImmersion_diagonal was read in Mathlib/AlgebraicGeometry/Morphisms/FormallyUnramified.lean at line 126. Its source and target are schemes. It does not apply to an arbitrary algebraic space, and passing to charts is itself a theorem, so this is not a Mathlib leaf. For bootstrap, the LocalRepresentability declarations were read with their hypotheses in Mathlib/AlgebraicGeometry/Sites/Representability.lean: they require a Zariski sheaf and relatively representable open immersions, not an etale atlas, so they do not give this result.

Before creating nodes I searched the whole DAG by tags, key words and statements, the whole imported blueprint with blueprint_refs.py search (including setoids, unramified diagonal, isomorphism sheaf, etale atlas, 05W1, 06N3, 076M and 0BH4), and the Lean sources. Existing stable-curve Isom lemmas require stable curves and sometimes finite type or finiteness; they do not prove the general Deligne--Mumford assertion. Existing etale relation quotients require a scheme relation, not the algebraic-space atlas condition of the bootstrap node. Existing etale-sheaf realization is a small-etale-site theorem for etale spaces over a fixed scheme, not the big-site recognition statement used here.

## Not duplicates

lem-sfb-dm-isom-space-unramified vs lem-sfb-curve-stack-infinitesimal-dm-locus: both mention Tag 06N3, but the existing node characterizes the open DM locus of the stack of proper curves by infinitesimal automorphisms; the new node states unramified representability of Isom functors for every DM stack and every test scheme, without any curve hypothesis.

lem-sfb-unramified-space-open-diagonal vs lem-sfb-dm-geometric-inertia-trivial: Tag 05W1 is a prerequisite cited in the item's source; the new node is the general open-diagonal theorem for an unramified algebraic space over a scheme, with no stack or stabilizer hypothesis, not the item's geometric-to-arbitrary-base assertion or its algebraic-space conclusion.

lem-sfb-unramified-space-open-diagonal vs lem-sfb-smooth-curve-abelian-level-rigidification: the existing node concerns smooth genus-at-least-two moduli with abelian level structures and their scheme representative; its discussion mentions Tag 05W1 only as part of the missing geometric-inertia argument. The new node concerns arbitrary unramified algebraic spaces and constructs no level structure or moduli representative.

No existing node contains the new bootstrap node's source tag 0BH4. It is a recognition theorem for an arbitrary etale sheaf with an algebraic-space-representable etale atlas; it assumes neither a groupoid nor a geometric stabilizer condition. In particular it is not a renamed clause of the item.

## Review by NF

I read algebraic.tex at Tag 045H (lemma-algebraic-stack-no-automorphisms) and Tag 04SZ (proposition-algebraic-stack-no-automorphisms), including the proofs that pass from a setoid stack to its sheaf and transfer the atlas. These are the source of the item's last three steps. I also read the local source and tag mapping for stacks-morphisms.tex Tags 06N3 (theorem-DM) and 06MB (lemma-properties-covering-imply-diagonal), algebraic.tex Tag 045G (lemma-representable-diagonal), spaces-morphisms.tex Tags 03ZJ (lemma-base-change-unramified), 03ZK (lemma-unramified-local), and 05W1 (lemma-diagonal-unramified-morphism). These supply the two geometric prerequisites. Finally I read bootstrap.tex Tag 0BH4 (lemma-spaces-etale-locally-representable) in full, together with the nearby etale/fppf discussion, for the recognition prerequisite. The source of each new node is a tag and its exact local TeX label.

Step 1 cites only lem-sfb-dm-isom-space-unramified, whose statement explicitly represents the Isom functor on all T-schemes and makes its map to T unramified. Applying it to x=y is legitimate for the arbitrary S-scheme T fixed in the proof; it imposes neither separatedness nor finiteness nor reducedness. The project defines DM by an etale atlas rather than by an unramified diagonal, so the new prerequisite explicitly carries the substantive atlas-to-unramifiedness theorem, not merely the definition of DM. Tag 06MB's atlas argument is local for etale covers; its Isom-space formulation applies to the project's etale-stack convention without assuming an fppf descent property for the original stack.

Step 2 cites lem-sfb-unramified-space-open-diagonal. I checked its explicit conclusion about every scheme base change of the diagonal; taking Z=T and b=(a,e) gives exactly the open equalizer needed. The identification of its test-scheme points with equality of the two automorphisms is the defining fibre-product equation. It does not use a theorem about closed equalizers or equality on reduced subschemes.

Step 3 cites def-weil-algebraic-closure, which actually includes existence of algebraic closures, def-weil-geometric-point, which includes the residue-field description, and def-weil-open-immersion, which identifies an open immersion with the restricted structure sheaf on its image. These statements justify choosing an algebraically closed geometric point above every point of T and concluding that the open equalizer is all of T as a scheme. This is why nilpotents are not lost. The hypothesis of the item applies to the composite Spec(Omega) -> T -> S and to the actual pulled-back object. Empty T causes no exception: its only open subscheme with the same underlying space is itself.

Step 4 cites the statement of def-sfb-stable-pointed-moduli-groupoids, not one of its proofs. That statement explicitly supplies groupoids, pullback, the sheaf condition for isomorphisms and effective etale descent. The elementary calculation g^{-1}f=id makes arrows unique. Overlap isomorphisms are therefore unique and satisfy the cocycle equation, so the stated descent axiom glues objects. The same uniqueness and the stated sheaf condition glue isomorphisms. The canonical class functor is fully faithful and essentially surjective and commutes with pullback. All of this is written in the step, rather than hidden in an uncited claim about coarse moduli.

Step 5 cites the same definition's exact atlas clause and its interpretation of scheme base changes. I checked the comparison on points of every T-scheme: the ordinary sheaf fibre product remembers a class equality; the 2-fibre product additionally remembers an isomorphism, which is unique by step 3. Forgetting or adjoining that unique isomorphism are inverse and respect restriction. Thus the given atlas, including representability by algebraic spaces and surjective etaleness, supplies precisely the hypothesis used in the next step. No scheme representability of the 2-fibre product, no coarse space, and no finite diagonal are assumed.

Step 6 cites only lem-sfb-etale-sheaf-space-atlas-bootstrap, which explicitly assumes just an etale sheaf, a scheme atlas, and algebraic-space base changes with surjective etale projection, and concludes that the same functor is an fppf algebraic space. Steps 4 and 5 verify all those hypotheses. The canonical equivalence of step 4 then yields naturality of the final equivalence. This bootstrap theorem is independent of stacks and is strictly below the item's conclusion, while steps 1--3 carry the geometric stabilizer argument themselves.

For new-statement edge cases I checked the empty stack and empty test scheme, schemes viewed as discrete stacks, and a classifying stack of a nontrivial finite etale group. In the last case the unramified Isom node still applies but the item's geometric hypothesis correctly fails. The necessity of the DM hypothesis is visible on B(mu_p) over an algebraically closed field of characteristic p: geometric automorphism points are trivial, but 1+epsilon is a nonidentity mu_p automorphism over the dual numbers; this stack has non-unramified diagonal and is excluded. I also checked that the diagonal prerequisite never infers an isomorphism merely from an underlying surjection: it is the open-immersion scheme structure that licenses that inference. For bootstrap I checked that the input is the big etale sheaf with the full atlas base-change condition, not a small-site sheaf or an arbitrary epimorphism of sheaves.

I checked delivery-errors B--E against the written files. Each new node has a self-contained statement, its notions are cited or defined inline, no proof or proof dependency is hidden in a new statement-only node, source labels and tags agree, and every Mathlib search was actually run. Same-tag pairs are distinguished above. The proof uses no unnamed non-elementary facts: the atlas-to-unramifiedness, algebraic-space diagonal theorem, and etale/fppf recognition are the three cited prerequisites; equality-locus formation and unique descent are written elementary calculations from their statements and the stack definition. The split does not move its own assertion into another node, use the proof of a citation, or cite its parent. All six steps have fewer than 1000 characters, so none crosses the 2000-character long-step threshold. The three new statements remain unsplit as required. No statement dispute was found and no Lean was written or compiled.

## Unfinished work

No part of this one-level split is left unfinished. The three explicitly stated prerequisite nodes are intentionally unsplit and are delivered for later work. No Mathlib leaves or Lean attachments are claimed.
