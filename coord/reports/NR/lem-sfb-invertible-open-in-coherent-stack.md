# Stage-1 report: lem-sfb-invertible-open-in-coherent-stack

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-invertible-open-in-coherent-stack.json: statement, now split into six proof steps; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-relative-finite-free-locus-base-change.json: new statement-only unsplit support lemma; no Mathlib match. It states Stacks 0CZR for a locally finitely presented scheme morphism and a finitely presented quasi-coherent sheaf flat over the base.
- citations.json: all 23 step/node citations, with verbatim statements.
- searches.jsonl: searches actually run through the required msearch.py command. The JSON nodes record these exact queries and their logged answers.

## Attachments

None. Searched lean/WeilConjectures by the item's blueprint tag, invertible/coherent/Picard/open keywords, and finite-free-locus/base-change terminology. The hits concern ideal sheaves, rank conditions for cohomology, or other Picard subfunctors; none states this item. The new 0CZR input also has no matching project declaration. No compiler or Lake command was run.

## Wanted literature

None. Both source statements and proofs are in literature/stacks-project/.

## Errors, changes and route

The imported item is mathematically correct. Its statement and stmt_deps are unchanged. Its proof was empty. I retained all inherited searches and blueprint metadata and appended the searches run in this attempt. There was no prior item copy, split, report, search log, or released repair note in the sandbox.

I read quot.tex, Tag 0D03 (lemma-picard-stack-open-in-coh), lines 2601–2657, including the precise proper-support and flatness argument. The only new node states more-morphisms.tex, Tag 0CZR (lemma-finite-free-open), lines 4823–4851. I also read spaces-more-morphisms.tex, Tag 0CZT, lines 5989–6021, the algebraic-space version cited by 0D03. This is a strictly smaller input on the source space, with no properness, global base locus, groupoid, or stack assertion.

The latest blueprint was read at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/: _section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. This preserves the inherited supporting Picard-moduli prerequisite beneath direct-images clause (3). The ancestor command returns None, as in the imported item's blueprint.from.node; this is retained rather than inventing a blueprint id. New-node via prepends the item to the inherited chain. Searches of the whole imported blueprint for invertible open coherent, finite free open, locally free locus, free locus, locally free, 0CZR, 0CZT, rank one locus, and Picard coherent found no node stating either theorem. General invertible-module definitions and Picard representability theorems are different statements.

## Not duplicates

No existing node shares the new node's primary source tag 0CZR (or the cited space analogue 0CZT); whole-DAG searches found none. The delivery checker also indexes the contextual 0D03 citation, and its flagged pair is distinguished below.

lem-sfb-relative-finite-free-locus-base-change vs lem-sfb-relative-flat-locus-base-change: the latter concerns flatness of a morphism X→Y with source X flat over S, and does not state freeness of a sheaf F flat over T. Applying it would require a new construction and comparison, not a specialization.

lem-sfb-relative-finite-free-locus-base-change vs lem-sfb-coherent-universal-rank-locus: the latter assumes a Noetherian base and represents pullbacks becoming a fixed rank by a generally locally closed subscheme. The new node has an arbitrary base and uses relative flatness to prove equality of the already-free source locus under arbitrary change of base.

lem-sfb-relative-finite-free-locus-base-change vs lem-pc-finite-free-residue-locus-open: the latter is an openness statement for residue cohomology of a bounded complex of globally finite free sheaves; it gives no relative-sheaf base-change equality.

lem-sfb-relative-finite-free-locus-base-change vs lem-sfb-invertible-open-in-coherent-stack: the new lemma gives only a source open W for any finite rank; proper images, the rank-one condition, and the representing equivalence are proved in the item.

lem-sfb-relative-finite-free-locus-base-change vs lem-sfb-flat-proper-picard-algebraic-space: the existing node represents the fppf Picard sheaf assuming universal O_T≅(f_T)_*O; it does not state a source sheaf freeness locus or its base-change equality. Its contextual reference to 0D03 is not its assertion. The new node uses 0CZR and does not assume properness or universal O-cohomology flatness.

## Review by NR

I checked delivery-errors B–E against the actual files and the source, with each cited statement open. The new node introduces p,Y,T,F,v,Y_1,q, finite presentation, and the finite locally free predicate, and cites the definitions that supply those notions. Its flatness convention agrees with the stalkwise ambient convention because def-pc-scheme-module-flat-over explicitly states the equivalent stalkwise condition. Its proof is empty, proof_deps empty, status unsplit: it is not secretly a second split. The source explicitly permits arbitrary base change and only assumes local finite presentation of p, not flatness of p. I tested the zero module (the finite-free open is the whole source, rank zero), the empty source/base, and p=id with F flat and finitely presented. The relative-flatness hypothesis is essential: A=k[e]/(e^2), F=A/(e), base p=id without F flat would become free after Spec k→Spec A although it was not free at the original point. That counterexample does not satisfy the new node's hypotheses.

Step 1 uses lem-weil-pbc-flat-morphism-base-change exactly for flatness of p, proper-fp-permanence clause (b) for properness, and invertible-module's rank-one frames for finite presentation. module-flat-transitive states the required restriction-of-scalars implication (its hypotheses hold on the local rings). The coherent-stack statement supplies the exact proper-support witness convention and arrows, not an unstated theorem about locally free loci. Pullback's tensor formula proves preservation of a rank-one frame directly. Full faithfulness is literal equality of arrow sets.

Step 2 checks p is locally of finite presentation using qcqs-morphism-permanence clause (3); F is finitely presented and T-flat from the ambient statement. These are precisely the new 0CZR node's hypotheses. Only that new node is used for the nontrivial base-change equality. The proper-morphism definition actually states universal closedness, so the image of the closed bad subset is closed. finite-locally-free-sheaf means the variable local finite frames needed on X_V.

Step 3 uses the common-extension-fields statement, which supplies embeddings for any two residue extensions; neither algebraicity nor finite degree is assumed. The fibre-product definition supplies the morphism from the common-field spectrum. This produces a point above any compatible pair and justifies the crucial converse about the image of Z; I did not treat scheme pullback points as a set-theoretic product. The factorization through V is then the explicitly described restriction of the map of locally ringed spaces. The common-field lemma is a declared generic tool use from another unit: it is field theory, not a replacement for this unit's geometric route.

Step 4 is the elementary rank calculation from finite frames, with source modules.tex 01C9 (lemma-rank) read at lines 2126–2144. At a point, reducing frames to a nonzero residue field proves independence of the number of generators; each frame proves local constancy. The existing finrank-field-base-change statement is applicable to finite-dimensional residue vector spaces over residue field extensions. Pullback's tensor formula makes the new frames. Thus both the rank-one and complementary rank loci are open; there is no unjustified claim that an infinite union of closed sets is closed. In particular this works on non-quasi-compact T and for unbounded ranks on its different components. Marked elementary because the frame calculation is written out and no additional theorem is assumed.

Step 5 uses proper-fp-permanence clause (b) again on V→T and proper-morphism's actual closed-map assertion. It applies point lifting already proved in Step 3, and Step 4's rank calculation, to identify the universal rank-one open. Every factorization and converse is written. For X empty, W and R are empty and U=T; this correctly includes the unique invertible sheaf on the empty scheme. For F=0 and a nonempty fibre, that fibre lies in rank zero and is excluded. For F already a line bundle, U=T. Disconnected and empty fibres cause no added surjectivity hypothesis. Nilpotent bases and nonflat test maps are allowed by 0CZR.

Step 6 reads the definition of full open substack and its two-fibre-product convention literally. It gives the objects (L,alpha), their unique comparison arrows, and the resulting trivial automorphism groups; hence it proves an equivalence of groupoids, not only a bijection of isomorphism classes. The pullback definition supplies id and composition isomorphisms. Their coherence here follows from uniqueness of the comparison arrows. This realizes the representing equivalence naturally over T and the open immersion is the actual U⊂T.

I checked no cited statement is being used through its proof, no cyclic reference is introduced (the one new support node has only definition dependencies), no own-clause relabeling, no added reducedness, f_*O, Noetherian, or flat-test-map assumption. All steps are below 2000 characters (816,598,872,878,714,1018), and I reviewed them for hidden comparison lemmas anyway. The two elementary steps are the explicit frame and comma-groupoid calculations. No SGA source is used.

Mathlib hits were read: RingTheory/Spectrum/Prime/FreeLocus.lean:45–210 gives openness of a ring-module free locus and the forward inclusion under arbitrary scalar extension, but not the reverse inclusion for a sheaf flat over a separate base. freeLocus_eq_univ assumes intrinsic flatness over the module ring, absent here. Scheme flatness/base-change hits give morphism properties, not the 0CZR sheaf theorem. LocalRepresentability hits for the item concern set-valued Zariski sheaves and require a supplied open cover; they do not construct its rank-one base locus. No result is recorded as a Mathlib leaf.

## Unfinished work

The new support node intentionally remains statement-only for the next stage-1 worker. The assigned item is fully split; delivery validation follows below.
