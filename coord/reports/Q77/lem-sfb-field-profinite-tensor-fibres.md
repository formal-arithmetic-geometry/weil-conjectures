# Stage-1 report: lem-sfb-field-profinite-tensor-fibres

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-field-profinite-tensor-fibres.json — statement, now split into eight proof steps; no full Mathlib match.
- citations.json — fourteen verbatim statement quotations, one for each step/node citation.
- searches.jsonl — five actual search results recorded by msearch.py (LeanFinder twice, Loogle, grep, LeanSearch); the item's earlier Q82 searches are retained.
- report.md — this report.

New nodes: 0. New Mathlib leaves: 0. The statement and statement dependencies are unchanged. No unit realization is changed because this is not the unit's key node. All writes were confined to this item's sandbox; no Lean files or compilers were used.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag and the profinite tensor/fibre notions found no declaration stating this item. ModuleObject/Basic.lean supplies test objects, and RingTheory/Spectrum/Prime/LocallyConstant.lean supplies the general prime-spectrum homeomorphism, but neither states the full algebra-map classification, its topology, and its two naturality assertions. The latter belongs to the already existing lem-weil-pbc-locally-constant-prime-spectrum; no new attachment claim is needed.

## WANTED

None. Read Bhatt–Scholze, The pro-etale topology for schemes, Examples 4.1.9–4.1.10, printed pp. 27–28 (PDF pp. 27–28), and Stacks proetale.tex Tag 097D (lemma-construct-profinite), limits.tex Tag 01YW (lemma-directed-inverse-system-affine-schemes-has-limit), algebra.tex Tags 00U3 (lemma-etale-over-field) and 00U2 (lemma-etale, part (11)). The source's examples give the tensor and field-site descriptions, not all the explicit intermediate-field/evaluation formulas. Accordingly the expanded proof is marked agent-written, with that source as its context.

## What was wrong or incomplete

The live item was statement-only, with no proof and no Lean audit declaration. Its statement is correct, including nonnormal intermediate fields and the empty parameter. The proof must not identify Emb_k(L,Omega) with a quotient G/H without explaining its topology; we avoid needing that additional result. In particular L is not assumed finite or normal. Also, the test-object node's LC identification is only over Z: we do not cite it for the desired identification over L. We prove the L-valued ring colimit and use the general spectrum/colimit theorem.

During the C4 check I noticed that the test-object statement assumes a finite-quotient presentation rather than proving that one exists. Step 1 now cites the existing same-unit lem-sfb-cofinal-clopen-partition-reconstruction for exactly this assertion, and explicitly verifies directedness. No new node was needed.

The inherited blueprint.from.node is null, as confirmed by tools/blueprint_refs.py ancestor. I retained its existing precise place and via chain rather than inventing an ancestor. The split realizes the geometric input previously isolated from step 8 of lem-sfb-field-profinite-galois-site, below the coefficient-topology comparison, and changes neither the chapter route nor the unit's cohomological steps. Blueprint searches for locally constant functions, separable closure, Emb_k, geometric fibres of profinite, LC(P, and 097D found no blueprint node stating the full item. The existing condensed-point basis has related separably closed-field assertions, not this general intermediate-field naturality statement.

## What remains unfinished

Nothing in this stage-1 split. Existing cited nodes may remain open in their own stages; their proofs are not being claimed here. The independently reviewed landing remains the maintainer's responsibility.

## Not duplicates

No new nodes. Reused the existing partition reconstruction, finite-stage factorization, prime-spectrum, affine-limit, finite-separable-etale, finite-product-etale and field-etale-structure nodes instead of creating special cases or clauses of the item.

## Mathlib searches

I read the five results in searches.jsonl. LocallyConstant.evalₐ, coeFnAlgHom, constₗ, comapₐ and mapₐ construct the maps; they do not classify all algebra maps or prove this product homeomorphism. InfiniteGalois.proj, algEquivToLimit and limitToAlgEquiv concern the Galois group's own inverse limit. The second LeanFinder phrasing also found WeakDual.CharacterSpace.continuousMapEval_bijective and homeoEval_naturality: those have RCLike coefficients and continuous-map/linear-dual hypotheses, rather than arbitrary algebraic separable intermediate fields and locally constant rings. Hence they are not one-line specializations of this item. The actual grep hits at Algebra.lean lines 343, 407 and 449 were read in context; these are the precomposition, postcomposition and constant algebra maps. No unavailable query was reported as a negative match, and no unexecuted query was recorded.

## Review by Q77

I read delivery-errors B–E in full and checked the actual statements rather than using facts from their proofs. The construction follows Examples 4.1.9–4.1.10; the explicit algebra argument was checked against the Stacks affine-limit and etale-field constructions just listed. There are no new nodes whose sources, definitions, searches or duplicate pairs need auditing. Each proof step is below 1200 characters, so none hides a long independent lemma under the 2000-character threshold.

Step 1 uses the partition reconstruction statement to obtain a limit of finite discrete quotients, checking that all finite clopen partitions form a small, nonempty, directed cofinal system. The factorization statement then applies to the locally constant map with codomain the underlying set of L; it explicitly allows empty limits. The universal property of the ring colimit is written out, using surjectivity of the quotient maps to check equality at a common refinement.

Step 2 uses the small-diagram spectrum/colimit statement exactly as stated; the smaller-universe quotient set is an actual small index. The finite-product spectrum computation is elementary and is written through coordinate-idempotent localizations, rather than being borrowed from a definition. The test-object node supplies the scheme limit defining L[P], not the LC ring identification over L.

Step 3 uses the separable-closure statement only for algebraicity/separability and finite subextensions. A finite list of values generates a finite separable subfield within L; refining the partitions and enlarging that field makes the union directed. The finite-separable-etale node gives scheme etaleness of each K, the product node expressly includes the empty product/zero ring, and the ring/scheme-etale equivalence expressly gives finite presentation. The ind-etale definition is then used only after an actual filtered presentation has been supplied; it is not cited for a preservation theorem.

Step 4 applies the prime-spectrum statement with R=L, so Spec L is a singleton. The kernel of a unital map to a field is prime by the elementary no-zero-divisor argument. Subtracting the constant value proves the factorization without needing an extra assertion about residue fields. The constant restriction is injective since L is a field and P is nonempty. The empty case is treated separately, since constants are not an injective copy of L in the zero function ring.

Step 5 uses the etale-algebra-over-field-product statement solely for finite-dimensionality of a finite etale subalgebra. A finite basis lies in one K^{P_i}, so that family of stages is cofinal among the subalgebras used in the topology. On every stage the evaluation map depends on two discrete restriction coordinates, proving continuity in the precise stipulated topology. Step 6 checks the other direction independently: constants detect embedding restrictions, while basic opens D(f) and the finite stage containing f make the kernel map continuous. The cited prime-spectrum homeomorphism then recovers p continuously. This uses its statement's homeomorphism clause, not merely its pointwise formula.

Step 7 writes out the three actual compositions of functions, so the action is postcomposition/left translation and the field-inclusion map is restriction in the correct direction. Step 8 is the elementary finite-root-set permutation proof: no normality of the intermediate L, no algebraic-closure hypothesis, and no unsupported assertion that an arbitrary field embedding is surjective is used. Algebraicity of Omega/k supplies the finite root set. Agreement on finite intermediate fields gives the same coset neighbourhood basis on embeddings and on automorphisms.

I tested P empty, P a singleton, finite P, L=k, L=Omega, k separably closed, and nonnormal finite intermediate fields. P empty gives the zero ring, empty scheme and empty Hom space. A singleton gives Emb_k(L,Omega). For L=k there is one coefficient embedding and the action on P is trivial. For L=Omega the finite-root argument gives G and the Krull topology. None of the computations assumes a characteristic, perfection, nonempty quotient blocks in the empty case, or a finite extension L/k.

All fourteen entries in citations.json were copied verbatim from the cited live statements. proof_deps is precisely the union of uses. Generic off-unit tools are declared in split_report.tool_uses with the role each plays; the partition reconstruction is already in this item's unit. No citation is to the parent item or a descendant depending on this item. There is no statement dispute, no source error, no changed target and no SGA route.
