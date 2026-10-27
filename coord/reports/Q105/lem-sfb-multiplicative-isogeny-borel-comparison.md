# Stage 1 delivery: lem-sfb-multiplicative-isogeny-borel-comparison

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-multiplicative-isogeny-borel-comparison.json: item, six proof steps, status split. The statement and its hypotheses are unchanged. Preserved the earlier recorded searches and added the actual Q105 searches.
- dag/nodes/sec-six-functors-basics/lem-sfb-borel-quotient-lifting.json: new statement-only node; no Mathlib match. A prescribed Borel lifts through an arbitrary faithfully flat quotient of smooth connected affine groups. This has no multiplicative or finite kernel assumption.
- dag/nodes/sec-six-functors-basics/lem-sfb-borel-scheme-normalizer.json: new statement-only node; no Mathlib match. The normalizer theorem for every smooth connected affine group, on every test algebra.
- citations.json: a verbatim statement excerpt for every citation in the six item steps.

Two new nodes, zero Mathlib leaves. Searches are recorded by their exact tool and query with authentic results from searches.jsonl. Both new nodes have two different semantic phrasings plus LeanSearch, Loogle and Mathlib grep; all services answered. The earlier intersection searches are retained in searches.jsonl, but produced no new node: the existing unipotent-to-multiplicative vanishing lemma proves the required intersection assertion directly.

## Attachments

None. Searched the current read-only lean/WeilConjectures source for the item's blueprint tag and for Borel, normalizer and isogeny. The normalizer declarations found concern abstract subgroup operations and Hopf vanishing ideals, not the Borel normalizer theorem. The isogeny declarations concern abelian varieties or formal gluing. There is no project declaration stating the item in full.

## WANTED

None. Milne's Algebraic Groups PDF is present and was read locally; the generic descent and fppf permanence inputs have Stacks sources present locally.

## Problems found and changes made

The imported item had no proof. Milne 18.18 compresses the inverse-image Borel assertion and the character-row surjectivity into a few lines. The split supplies scheme-theoretic centrality, a Borel lifting, containment of the entire kernel, a local lift argument identifying the inverse image, the actual inverse of the quotient map, and extension of characters through the diagonal quotient of a triangular embedding. A field-point argument alone would miss infinitesimal kernels. No source statement error or statement dispute was found.

The current latest blueprint unit and its direct-images proof were read, as were the stored chapter and unit records. The item's existing creation chain records the older alteration/PGL-cover prerequisites of direct-images proof (3). This work splits that already dispatched prerequisite without editing its parent chain or changing the unit's proof. blueprint_refs.py ancestor prints a null blueprint ancestor for this existing created-node lineage; the two new nodes inherit exactly that null ancestor, prepend this item to via, and identify the precise Milne supporting argument in from.place. Searches across the entire imported blueprint for Borel, quotient Borel, normalizer and multiplicative groups found no matching blueprint statement; same_as is empty. The existing item blueprint and all maintainer metadata are preserved.

## Not duplicates

lem-sfb-borel-quotient-lifting vs lem-sfb-central-isogeny-borel-root-compatibility: the existing node assumes a reductive target and a finite central kernel and also asserts root/coroot compatibility. The new node treats arbitrary quotient kernels and arbitrary smooth connected affine groups, including nonreductive ones; its Borel-lifting assertion is needed before the specific inverse-image calculation.

lem-sfb-borel-quotient-lifting vs lem-sfb-general-borel-flag-variety: the existing statement constructs a flag scheme and its group action for a single group. It states no theorem about images or lifts of Borels through quotient homomorphisms.

lem-sfb-borel-scheme-normalizer vs lem-sfb-general-borel-flag-variety: the existing statement gives the scheme stabilizer of a point of the flag scheme, but identifies the action with conjugation on Borels only for elements of G(k). It does not identify the normalizer subgroup functor on arbitrary test algebras or families of conjugate subgroups. A nonreduced central kernel cannot be handled just by that rational-point equivariance clause. The new statement gives precisely N_G(B)(A)=B(A) for every A, as Milne 17.48 states scheme-theoretically.

lem-sfb-borel-scheme-normalizer vs lem-sfb-maximal-torus-centralizer-borel: the existing statement concerns the centralizer of a chosen maximal torus, not the normalizer of a Borel subgroup. It does not supply the present central kernel containment without additional maximal-torus inputs.

The new nodes are not restatements of the item's clauses: quotient lifting is an existence assertion for arbitrary quotient maps, and the normalizer theorem is about a single group and its Borel. The item itself proves equality with the full inverse image, the quotient isomorphism, and all character exactness clauses. No new node contains a proof sketch or any proof steps. Neither new source cites a Stacks tag, so there are no same-Stacks-tag pairs to add.

## Review by Q105

I read Milne Proposition 18.18 and its diagram on printed p.391, Proposition 17.20 on pp.357--358 for the lifting node, and the full scheme-theoretic Normalizer Theorem 17.48 with Lemma 17.47 on pp.366--367 for the normalizer node. For the supporting character argument I read Theorem 12.9 on pp.233--234, Proposition 16.2 on pp.324--325, Theorem 16.26 on pp.332--333, Lie--Kolchin 16.30 on pp.334--335, and Corollary 14.18 on p.284. For the quotient formulation I read the Homomorphism Theorem 5.39 on p.108 and the quotient statements recorded by the existing DAG nodes. I also read Stacks descent.tex lemma-fpqc-universal-effective-epimorphisms (Tag 023Q) and topologies.tex lemma-fppf (Tag 021O).

Step 1 uses the actual statement of connected-action-multiplicative-type-rigidity: its acting group is G_1, which is smooth and connected, and its acted-on group is diagonalizable N, which need not be smooth. Conjugation preserves N by the kernel formula written in the step. The lifting node supplies a Borel B mapping faithfully flatly and finitely presentedly to the prescribed B_0. The normalizer node supplies N(A) contained in B(A) because central elements normalize B after every A-algebra extension. This avoids claiming that finiteness makes the kernel reduced or etale.

Step 2 uses fppf-covering-base-change to lift f(g) along B to B_0. The calculation gb^{-1} in N is written explicitly. Representable fpqc descent gives maps into B, with equality after inclusion checked by uniqueness; thus it supplies membership on the original test algebra, not only on closed points. This is a short elementary sheaf-local calculation from the cited statements, and is marked elementary. The kernel of the restriction is the same defining fibre product N, and all of N has already been put inside B.

Step 3 uses homogeneous-orbit-quotient-geometry for representability and local coset representatives for the two quotients. The homomorphism-factorization node gives a finitely presented faithfully flat quotient for f; its residual closed immersion has zero defining ideal since f is faithfully flat, so f itself admits the required fppf local lifts. The explicit test for equality of cosets is f(g^{-1}g') in B_0, equivalent to g^{-1}g' in B_1. This proves both independence of representatives and the two inverse identities. Yoneda is cited only for the representable-functor bijection it actually states, not for an unrelated evaluation formula.

Step 4 applies the faithfully-flat-group-quotient-universal statement with G=B_1, Q=B_0, H=G_m and scheme-theoretic kernel N. The factorization and uniqueness clauses give exactness and injectivity. The maps are precisely the specified pullback and restriction maps. Triviality on N is required as a morphism, not just on F-points.

Step 5 applies Lie--Kolchin to the smooth connected solvable B_1; termination of its derived series directly gives the finite normal-series hypothesis of that node. The triangular-diagonal-kernel node supplies a group morphism d, its scheme-theoretic unipotent kernel V, and a diagonalizable quotient D. The intersection K=N intersect V is unipotent by restricting the stated unitriangular closed immersion, so unipotent-to-multiplicative-trivial applies to its inclusion into N, with no smoothness assumption on K or N. Hence K=1 and d restricted to N is a monomorphism on all algebras. The monomorphism-closed-immersion node applies to these separated finite-type group schemes. This intersection argument takes only a few lines from those statements and definitions, so I did not make a separate node for it.

Step 6 uses exactly the closed-immersion/surjective-character-map clause of multiplicative-character-antiduality. D is a closed subgroup of a split torus by the diagonal-kernel node, and N is diagonalizable by the item's hypothesis, so both are of multiplicative type; algebraic closedness makes the character group in the cited separable-closure formulation the one used here. A character of D is pulled back by d; its restriction to N is the chosen character by the defining composition. Thus the restriction map, not merely some abstract map, is surjective.

I checked the trivial group, the identity isogeny, and tori with t mapped to t^n, including n divisible by the characteristic. For t mapped to t^p the character sequence is 0 to Z, multiplication by p, to Z to Z/p to 0, and the flag schemes are points. This tests the nonreduced mu_p kernel explicitly. The same argument covers the nonreductive example G_a times G_m with identity on G_a and t mapped to t^n on G_m. The lifting lemma also applies to quotients with unipotent kernel, for example projection G_m times G_a to G_m, so it is strictly independent of the item's diagonalizable-kernel statement. The normalizer theorem allows G itself solvable, in which case B=G, and dimension zero, where both groups are trivial.

I checked every proof citation against its node statement and copied the used clauses verbatim into citations.json. All cited nodes introduce the objects and hypotheses used. The only generic off-unit citations are fppf base change, representable descent, and Yoneda; these are existing Mathlib leaves and are additionally declared in split_report.tool_uses. No SGA source is used. No step exceeds 2000 characters, and no comparison or substantial lemma is hidden in a long step. Nothing is unfinished mathematically at this one-level split: only the two deliberately statement-only supporting nodes remain unsplit for later workers.
