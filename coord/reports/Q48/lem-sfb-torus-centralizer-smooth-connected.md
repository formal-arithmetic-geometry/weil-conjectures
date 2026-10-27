# Stage-1 delivery: lem-sfb-torus-centralizer-smooth-connected

Group Q48; direct delivery; 2026-10-23. Only the sandbox was written. No Lean files, compiler, Lake, local DAG checks, repository git commands, agents, or launcher modifications were used.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-torus-centralizer-smooth-connected.json: statement; seven-step split, statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-torus-fixed-scheme-smooth.json: statement-only, unsplit; no Mathlib match. General smooth fixed-locus input, with arbitrary smooth affine X, not a centralizer assertion.
- dag/nodes/sec-six-functors-basics/lem-sfb-torus-regular-semisimple-element.json: statement-only, unsplit; no Mathlib match. A single torus point detects the centralizer functor; no connectedness conclusion.
- dag/nodes/sec-six-functors-basics/lem-sfb-solvable-semisimple-centralizer-connected.json: statement-only, unsplit; no Mathlib match. Semisimple-element centralizers in solvable groups; no torus in its statement.
- dag/nodes/sec-six-functors-basics/lem-sfb-torus-commuting-point-common-borel.json: statement-only, unsplit; no Mathlib match. Existence of a Borel containing a torus and a specified commuting rational point; no centralizer connectedness or smoothness conclusion.
- citations.json: verbatim statement quotations for every node cited in each of the seven steps.
- searches.jsonl and search-*.txt: genuine msearch queries and preserved results. The older item's searches are retained; newly added entries are taken from this group's actual log. run_searches.py records the completed first search batch; write_nodes.py constructs only sandbox JSON. milne.txt is pdftotext output of the local source, retained for review.

## Attachments

None. Read-only searches of lean/WeilConjectures by the blueprint tag, torus, centralizer, and fixed/smooth notions found matrix-centralizer equations and abstract group centralizers, not a completed declaration asserting the item or any new lemma. Existing upstream sorry declarations were not treated as proofs.

## WANTED

None: Milne iAG2017 is available locally. Generic scheme citations already have DAG nodes and Stacks sources.

## Source error

Milne Lemma 17.37, printed p.363, has a parenthesis describing a finite union over Borels containing T. That finiteness assertion is false for arbitrary T. For example, for the rank-zero torus in GL_2 over an algebraically closed field, every Borel contains T, and the Borels are parametrized by all lines in k^2, hence are infinite. Indeed a finite union of proper Borels cannot cover GL_2. The proof actually establishes the valid assertion that each centralizing rational point lies with T in some Borel. The new common-Borel lemma states exactly that assertion and omits finiteness. The item's last step uses a connected subspace through the identity for each rational point and density of closed points; it does not take an infinite union of closed subschemes to be an equality of schemes. The item's statement is true and unchanged, so it is not STATEMENT-DISPUTED.

The centralizer display in Proposition 1.92 also prints N(R) without an ambient N having been introduced there; the intended ambient group is G. Our universal-factorization calculation uses G throughout, as in that proposition's proof.

## Not duplicates

Searches were made over the whole DAG's statements, titles and sources for centralizer/centraliser, fixed point/scheme, torus, linearly reductive, Borel, and the precise Milne numbers 13.1, 13.10, 16.40, 16.42, 17.37 and 17.38. Whole-blueprint searches used blueprint_refs.py search for centralizer, torus, linearly reductive, semisimple, Borel, fixed, fixed subscheme and fixed-point; the current latest blueprint was also read by rg. The three centralizer blueprint hits are characteristic-zero matrix geometry and Cartier, not these arbitrary-characteristic group-scheme lemmas. The reported nearest ancestor is None; the inherited null ancestry and complete via chain are retained, with precise supporting places appended on the new nodes. No source for a new node cites a Stacks tag, so there are no same-Stacks-tag pairs to distinguish mechanically.

lem-sfb-torus-fixed-scheme-smooth vs lem-sfb-torus-centralizer-smooth-connected: the former concerns an arbitrary torus action on a smooth affine scheme and only the smoothness of its represented fixed locus. The item's conjugation identification and connectedness proof remain in its own steps; it is not Corollary 13.10 renamed.

lem-sfb-torus-regular-semisimple-element vs lem-sfb-torus-centralizer-smooth-connected: equality of two centralizer functors reduces a torus to a single point and says neither that either functor is representable nor that it is smooth or connected.

lem-sfb-solvable-semisimple-centralizer-connected vs lem-sfb-torus-centralizer-smooth-connected: this is Theorem 16.40 for a semisimple element and a solvable ambient group, used after a nontrivial common-Borel and regular-element reduction. It does not restate the torus clause.

lem-sfb-torus-commuting-point-common-borel vs lem-sfb-maximal-torus-centralizer-borel: the existing node assumes a maximal torus and asserts scheme containment in every Borel through it. The new node allows any torus and gives one Borel containing one specified commuting rational point. The existing node's proof depends on this item, so using it here would also be circular.

lem-sfb-torus-commuting-point-common-borel vs lem-sfb-reductive-borel-pair-structure: the latter assumes reductivity and a split Borel pair and gives root-theoretic structure. The new node requires neither reductivity nor an existing pair and asserts a common-Borel existence property for an arbitrary smooth connected group.

The existing affine-group-centre-base-change node concerns the centre C_G(G), not centralizers of a specified torus; its constant-source factorization-locus dependency is reused directly rather than duplicated. No new general representability or base-change lemma was created. Two-line subgroup tests, finite generation of a quotient, and the clopen connectedness argument remain steps, not nodes.

## Review by Q48

I read Milne's Proposition 1.92 and the paragraph after it (printed pp.33–34) for the functor and scalar extension, Theorem 13.1 and the proof via 13.3–13.7 (pp.254–256), and Corollary 13.10 (p.257) for the torus conjugation application. For the four new nodes I read respectively: (1) Theorem 13.1, including the opening statement that tori are linearly reductive and its reference to 12.30; (2) Lemma 16.42 and its faithful-representation, finitely many weight-separation argument on p.339; (3) Theorem 16.40's induction and Lemma 16.39 on pp.338–339; (4) Lemma 17.37 and its use of the fixed locus on G/B on p.363. I read Theorem 17.38 there to check their assembly. These are supporting statements only, not proof sketches embedded in new-node statements.

Step 1 cites the affine fibre-product statement for Spec(R tensor R), not merely a definition of product. Its finite-type, closed-immersion and separatedness citations explicitly give the meanings used: two copies of generators generate the tensor algebra, the diagonal is multiplication and is surjective, and separated means closed diagonal. The identical calculation works for T and for G times G, so all three schemes in the next application are separated and of finite type. I read these cited statements in full. This is affine algebra from those definitions, so the step is marked elementary.

Step 2 reads the existing constant-source closed-factorization-locus statement with precisely Y=T, S=G, X=G times G and W=the diagonal. It really supplies a unique closed subscheme and the universal property for every test scheme, and it does not require Y proper or reduced tests. Multiplication and inverse are morphisms by the group-scheme definition. The affine-spectrum statement really identifies coordinate algebra maps with morphisms; applying the commuting tests at A tensor D and its universal T-point proves the converse for arbitrary A, including nilpotents. Thus no unsupported inference from field points to a scheme-theoretic centralizer is used.

Step 3 uses only the explicit all-algebra subgroup definition, the quotient-algebra form of closed immersion, and the finite-type definition. Products and inverses of centralizing points still commute with all T-points after every algebra extension. The quotient R/I is generated by images of generators of R. This proves subgroup and finite-type assertions directly and is elementary. This argument does not use geometric connectedness, and so it can also be applied to the Borel groups later.

Step 4 uses the new general fixed-scheme smoothness lemma and the group law, after writing the equivalence tgt^{-1}=g iff tg=gt for every base extension. The lemma explicitly assumes a represented closed fixed locus; step 2 supplies that exact hypothesis, and smoothness and affine finite type of G and the torus hypothesis are the item's assumptions. No general theorem about arbitrary invariants rings is smuggled into this step. The cited lemma is Theorem 13.1 specialized to tori, not the item's smooth-centralizer clause as a replacement node.

Step 5 cites clause (2) of the existing proper-and-smooth-base-change statement, which explicitly states preservation of smoothness. Connectedness of G_K is the item's hypothesis, not a consequence asserted for arbitrary base changes of connected schemes. Finite generation of tensor scalar extension is checked on generators. The fibre-product statement gives the universal property needed for scalar extension of represented functors. For each K-algebra A, the collections of A-algebras used in the commuting tests are identical, since each inherits K from A. This is the reason C_K is the correct centralizer, with no separability or perfectness assumption on k.

Step 6 uses exactly three new statements. The common-Borel lemma says that there exists B containing the torus and the chosen rational point, without maximality. Its definition of Borel supplies smoothness, connectedness and solvability of B. The regular-element lemma is applied to B (not merely G_K), so it gives an element semisimple in B and equality of its centralizer with that of T_K on all algebras. The solvable semisimple-centralizer lemma supplies connectedness of this actual equalizer scheme with all its hypotheses now in force. A natural isomorphism of represented subfunctors gives equality of the centralizers; inclusion in C_K follows from the earlier universal property. The subgroup contains c and the identity. I did not cite maximal-torus-centralizer-borel, which both has the wrong hypotheses and depends on this item.

Step 7 takes only clause (1) from the existing affine Nullstellensatz statement: it is stated for any algebraically closed k and finitely generated k-algebra, with no characteristic-zero hypothesis. The Jacobson-space statement really gives density of closed points of the ambient scheme lying in every closed subset. C_K is affine finite type, and V is closed, so both apply. A clopen decomposition pulls back to each connected D; since the identity is in its first part the second is empty, and hence V has no rational point. Density and rationality of closed points make V empty. This is the explicit elementary topological argument needed after the cited algebraic facts; no component finiteness, smooth implies reduced, infinite-union equality, or normalizer theorem is needed.

I tested rank-zero T (C=G, regular element s=1), a commutative G (all centralizers equal G), upper triangular GL_2 with its diagonal torus (the torus is detected by a diagonal matrix with distinct eigenvalues), GL_2 with its scalar torus (C=GL_2 and one must use many Borels), products of general linear groups with nonmaximal subtori (block centralizers), and k algebraic over a finite field. In the last case a torus has no Zariski-dense cyclic point in general; the regular-element lemma only separates finitely many representation weights and does not assume such a point. The weight-separation argument yields block commutation equations with nonzero scalar coefficients, so equality persists on nonreduced A. For the smooth fixed-scheme lemma I also checked the empty X and trivial action. Solvability is essential for the semisimple-centralizer node and is explicitly assumed; connectedness is not claimed for an arbitrary reductive semisimple centralizer. The common-Borel lemma's torus need not be maximal, including the trivial torus as noted in the source correction.

Every non-elementary ingredient of the seven steps is a cited statement. citations.json records an actual verbatim statement or its relevant clause, not a proof fragment. Every new statement introduces its own objects and defines torus, semisimple, solvable, action and Borel when used, with existing definition dependencies for schemes, smoothness, groups, finite type, subgroup, connectedness and G_m. I compared the hypotheses rather than relying on titles. Every new node has empty proof, proof_deps and null proof_origin. No proof step exceeds 2000 characters (all are below 1000); no hidden lemma is left in a long step. The statement and import/history fields of the item are retained. Generic off-unit uses are declared in split_report.tool_uses and are explained below; the latest blueprint direct-image/alteration route is unchanged.

All four new nodes and the item have semantic searches in two phrasings, a Loogle pattern, and a real logged Mathlib grep. I read the returned signatures: the hits are abstract fixed-point sets and group centralizers, Lie algebra or root-system assertions, or general smooth-locus facts, none of which is the required scheme assertion or a one-line specialization. The second regular-element LeanFinder phrasing was also run and logged after narrowing the general affine-action query to exactly the group assertion. Searches were reused after the interruption, not invented or silently rerun.

## Generic tools and route

lem-pc-proper-base-change is used only for smooth scalar extension; lem-weil-pbc-fibre-product-affine-spectra only for affine tensor products. lem-sc-lft-over-field-jacobson-space and clause (1) of lem-wf-affine-nullstellensatz-vanishing supply density and rationality of closed points. They are general scheme/algebra facts, not alternate six-functor, alteration, trace-formula or duality routes. No lemma of the unit states these facts; they are explicitly declared generic tools in split_report. The chapter and unit records and latest blueprint unit/direct-image proof were read. The imported item is a supporting node, not the unit's key statement, so no unit realization record is changed. No SGA source is used.

## Unfinished work

The four supporting lemmas remain unsplit stage-1 items by design. This delivery completes one level of the assigned item, not their proofs or any Lean formalization. Dry-run and push outcomes follow below when available.

## Validation

The required deliver.py --no-push command exited 0 and printed: OK (not pushed) deliver/Q48/lem-sfb-torus-centralizer-smooth-connected at 6c894c5e9be: preflight passed. The remote checks passed; no diagnostic repairs were required. The dry-run process exited before starting the final push. Four new nodes, zero new Mathlib leaves.
