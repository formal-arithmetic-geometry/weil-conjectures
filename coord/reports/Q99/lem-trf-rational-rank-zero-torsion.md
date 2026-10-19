# Stage-1 delivery: lem-trf-rational-rank-zero-torsion

## Files written

- dag/nodes/sec-trace-formula/lem-trf-rational-rank-zero-torsion.json: statement, unchanged; split into four steps using existing nodes. Mathlib has module-rank, torsion and localization machinery, but no exact direct declaration for this rational-tensor criterion was found.
- citations.json: one verbatim statement quotation for each cited node in each proof step.
- report.md: this report. searches.jsonl is the actual search-command log.

No new nodes; no new Mathlib leaves. The existing localization and tensor-product dependencies are Mathlib leaves.

## Attachments

None. The whole WeilConjectures/ source tree in the supplied slopmaster2 checkout was searched for the blueprint tag, rational rank, rank_eq_zero_iff_isTorsion and related rational-tensor wording. No project declaration states the item. Rational Tate-module declarations concern a different object. Master is reference material and was not used as evidence of a finished proof.

## Wanted literature

WANTED: literature/temkin-stable-modification-arXiv-0707.3953v3.pdf, §2.1 notation before Lemma 2.1.2 and Proposition 4.3.1 proof p. 27, for lem-trf-rational-rank-zero-torsion. The inherited source says the local archive is unavailable; the proof here is explicitly agent-written, using the locally available Stacks algebra.tex, not attributed to an unread Temkin proof.

## Audit and changes

The statement is true for arbitrary abelian groups, with no finite-generation assumption, and is unchanged. The original node had no proof. I supplied the argument, retained its ancestry and source metadata, and retained the previous worker's searches while adding only the searches actually run by this worker. No maintainer-owned fields, unit records, live source or tools were edited.

The three blueprint levels were read in SETUP.md. The fixed chapter is sec-trace-formula and the unit sk-i-curve-zero has the contracting-local-term route. This item is a generic algebraic input many levels below the imported lem-trf-local-term-locality; the current main-20261015 statement and proof of that ancestor were read. Nothing changes their route. blueprint_refs.py ancestor confirmed the inherited ancestor; search for "rational rank" found no imported duplicate. The whole DAG was also searched for rational rank, zero-rank criteria, torsion and localization/tensor comparisons. Existing general localization nodes were reused instead of creating special rationalization nodes. The elementary dimension-zero and sign arguments were kept as steps, not made into nodes.

The freshly logged searches include two semantic phrasings (rank after fraction-field tensoring; vanishing after localization), LeanSearch, Loogle and source grep. The hits were read: Dimension/Finite.lean:59 is rank_eq_zero_iff; Dimension/Torsion/Finite.lean:31 is Module.rank_eq_zero_iff_isTorsion. Their rank is the rank of the original module, whereas the statement defines rational rank using its Q-tensor product. Module.rank_baseChange (Dimension/Constructions.lean:371) requires a free original module, which is unavailable here. The general IsBaseChange rank lemmas in Dimension/Localization.lean:193 and :216 have further localization/base-change hypotheses, so none of these is an exact direct specialization for the item. The proof instead makes the tensor/localization comparison explicit with an existing Mathlib leaf. LocalizedModule.subsingleton_iff is relevant background, but the proof only needs the already represented elementwise kernel criterion. All successful search entries marked "no match" mean no direct match for the item; their actual hits are preserved verbatim in the results logs.

## Review by Q99

I read the item's statement and its rational-rank definition, the full statements of all four dependencies, and the Stacks source algebra.tex at Tag 07JZ (definition-localization-module, including the preceding fraction construction and the localization map) and Tag 00DK (lemma-tensor-localization, including its proof). I verified these tag-label pairs in stacks-project/tags/tags. I also read the existing tensor-localization-over-base leaf: it is general in R -> A, T, M and N; it is not the merely principal-localization lemma. The item's Temkin reference was not locally available, so the missing archive is reported above and proof_origin is agent.

Step 1 uses exactly def-trf-rational-rank's displayed definition, with its cardinal vector-space dimension. Its elementary argument is written: a hypothetical nonzero vector gives a linearly independent singleton because every nonzero rational is invertible, contradicting the supremum defining dimension being zero. No finite-dimensionality or finrank-zero inference is used. This is a few-line argument from the definition of dimension, not an extra unproved linear-algebra lemma.

Step 2 uses def-weil-pbc-module-localization's actual fraction equivalence relation and operations. For the module Z, a nonzero integer cannot annihilate a nonzero integer. Thus the relation is precisely equality by cross multiplication for rational fractions; every rational has such a representation. This checks that S^{-1}Z is Q rather than silently assuming an arbitrary ring localization is Q. S contains 1, is closed under products, and excludes 0. The same node introduces S^{-1}G without restricting G.

Step 3 uses exactly the isomorphism and formula in lem-weil-pbc-localization-tensor-over-base, with identity ring map Z -> Z, multiplicative set T=S, module M=Z and arbitrary module N=G. Every abelian group is a Z-module by integer multiplication. Both sides of the cited formula consequently have the required types. The two tensor unit maps and the symmetry maps are given explicitly, with the inverse calculation on pure tensors supplied by def-weil-pbc-module-tensor-product's universal property, balancing relation and generating property. The functorial localization of the unit maps is part of the statement of def-weil-pbc-module-localization, not borrowed from its proof. These compositions yield theta(g/s)=g tensor 1/s. This is one routine application of the existing localization theorem and the unit/symmetry identifications, not a hidden new comparison theorem. In particular it establishes S^{-1}G=0 from Step 1 without assuming G flat, free, torsion-free or finitely generated.

Step 4 uses the sentence "In particular m/1=0 if and only if um=0 for some u in S" that is actually in def-weil-pbc-module-localization's statement. The nonzero integer annihilator is converted to its positive absolute value by the two explicit sign cases. This proves the precise n>=1 convention and does not assert a uniform exponent for G. All cited statements are quoted verbatim in citations.json. proof_deps is exactly the union of uses. All off-unit dependencies are existing Mathlib leaves or definitions, so no route exception is needed.

I checked B through E of delivery-errors.md against the files: no new node, no duplicate, no proof hidden in an unsplit statement, no restatement of this item as a new lemma, no statement weakening, no unexplained clearing of denominators, no stronger hypotheses. Edge cases checked: G=0; finite cyclic groups; Q/Z and an unbounded direct sum of finite cyclic groups (torsion need not have a common exponent); G=Z and G=Q (rational dimension one, so the hypothesis fails); infinitely generated and infinite-rank groups (cardinal dimension avoids the invalid finrank shortcut). The graph edges point only to existing general leaves/definitions. The four proof-step lengths are 491, 613, 1058 and 378 characters, all below the long-step threshold. No Lean was written and no compiler/build tool was run.

No prior returned delivery was present. The corrections in this delivery are the previously missing proof and the explicit tensor-order, fraction-ring and positive-exponent identifications. No mathematical dispute was found.

## Unfinished work

None in the stage-1 split. Acquisition of the missing Temkin archive remains a literature request; the elementary algebraic proof is complete from the available source and existing nodes.
