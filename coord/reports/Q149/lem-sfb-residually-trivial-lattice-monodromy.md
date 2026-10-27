# Q149 stage-1 report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-residually-trivial-lattice-monodromy.json: item, statement retained; ten proof steps, status split.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-group-prime-power-exponent.json: statement, Mathlib leaf IsPGroup.iff_card, Mathlib/GroupTheory/PGroup.lean:102. IsPGroup is the exact elementwise hypothesis at lines 25-27; the implication is the forward direction at lines 102-106.
- citations.json: one verbatim statement quotation for each of the 24 step/node citations.
- report.md: this report.

The sandbox contained no item or prior report. I copied the live item, retaining its earlier searches, source, blueprint provenance and all maintainer-owned fields. New searches are recorded by msearch.py in searches.jsonl. No repository or launcher file was written, no git command was run there, and no Lean or compiler tool was used.

## Attachments

None. Searches for the blueprint tag and for residually trivial, congruence monodromy and finite monodromy in lean/WeilConjectures found no exact item declaration. Existing FiniteMonodromyTrivializingTorsor covers F_ell rather than A_n; FiniteSetMonodromyTorsor does not specify the image group or its ell-power order. Neither is an attachment for this item. The project occurrence of IsPGroup.iff_card in Curve/AffineGeneric is a use of the general theorem rather than a project declaration of the new leaf.

## Wanted literature

None needed for this split. The local-field facts are cited as the existing lemma lem-sf-bc-adic-ring-domain, not re-proved or attributed to an unobtained source. Its coefficient-completion assertion is not used.

## Corrections and scope

No statement correction or statement dispute. The item correctly requires a separate cover for each n and allows rank zero. Its source place is composite agent-formulated material: Bhatt--Scholze Proposition 6.8.4(1) itself says the integral-to-reduction-tower equivalence is easy and leaves its proof to the reader. I do not cite that sentence as a proof. Instead the steps supply the quotient identification, the local models, the transitions and the group calculation. I retained proof_origin.by = agent. Stacks 03SF is the Galois-cover section; the fundamental-group theorem itself is 0BND, and the proof cites it under that tag.

The item has no imported blueprint ancestor: blueprint_refs.py ancestor prints None. I kept its existing provenance through the parent lattice-potential-Kummer-tameness input into det-thm-sf-ctf-stability-direct-images proof (3). I read the fixed chapter and the sk-thm-sf-ctf-stability unit, including the warning about no uniform trivializing cover; the proof does not assert such a cover. No unit realization is due: this is not the key statement of that unit.

## Not duplicates

lem-sfb-finite-group-prime-power-exponent vs lem-exc-finite-group-cauchy: the latter is Cauchy's theorem for a finite subgroup of field automorphisms; the new leaf directly converts elementwise prime-power exponents into group cardinality for a finite matrix subgroup over any commutative ring. It is a one-line application of a different Mathlib theorem.

lem-sfb-finite-group-prime-power-exponent vs lem-sc-primary-pgroup-filtration: the existing statement constructs a filtration of a primary module under an already given ell-group; it does not establish the cardinality criterion.

lem-sfb-finite-group-prime-power-exponent vs lem-exc-infinite-tame-inverse-limit: that statement assumes prime-power orders in an inverse system, whereas the new leaf establishes the finite cardinality conclusion from elementwise exponents.

Whole-DAG statement/source searches for IsPGroup.iff_card, IsPGroup.exists_card_eq, congruence kernels, and prime-power exponents found no existing node giving this implication. Blueprint searches for IsPGroup, IsPGroup.iff_card, finite group prime power exponent and prime power exponent returned no equivalent statement. The two blueprint hits for congruence concern different constructions. Extra searches for connected-cover/orbit statements led to reusing cor-galois-open-subgroups rather than creating another node. No new Stacks-tag node is introduced.

## Review by Q149

I read Bhatt--Scholze, The pro-etale topology for schemes, printed pp.58-60: Definition 6.8.1, Lemma 6.8.2, Definition 6.8.3 and Proposition 6.8.4, including its omitted proof of (1). I read proetale.tex lemma-compare-locally-constant (099Y) in full, and pione.tex theorem-fundamental-group (0BND), section-finite-etale-under-galois (03SF), and the connectedness discussion in lemma-finite-etale-connected-galois-category (0BNB). I also read sites-modules.tex lemma-flat-pullback-exact (04JC). For the new leaf I read Mathlib/GroupTheory/PGroup.lean lines 25-39 and 98-106. It states exactly the implication after unfolding IsPGroup, without requiring commutativity or nontriviality of G.

Step 1 uses the continuous-section exact-sequence lemma with multiplication by a nonzero uniformizer power. Its hypotheses really allow linear maps rather than requiring the first map to be a ring homomorphism. Division by the fixed scalar is continuous on its image; the finite discrete quotient has an open kernel. The pulled-point functor is explicitly a left adjoint, so its preservation of this cokernel is supplied by the general left-adjoint colimit lemma. No unsupported left exactness of point pullback is needed. The coefficient definition supplies the actual quotient maps and finite rings.

Step 2 uses the stated lisse cover, the exactness theorem for underlying abelian inverse images, the Cartesian coefficient theorem, and the finite-discrete internal/ordinary equivalence. I checked that the last theorem is for an arbitrary scheme T, without a Noetherian restriction. It gives both the constant ring identification and preservation of the actual free models. It is stronger than a definition of module objects and supplies the identification actually used.

Step 3 cites the type-locus statement, which explicitly gives disjoint clopen subschemes for finitely presented constant module types. Free finite modules satisfy that hypothesis. Connectedness leaves the type seen at the chosen point; equality of ranks is the elementary cardinality comparison over the finite nonzero residue field. Thus all stages have the same d, not just locally some rank.

Step 4 uses both the uniform-model etale-cover statement (retaining A_n^d) and the local-system comparison equivalence, followed by the exact fully faithful classical-module comparison. These citations actually assert the needed equivalences. The nested scalar cokernels have exactly the same relations; faithfulness then gives the quotient cocycle. This makes the compatibility about the actual maps rather than arbitrary isomorphisms between unmarked models.

Step 5 uses only clause (1) of cor-galois-lisse-representations. It explicitly permits arbitrary connected schemes with a point and finite rings, and includes scalar-change compatibility and the trivial unit representation. The Noetherian/separated/invertible-ell hypotheses in clause (2) are not used. Full faithfulness reflects the assumed residue trivialization. Basis change preserves identity reduction.

Step 6 uses the ring-only portion of lem-sf-bc-adic-ring-domain: finite quotient rings and residue characteristic ell. Thus ell is in the uniformizer ideal. I wrote the binomial argument and its induction explicitly, checking the linear term as well as the higher powers. Every term moves at least one ideal level for i >= 1; the argument also works at ell=2 and for ramification. This step is elementary relative to those stated ring facts. It does not hide a separate congruence-filtration theorem. The new leaf is used in step 7 separately for K_n and Q_n, both finite as subsets of the finite matrix set; no uncited subgroup-order theorem is needed.

Step 8 uses the pointed open-subgroup classification, not an unpointed classification that would only give conjugacy. It gives a connected cover and positive constant finite locally free degree. The fundamental-group equivalence identifies its fibre with the cosets of its stabilizer; lem-galois-transitive applies using the explicitly cited conversion from scheme connectedness and the existing Galois-category instance. The kernel is open by continuity to a finite discrete matrix group. The quotient-to-image bijection and the commuting right multiplication formula are written out. In the left action a sends q to q a^{-1}; this choice makes the action law agree with multiplication in Q_n.

Step 9 uses the finite-limit and fully faithful parts of thm-galois-fundamental to lift the explicitly bijective action map. Its inverse formula is checked: if r=q a^{-1}, then a=r^{-1}q. This proves the torsor on every geometric fibre, rather than just the marked one. Positive finite locally free degree ensures these fibres are nonempty. The same cited theorem states the stabilizer description after finite etale base change; the finite module equivalence on the connected P_n turns the trivial restricted action into the constant free module. The internal/ordinary equivalence already established in step 2 retains the underlying abelian sheaves throughout.

Step 10 checks n=1 and d=0 explicitly. The identity cover is connected and finite etale since X is nonempty connected, and group order one is ell^0. For p different from ell, a power of ell is prime to p. Nothing selects a cover simultaneously for infinitely many n.

Against delivery-errors B--E: the sole new node is self-contained and proof-free, with verified Mathlib declaration and line numbers. Every cited node's statement was opened, and citations.json was checked as literal substrings, not paraphrases. All uses are in proof_deps. Non-elementary comparison and Galois-theory inputs are cited rather than concealed as elementary steps. No proof step exceeds 2000 characters (the largest is 1041). No new lemma restates a clause of the item: the only new fact is an finite-matrix-group specialization of the abstract criterion already in Mathlib. Generic off-unit tools are declared in split_report.tool_uses with their precise purpose. No route is replaced and no new dependency points back to this item.

## Unfinished work

None in the one-level split. The statement-only dependencies already in the DAG remain their own items. Validation and delivery are through the required server dry run followed by deliver.py.

## Dry-run repairs

The citation checker required a longer quotation for lem-galois-transitive; citations.json now quotes its whole statement. The first server preflight required a notion citation in the new leaf. I specialized the abstract criterion to the finite matrix subgroups actually used, explicitly introduced their multiplication, identity and inverses, and cited the existing matrix definition. Mathlib searches for this contextual formulation still return IsPGroup.iff_card as an immediate specialization. This changes neither the item statement nor its proof argument. The existing lem-sfb-finite-matrix-group-coprime-power proves bijectivity of a coprime power map from a group-order hypothesis; it does not establish the prime-power cardinality concluded by this leaf.


## Returned-delivery repair (2026-10-22)

The return in coord/returns/Q149.md identifies the approved returned head as e78ef166054 and explains that the side completion was not promoted to the live queue DAG. This is the retained returned-delivery sandbox, including its proof, report, citations and 22 logged searches; those searches were read and reused, not invented or repeated. The earlier paragraph saying that the sandbox was initially empty describes the original submission, not this repair.

I compared the retained item with the current live item. The live statement, statement dependencies, source and blueprint provenance agree; the live item remains unsplit with no assembly proof. The new Mathlib leaf is absent from the live DAG. I refreshed every non-stage-1 field from the current item rather than treating the side completion as live. The required delivery tool rebases the overlay on the current origin/sheaf-dag itself; the initial repair dry run finished successfully at e0be3e040bc and did not push.

I reopened all twenty current proof-dependency statements, not merely the quotations: the coefficient definition and point pullback, continuous-section cokernels, left-adjoint colimits, lisse cover, geometric inverse-image exactness, Cartesian coefficients, finite-discrete module equivalence, type loci, uniform-model etale cover, finite-presentation comparison, exact classical comparison, finite-coefficient Galois representations, local-field ring facts, pointed open subgroups, fundamental-group equivalence, transitivity, connected-object conversion and the finite-etale Galois-category assertion, together with the retained Mathlib leaf. All twenty-four retained step/node quotations are still verbatim. In particular, no change in the current cited statements invalidates the uses enumerated in Review by Q149 above. I reread Stacks 099Y and 0BND/03SF and Bhatt--Scholze printed pages 58--60, and checked the Mathlib definition and iff_card implication again.

The proof adjustment is in step 5: it now explicitly composes the actual reduction transitions from n to 1, identifies A_1 tensor_{A_n} G_n with G_1, and only then invokes scalar-change compatibility of the finite-coefficient representation equivalence. This checks the residual-triviality inference against the current finite-coefficient clause, without invoking its more restrictive ell-adic clause. All citation entries remain applicable. The statement, one-level split and sole Mathlib leaf are retained, as requested by the approved mathematical review. All proof steps remain below 2000 characters; n=1, rank zero, ell=2 and ramified coefficients still satisfy the written argument. No common cover is introduced. A final dry run and push follow this repair record.
