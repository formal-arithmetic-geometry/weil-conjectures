# Stage-1 report: lem-route-sp-integral-twist-level-comparison

## Files written

- `dag/nodes/sec-smooth-purity/lem-route-sp-integral-twist-level-comparison.json`: statement, split; no Mathlib match.
- `citations.json`: seven proof-step citations with verbatim excerpts of the live statements.
- `searches.jsonl`: original output records produced by the required search command.

New nodes: 0. Mathlib leaves: 0. The existing DAG already contains the non-elementary ingredients.

## Attachments

None. Searching all of `lean/WeilConjectures/` for the item tag, `spIntegralTwistLevel_comparison`, integral-twist variants and `tateFiniteLine` found no project declaration stating this item. The actual declaration is `AlgebraicGeometry.ProEtale.spIntegralTwistLevel_comparison` in `lean/Sheaf/Paper/ProEtaleTateTwists.lean:356`, and its proof is `sorry`; this is not an attachment.

## WANTED

None.

## Corrections and scope

The item was machine-generated: its statement mixed a title, proof docstring and Lean signature and had no statement dependencies. I replaced this with a self-contained mathematical statement of that exact signature and introduced the actual native restricted free-tensor level explicitly. The index is positive exponent n+1, not n; the finite coefficient is O_E/(ell^(n+1)), not the uniformizer quotient O_E/(pi^(n+1)). The lifted ring in the conclusion is retained.

There is no statement dispute. The Lean signature has no hypothesis that ell is invertible on X, and the proof needs none: it uses only the roots abelian sheaf and its specified quotient action. The blueprint's invertibility hypothesis is relevant to subsequent local freeness and finite-etale representability. Neither assertion is used here. The docstring also describes compatibility with reductions and root transitions, but the theorem signature has only a single-level existential isomorphism; the split proves exactly that theorem and adds no transition assertion.

The original source record cited an old provisional line range; I located and read the current declarations, including the definitions of spEllPointRing, spIntegralTwistLevel and tateFiniteLine. No Lean was written or compiled.

The two existing finite-discrete comparison nodes describe their sources as Bhatt--Scholze Section 5.3, and one names Proposition 5.3.2. Reading the PDF shows that this proposition concerns derived left completion, not the constant finite ring comparison. The direct discrete constant-sheaf assertion is Lemma 4.2.12. I cite that as supporting literature and use precisely the two DAG statements for the ring-object and inverse-image comparisons, rather than claim that Proposition 5.3.2 states them. Those other nodes were not edited.

## Earlier attempts and searches

The exact archive-listing command in the assignment returned no matching directories. The active sandbox contained only dispatcher markers, no item, report or searches. There was therefore no abandoned construction to repeat or evidence to misattribute.

DAG searches covered the exact native construction names, finite discrete constant-ring comparisons, roots tensor/scalar-extension descriptions and free-module constructions. I read the full statements of each cited node. I also read the unit sk-prop-an and the chapter sec-smooth-purity, the current ancestor proof in `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/sk-prop-sfb-cartesian-coefficients-twists.proof.md`, and the current Tate-twist definition in sec-proetale-coefficients. Blueprint searches used `tools/blueprint_refs.py search` with `finite twist`, `constant ring`, `tensor quotient`, `scalar extension roots`, `integral twist`, `finite Tate`, and `ring scalar extension`. They yielded the general Tate-twist definition and geometric purity statements, not another node equating this native free tensor with the ordinary finite Tate line. The ancestor command prints `None` because this provisional route node's created chain is not recognized by that helper; I retained its explicit existing ancestor, det-prop-sfb-cartesian-coefficients-twists, with its existing via chain, and replaced the provisional place by the exact finite-level formula in its integral paragraph. No new node needs an inferred ancestor.

The logged Mathlib searches use two semantic phrasings, two Loogle patterns and two source grep patterns, plus LeanSearch. All services answered. LeanFinder returned generic light-condensed monoidal/sheafification structures and presheaf module tensors; LeanSearch returned field-theoretic cyclotomic facts. The Loogle and grep patterns returned no hits. None states this coefficient-specific comparison or gives it by a one-line specialization. Exact query texts and returned names are in the node and the untouched search log. The inherited route_nodes.py grep remains identified as earlier machine evidence.

## Not duplicates

No new nodes were created. In particular I did not create another finite-discrete constant-ring comparison, another finite Tate universal property, an elementary quotient-characteristic lemma, or an isomorphism lemma restating the item's conclusion.

## Review by NB

I read delivery-errors B through E in full and checked this split against their actual mathematical failure cases.

The sources I read for the item are the current blueprint ancestor's integral paragraph and the current Tate-twist definition, together with the attached sorried Lean declaration and its concrete source definitions. For the tensor argument I read Stacks `sites-modules.tex`, Tag 03EK (`section-tensor-product`), the change-of-rings construction and `lemma-adjointness-tensor-restrict`, and Tag 03CY (`lemma-sheafification-presheaf-modules`). I read Bhatt--Scholze Lemma 4.2.12 and checked the misleading Section 5.3 pointer as described above. There are no new-node sources to audit.

Step 1 uses exactly lem-sp-ell-quotient-finite-discrete, whose statement asserts both finiteness of the ell-power quotient and continuity to the discrete target for every n>=0. Its finite-extension and topology hypotheses match the fixed embedding in the algebraic closure. The remaining quotient factorization is written out: the ideal contains its generator, hence reduction kills N, so integer representatives define the displayed unital Z/N map. I did not substitute the pi-power quotient or assume unramified E.

Step 2 uses lem-weil-pbc-finite-discrete-condensed-ring-constant for the monoidal point ring isomorphism, then lem-weil-pbc-finite-discrete-scheme-ring-constant for its pullback to arbitrary X. The first node really includes unit and multiplication; the second explicitly allows empty schemes and zero rings. Finally def-weil-pbc-internal-abelian-sheaf-module-equivalence states the internal/ordinary module equivalence and that it keeps underlying abelian sheaves and restrictions identically. Its size and monoidal-sheafification hypotheses are met by the small site and the specified sheaf tensor. This is a definition/equivalence with the needed statement, not a definition of some unrelated notion.

Step 3 cites the actual internal module axioms in sk-def-sfb-module-objects and the sheafified tensor construction in det-def-sfb-sheaf-tensor-structure. It does not assert an uncited free-object theorem: it supplies both maps and checks that they are inverse using unit, associativity and linearity, namely f(b tensor m)=b f(1 tensor m). Thus its elementary judgment concerns a direct calculation from the cited axioms. Sheafification extends the restriction-compatible bilinear formulas; no assertion that every global tensor section is itself a pure tensor is made.

Step 4 uses lem-sp-finite-tate-line-universal, not merely the definition of the finite Tate line. I checked its entire statement: it represents additive maps out of the actual roots sheaf, its Hom equivalences are natural for postcomposition, and it applies to arbitrary schemes with no ell-invertibility assumption. The Lean source finiteTateLine_universal explicitly confirms this scope. Defining j from its bijection on the identity and using naturality gives v j=i; the two displayed composite calculations then prove both inverse identities. Thus I do not invoke full faithfulness of a Yoneda functor as if it were a representability statement. Restriction of scalars changes only an action, and the internal/ordinary equivalence and coefficient transport retain the underlying abelian sheaf, so the result has exactly the target's forgetful functors.

I checked small cases: n=0 uses exponent one; ramified E still gives the correct ell-power ideal; X empty has zero abelian sheaves and the same unique inverse maps; X in characteristic ell has possibly non-lisse roots but the additive-module argument still applies; and the generic constant-ring and Hom ingredients include the zero ring. No flatness, connectedness, qcqs, finite-type or nonempty hypothesis is introduced. The proof never passes to an infinite limit or uses representability, so there is no small-index or inverse-image/limit claim to justify. Each dependency was checked for a path back to this item; none has one.

The generic coefficient and Hom nodes from other units are declared in split_report.tool_uses: they are algebraic comparison tools, not replacements for the affine-space purity route. Every proof citation has its exact statement excerpt in citations.json. Each step is shorter than 2000 characters. The proof is marked agent-written, and new unsplit nodes, proof-only clauses, duplicate lemmas and unsearched Mathlib claims are absent.

## Unfinished work

None in the stage-1 split. The attached Lean proof remains sorry, as expected for this stage. Server dry-run and push results are recorded below after the commands finish.

## Validation

Required server dry run exited successfully: `OK (not pushed) deliver/NB/lem-route-sp-integral-twist-level-comparison at 3144d2e61b8: preflight passed`. This includes the server DAG and split checks. No local compiler, Lake, global build or banned local checker was invoked. The only change after its snapshot was correcting the report's citation count from eight to seven; the node and citations were unchanged. Direct push uses the required delivery command and repeats preflight on its delivery tree.
