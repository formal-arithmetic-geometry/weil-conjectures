## Files written

- `dag/nodes/sec-smooth-purity/lem-cbc-finite-extension-reduction-cone-bound.json`: the item, now split with four proof steps and no new nodes.
- `citations.json`: verbatim statement excerpts for every dependency used in every step.

## Attachments

None. I found no finished declaration with this exact statement in the project source.

## WANTED

None.

## What was wrong in the node, blueprint, or brief

The imported item was unsplit even though its source sentence already identifies the intended route. Its statement distinguishes the completed coefficient sheaf \(A_T\) from constant coefficients, so I retained that distinction and made the proof pass through the existing completed-constant-sheaf reduction node. No statement correction was needed. No duplicate node was created: the existing two-term resolution for the pulled-back condensed coefficient ring has a different ambient coefficient category, while the existing completed-constant-sheaf reduction node supplies the flatness and quotient identification used here.

## What I could not finish, and why

Nothing remains unfinished in the stage-1 split.

## Review by Q06

I read the item node, its parent `thm-cbc-finite-extension`, the unit `sk-prop-sf-cbc`, and the source material in `literature/stacks-project/sites-modules.tex`, `literature/stacks-project/derived.tex`, and the imported completed-coefficient nodes. I also checked the source's old split location: the parent proof invokes this item for the common finite-level amplitude bound.

Step 1 uses exactly the finite quotient information in `def-weil-l-adic-coefficient-extension`, the short-exact-sequence preservation in `lem-weil-pbc-constant-module-section-properties`, and the flatness, quotient identification, and completed-vs-constant distinction in `lem-weil-pbc-completed-constant-sheaf-reduction`. The DVR hypothesis supplies injectivity of multiplication by the uniformizer; tensoring the constant exact sequence by the stated flat completed sheaf gives the \(A_T\)-module resolution. I verified that the quotient is finite and that every map has the displayed completed coefficient category.

Step 2 now cites `def-pc-kflat-complex`, `lem-pur-quasi-iso-cone-acyclic` and `lem-pc-tensor-mapping-cone-iso` explicitly. Their statements give respectively acyclicity after tensoring an acyclic complex, the equivalence between a quasi-isomorphism and an acyclic cone, and the natural comparison of the tensor of a cone with the cone of a tensor map. I apply them to the augmentation of the exact two-term resolution from Step 1, rather than assume that an arbitrary tensor preserves quasi-isomorphisms. The signed flip is written explicitly with the total differential of `def-pc-tensor-complex-sheaves`. `lem-pur-derived-change-of-rings` clause (2), and the K-flat resolution clause of `def-weil-pbc-adic-coefficient-datum`, identify the resulting quotient complex with the derived quotient in its correct category. Restriction of scalars uses the same-underlying-sheaf statement of `def-pc-sheaf-restrict-scalars`.

Step 3 uses the natural tensor-cone isomorphism again, now for the multiplication map on the unit module, and the explicit cone-triangle structure in `def-weil-abstract-derived-category`. This is stronger than the abstract TR1 axiom: it says precisely that the displayed concrete cone triangle is distinguished in the derived category. I checked naturality on a chain map by the augmentation square on tensors, and resolution independence by clause (2) of `lem-pur-derived-change-of-rings`. Clause (1) and the augmentation square show that a quasi-isomorphism between K-flat representatives also induces a quasi-isomorphism on the cone model, which justifies descent of these natural squares. Thus no cone functor on an arbitrary triangulated category is assumed.

Step 4 uses the exact long cohomology sequence in `lem-sf-derived-homology-long-exact`, the cohomology-sheaf definition in `def-weil-derived-cohomology-sheaves`, and the same-underlying-sheaf clause of `def-pc-sheaf-restrict-scalars`. I checked both boundary cases: \(q<a-1\) forces vanishing from the \(q\) and \(q+1\) terms, while \(q>b\) does the same; \(q=a-1\) is retained, so the asserted vanishing interval is \([a-1,b]\). The argument is independent of \(n\). Small cases \(n=1\), \(a=b\), \(M=0\) were checked. The dependency closure has no cycle, and the existing Mathlib searches were read and retained; they found only generic cone/completion APIs, not this completed-sheaf assertion. No SGA source or route substitution is used.

## Continuation repairs

The retained dry run failed because the restriction-of-scalars quotations omitted the Markdown emphasis in the current statement. I copied the current statement verbatim. Re-reading also exposed the unsupported use of abstract triangle axioms for a concrete cone, and the unexpressed reason why the tensor comparison is a quasi-isomorphism; Steps 2 and 3 now cite the existing concrete derived-category, K-flat, tensor-cone, and cone-acyclicity statements that actually supply those facts. No new node or statement change was needed. I restored the item's original creator metadata from the current repository rather than attributing its creation to this split.

I read the current main-20261015 finite-extension statement and proof (under `sec-six-functors-basics/sk-thm-sf-pf-field`): the parent transports the integral result by rationalization and uses finite-level amplitude. This subsidiary uniformizer argument supplies the amplitude bound and does not change that route. I read Stacks `sites-cohomology.tex`, definition-derived-tor and lemma-derived-tor-quasi-isomorphism-other-side, and `derived.tex`, lemma-cohomology-homological, in addition to the constant-exact and completion-flat sources named above. The generic tensor-cone, K-flat and cone-criterion statements were read in full before citing them. The tag-to-label table identifies the K-flat definition as 06YN and the derived-category definition as 05RU (definition-unbounded-derived-category); I corrected these precise source labels. Every step is below 2000 characters. The imported Mathlib search records are unchanged; the sandbox had no searches.jsonl to replay and this repair creates no nodes or changed search questions.

For sharpness, take $M=(A/I)_T$ in degree zero on a nonempty geometric point: multiplication by $\varpi^n$ is zero, so the reduction has cohomology in degrees $-1$ and $0$. Thus the extra degree at the lower end cannot simply be removed. For the empty scheme all the module sheaves vanish and the same proof applies. A DVR is Noetherian, and its uniformizer-power quotient has the displayed two-term finite free resolution, so the Noetherian and perfect-quotient hypotheses of the cited coefficient datum are satisfied.
