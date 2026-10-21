# Stage-1 report: lem-sbc-reflected-compositor-unit-normalization

## Files written

- `dag/nodes/sec-smooth-base-change/lem-sbc-reflected-compositor-unit-normalization.json`: statement, split; five proof steps using two existing Mathlib leaves. Original statement, source, creation record, blueprint ancestry and imported searches retained. Actual searches from this worker appended.
- `citations.json`: one verbatim statement quotation for every step/node citation.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No unit record changed: this item is an auxiliary descendant, not the key statement of its unit.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the exact blueprint id, reflected compositor, completed composition and completion units. The completion comparison in `CategoryTheory/DerivedCategory/Complete/IntegralCompletion.lean` compares completing before and after a functor preserving the completion kernel. It does not state the prescribed reflected-conjugate/ambient-conjugate equation under this item's abstract hypotheses. No project declaration giving all clauses was found.

## WANTED

None. All sources needed for the proof are present locally.

## Corrections and scope

The imported item had a statement and searches, but no proof. The statement is correct and was preserved verbatim, as were its two statement dependencies. No STATEMENT-DISPUTED issue was found.

The proof route is the ordinary/reflected transpose calculation requested by its parent `lem-sbc-completed-operations-linear-natural-exchange`, current step 3 (inherited old step 5). That parent's normalization step realizes the integral-operation comparisons needed before the central-localization sentence of `sbc-thm-e-coefficient-smooth-base-change`. I read the current main-20261015 proof, the corresponding current DAG statement and proof, the recorded chapter and unit, and the current coefficient unit `_section.md`. Nothing here changes a chapter or unit route.

An important hypothesis check: `lem-sbc-reflector-adjunction-unit-formulas` assumes additive linear categories, whereas this item assumes only categories. I read its statement and did not cite it. The few-line formula needed here follows directly from the reflected Hom bijection already specified in this item's hypotheses, and is written in step 1. The square-mate factorization node is likewise not a premise: it concerns a different, four-category square. No new node was made for these elementary computations or for a restatement of this item's conclusion.

Nothing remains unfinished in this split. Its two generic dependencies are already Mathlib leaves; this is not a claim that a Lean proof was written or compiled.

## Searches and blueprint comparison

Ran the required msearch command with this item's group/id for LeanFinder (two different phrasings), Loogle, source grep and LeanSearch; read every returned hit list and the relevant source declarations. The sandbox `searches.jsonl` records the exact calls. The JSON preserves the imported search entries and appends only this worker's actual queries and results. All four services answered successfully.

Candidates read include `Adjunction.homEquiv` and `homEquiv_unit` (Basic.lean:160 and 181), `unit_conjugateEquiv_symm` (Mates.lean:311), `conjugateIsoEquiv` (Mates.lean:425), `Adjunction.leftAdjointCompIso` (CompositionIso.lean:72), and the reflector Hom bijections in Reflective.lean. These provide the pieces but do not individually state this item or specialize to it in one line: the two successive transposes and the naturality of d at the completion unit must still be calculated. Thus the item is split, not declared a Mathlib leaf.

Searched the whole DAG for reflector/adjunction/compositor/transpose concepts and the relevant Stacks tags, and searched the whole imported blueprint with `blueprint_refs.py search` for `compositor`, `reflection`, `conjugate`, `reflector`, and `completion unit`. No other blueprint statement gives this abstract normalization. `blueprint.same_as` is therefore empty. The ancestor command confirmed `sbc-thm-e-coefficient-smooth-base-change`, and the existing precise `from.place` and `via` are retained.

## Not duplicates

No new nodes. The existing `def-weil-pbc-composite-adjunction` supplies composite Hom bijections and `lem-weil-pbc-conjugate-iso-unit-equation` supplies conjugacy, rather than recreating either fact.

## Review by NR

I read Stacks `proetale.tex`, Tag 099N, `lemma-pushforward-Noetherian-case`, especially clause (2) and its proof, which points to the completed pullback adjunction. This source motivates the reflector setup but does not itself state the abstract normalization identity. Accordingly this split's proof origin is agent, not an attribution of the calculation to Stacks. For the actual categorical proof I read `categories.tex`, Tag 0037 (`definition-adjoint` and the following explicit unit/transposition formulas), Tag 0DV0 (`lemma-compose-counits` and its proof), and Tag 0B65 (`lemma-transformation-between-functors-and-adjoints` and its Hom-set proof). There are no new nodes needing separate literature sources and no SGA source is used.

Step 1 uses the stated hypotheses and the definition of an adjunction: the reflected transpose of t is the ordinary transpose of t composed with k. Applying this to the identity gives the reflected unit. I checked that fullness gives the requisite identifications of Hom sets and that right-adjoint preservation puts the targets inside the stated subcategories. This is not an application of the stronger additive reflector lemma.

For step 2 I opened both cited nodes. `def-weil-pbc-composite-adjunction` explicitly states that its Hom bijection is the composite of the two Hom bijections. `lem-weil-pbc-conjugate-iso-unit-equation` explicitly gives a unique natural isomorphism of left adjoints and the equation R1(c) eta1 = delta eta2. The substitutions are L1 = P12 P01, L2 = P02, R1 = D10 D21, R2 = D20 and delta = d restricted to C2. Right-adjoint preservation makes these functors well typed; fullness includes the inverse of each d component, so this is an isomorphism, not just a transformation. These citations supply existence, naturality, invertibility and the specific transpose characterization, not merely a uniqueness statement.

Step 3 cites only the composite-adjunction definition for its identification of the two successive transposes. Its actual comparison is the displayed three-line unit-naturality calculation. I checked each domain: k01 starts at L01 M, the first ordinary transpose has source L01 M, the reflected one has source P01 M, and R21 N lies in C1. Thus the second reflected Hom bijection applies. This calculation needs no inverse of any completion unit and hides no additional categorical lemma.

Step 4 cites the conjugacy-unit node again, now for L1 = L12 L01 and L2 = L02 in the ambient categories. The direction delta = d agrees with step 2. Functoriality gives the transpose after postcomposing by k02; the written equality uses naturality of d at k02 to identify that transpose with d at P02 M composed with the reflected unit. Injectivity is that of the ordinary composite Hom bijection, not faithfulness of R10 R21. This establishes the requested equality and its inverse-transpose description without cancellation of k. The citation quotation in citations.json includes exactly this node's unit equation.

Step 5 cites no theorem: it expands naturality of the two k factors, then c^c, then k02 and c. I verified the natural-transformation source is the restricted ambient L12 L01, while the intermediate reflected composite is P12 P01. Consequently the proof addresses the naturality clause as well as the pointwise equation.

I checked small cases. With all reflectors identity the equation is precisely the same conjugacy on both sides. With all ambient categories Ab and ambient adjunctions identity, take C0 = Ab, C1 the groups killed by p^2 and C2 those killed by p, with the quotient reflectors. For M = Z and p = 3, all three displayed k maps are noninvertible (Z to Z/9, Z/9 to Z/3, Z to Z/3), and the equation is equality of the two quotient maps. Taking d = minus identity instead gives minus the quotient map on both sides, also checking the conjugacy direction with a nontrivial d. The zero object gives the unique zero map. These cases require no nonemptiness, additive, smoothness or geometric hypotheses in the abstract proof.

I reviewed delivery-errors B through E point by point. There are no new-node self-containment, tag, duplicate or missing-search issues (B); each non-elementary input is an existing cited statement with its verbatim quotation and no imported proof is used as a premise (C); the item's argument is carried by its own calculations, with no clause moved into a new node and no cyclic dependency (D); and the domain, restriction, conjugacy orientation and noninvertible-unit checks above address the mathematical failures in E. Every proof step is below 2000 characters. The elementary flags apply only to definitions, displayed unit/naturality calculations and injectivity of the already given Hom bijection. The conjugacy existence/isomorphism step is non-elementary and cites the existing Mathlib leaf.
