# Stage-1 delivery: lem-trf-sepclosed-rank-one-completion

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-sepclosed-rank-one-completion.json`: item, statement, split into eight proof steps. Original statement and statement dependencies retained. No new nodes; no new Mathlib leaves.
- `citations.json`: eight citations, one for each step/node pair, with verbatim statement quotations.
- `searches.jsonl`: actual search-command log; all searches read and recorded in the item without changing the original search evidence.

## Attachments

None. Searching the current `lean/WeilConjectures/` for the exact blueprint tag and for separably closed/completion and algebraically closed/completion found no project theorem giving all clauses. The field-theory declarations concerning separably closed extensions address different claims. Mathlib's `IsAlgClosed.of_denseRange` is not an attachment or an exact leaf: its statement at `Analysis/Normed/Field/Dense.lean:45–47` requires characteristic zero and an algebraically closed dense field.

## Literature wanted

WANTED: local copy of Michael Temkin, *Stable modification of relative curves*, arXiv:0707.3953v3, proof of Theorem 2.1.8, printed p. 13, for lem-trf-sepclosed-rank-one-completion. The cited PDF is absent from this read clone. I read the online original at https://arxiv.org/pdf/0707.3953v3, PDF page 13: the paragraph following the height-zero case states that the completion of the separably closed height-one field is algebraically closed and then infers algebraic closedness of the residue field. It supplies no proof of this auxiliary fact. The proof delivered here is explicitly agent-written, rather than attributed to that assertion as though it contained an argument.

## What was wrong or incomplete

The unsplit item had no proof. Its statement is correct and has not been weakened, strengthened or otherwise changed. In particular, separably closed need not mean perfect, even in positive characteristic; using Mathlib's characteristic-zero theorem would silently lose a hypothesis case. The Mathlib TODO at Dense.lean:23–30 explicitly distinguishes the general separably-closed assertion from the implemented theorem.

The newest blueprint chapter, unit and `lem-trf-local-term-locality` statement/proof were read in `literature/blueprint/latest/`. The latter now follows contracting correspondences, whereas this item's provenance records an older Temkin supporting branch. This split concerns the existing lower lemma only; it changes no chapter or unit route and introduces no new route. The chapter/unit DAG records were also read. There is no item repair note and no previous sandbox split or report to replace.

## Unfinished work

None in this one-level split. Existing dependencies retain their own current status. No Lean was written, no compiler or Lake command was run, and neither the shared repository nor launcher files were written.

## Not duplicates

No new nodes were created. Before considering a new completion lemma I searched the whole DAG for the completion declarations and found `lem-sfb-normed-field-completion`; before considering polynomial approximation I found `lem-sfb-monic-dense-approximation`, `lem-trf-separable-monic-approximation` and `lem-trf-separable-polynomial-linear-factorization`. All are cited directly. The spectral norm and algebraic closure existence inputs already have nodes as well. Whole-blueprint searches for completion, normed field, metric completion and separable monic found no second blueprint statement identifying this item; its `same_as` remains empty.

## Review by NH

I read the original item, the current blueprint and Temkin's original passage described above. For the auxiliary analytical facts I read the local Mathlib source `Analysis/Normed/Field/Dense.lean`, the completion normed-field instance in `Analysis/Normed/Module/Completion.lean:91–95`, the norm extension in `Analysis/Normed/Group/Completion.lean:37–38`, `NormedField.instCompletableTopField` in `Analysis/Normed/Field/Instances.lean:23`, completeness and density in `Topology/UniformSpace/Completion.lean:301–302,325–327`, the isometry in `Topology/MetricSpace/Completion.lean:157–158`, and the ring homomorphism in `Topology/Algebra/UniformRing.lean:115–120`. The existing DAG statements, rather than the details hidden in their proofs, are the interfaces cited. No new node has a source to audit.

Step 1 uses the statement of `lem-sfb-normed-field-completion` for the complete field and isometric field embedding. Its hypotheses require a normed field, which the given real absolute value supplies. It does not assert nonarchimedeanness, nontriviality or density: preservation of the first two is explicitly proved in the step, and density is part of the meaning of the metric completion. Passing the strong triangle inequality to limits is justified by the norm's reverse triangle bound. Thus I did not attribute a stronger result to the cited statement.

Step 2 uses exactly the existence clause of `lem-pc-algebraic-closure-exists-unique` and the polynomial-root definition of `def-weil-algebraic-closure` to obtain an algebraic extension L/F and a root a. It then uses exactly the norm-extension conclusion of `lem-trf-spectral-norm-algebraic-extension`. That statement requires a complete nontrivially nonarchimedean normed base, now F, not the possibly incomplete original K. The extension is algebraic by the chosen closure. No completeness of L is assumed or subsequently needed.

Step 3 uses `lem-sfb-monic-dense-approximation` for monic coefficient approximation from the dense field K, then `lem-trf-separable-monic-approximation` for separable approximation over K itself. Both preserve the same positive degree d. The latter requires nontriviality and the nonarchimedean inequality, both original hypotheses on K, and explicitly requires neither completeness nor perfectness. Combining the two strict coefficient bounds uses the maximum inequality, with both bounds eta. Finally `lem-trf-separable-polynomial-linear-factorization` gives the actual product in K[T], rather than just one root; its monicity, separability and separably-closed hypotheses all hold. The number of factors is d by leading-term multiplication. I opened each cited node and copied its statement into the step's citation entry.

Step 4 is a finite computation from step 3: the leading terms cancel, lower powers of |a| are bounded by M, and a product of d nonnegative numbers smaller than epsilon^d has a factor smaller than epsilon. This argument works with multiple roots of f and with a=0, and does not use Krasner's lemma, continuity of roots, a Hensel argument, or a perfectness assertion. It is a few-line polynomial evaluation/product estimate, not an additional uncited theorem or a re-labelled clause.

Step 5 makes the limiting argument explicit. The roots b_n form a Cauchy sequence in the complete field F. Isometry of F into L makes the same convergence estimate valid there; the displayed triangle bound identifies a with the F-limit b without requiring L complete or asserting a closed-image theorem. Dividing by a nonzero leading coefficient then handles every nonconstant polynomial. This is the point at which all of the arbitrary-characteristic completion claim is assembled, rather than delegated to a new node.

Step 6 uses `def-trf-valuation-ring` only for its fraction-field criterion, which its statement really gives. Closure of the norm-bounded subring, its small-norm ideal, the description of units and maximality, and equality of the contracted small-norm ideal are written out. The fraction field is the original E because the inverse of an element of norm greater than one is integral. Step 7 explicitly checks injectivity through the contracted ideal and surjectivity through approximation at radius one. Its approximation element has norm at most one, so reduction is defined; this was checked rather than inferred merely from density of arbitrary elements.

Step 8 lifts the coefficients of a monic residue polynomial, applies the already proved root property of F, and proves the lifted root integral by the strict dominating-leading-term inequality. Reducing the evaluation equation gives the required residue root. The residue-field isomorphism from step 7 then gives the exact original residue-field conclusion. This calculation does not assume a discrete valuation, a chosen uniformizer or a finite residue field.

I checked delivery-errors B through E against the final files: self-contained statement, unchanged TeX, no statement-only node with a hidden proof, no circular citation, no clause-restating helper, no uncited non-elementary ingredient, and no use of a cited proof in place of its statement. Every actual external ingredient is an existing cited node; the elementary steps write the norm and polynomial calculations. All eight step texts are shorter than 2000 characters and none hides a separate general theorem. All eight citation quotes were checked as literal substrings of the current node statements. The Mathlib search results are actual command results: the item remains a non-Mathlib split despite hits for its supporting completion structures. Small cases checked were degree one, a=0, repeated/purely inseparable polynomials in characteristic p, nontrivial nondiscrete values, and the radius-one residue approximation; constant polynomials are not asserted to have roots. No SGA source is used.

## Validation

The required `deliver.py NH lem-trf-sepclosed-rank-one-completion --no-push` completed with exit 0 and printed `OK (not pushed)` at 44fd977e071; server preflight passed, including the DAG and split review checks. The final direct push follows the passing dry run. No local DAG/preflight/review tool or compiler was run.
