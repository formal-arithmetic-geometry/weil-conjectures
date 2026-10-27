# Stage-1 report: lem-sfb-pd-derivation-compatibility-closure

Group Q88, direct delivery, 2026-10-24.

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-pd-derivation-compatibility-closure.json`: statement; split into five explicit elementary calculations. Mathlib verdict: no exact match or one-line specialization.
- `citations.json`: nine step/dependency entries, each quoting a verbatim part of the cited dependency statement.
- `report.md`: this report. `searches.jsonl` was produced by the required search tool; `write_split.py` is a sandbox-only drafting aid.

Zero new nodes and zero Mathlib leaves. Only the item JSON and the report are intended delivery files; no Lean or unit file changed.

## Attachments

None. Searched the live `lean/WeilConjectures/` tree for the exact item id and divided-power/graded-derivation notions. The only relevant project hits concern a Koszul graded derivation and a source citation for divided powers on Tor, not this assertion. There is no project declaration covering the compatibility locus. The item has no existing Lean attachment or audit declaration to inspect.

## WANTED

None. The needed Stacks source is present.

## Corrections and source checks

The item was unsplit, with no proof and no earlier sandbox node or report. Its statement, source, statement dependencies, creation record and blueprint provenance are retained. No STATEMENT-DISPUTED issue was found. The node is auxiliary calculus, not a claim that Stacks explicitly states this lemma: 09PG gives the axioms, and 09PS omits the operator-extension details. The supplied proof is therefore marked `proof_origin.by = agent`.

I read the chapter record and the unit record, and the current blueprint files in `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`, in particular `_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`. This remains an algebraic input to the inherited Tate-resolution/lci chain below direct-image step (3). It does not replace a chapter or unit route. It is not the key statement of the unit, so there are no realization edits.

`blueprint_refs.py ancestor` confirms that the existing ancestry has null blueprint ancestor. I preserve that null value and the full inherited via chain and precise place. Whole-blueprint searches for `divided power` and `derivation`, and a search of the latest blueprint text for divided powers/odd derivations/09PG/09PS, find no duplicate statement. A whole-DAG search for 09PG, 09PS and divided-power compatibility finds the two definition nodes, the parent free-operator lemma, its curvature parent, and ordinary divided-power construction/descent nodes. None is a more general version of this item. No new node is needed: differentiating each displayed defining identity is a direct finite calculation rather than an unstated auxiliary theorem.

The fresh searches were executed through msearch.py and their exact tool/query/results were copied from searches.jsonl. Both semantic phrasings were read. Basic.lean:79-96 gives ordinary divided-power axioms only. DPMorphism.lean:62-65 requires a ring homomorphism, so it cannot be applied to an odd signed derivation. SubDPIdeal hits require divided-power closure as a hypothesis and do not prove this compatibility locus has that property. The existing inherited searches remain in the node; no historical query is represented as newly executed. All fresh services responded; none was recorded as unavailable.

## Unfinished work

No mathematical gap remains in this one-level split. The only dependencies are the two existing definitions, and there are no new queued items. No compiler, Lake, global build or local delivery-check script was run.

## Not duplicates

There are no new nodes, hence no new/existing same-tag pairs. In particular, I reused `def-sfb-nonnegative-strict-graded-algebra` and `def-sfb-graded-divided-power-structure` rather than introducing parity, scalar-calculus, or compatibility-clause nodes.

## Review by Q88

I read Stacks `dpa.tex`, section-tate (09PF), lines 951-962, the complete definition-divided-powers-graded (09PG), lines 965-983, its following observation about ordinary divided powers, and lemma-get-derivation (09PS), lines 1433-1471. The latter explicitly allows the lifted operator to have nonzero square. The former includes both signed commutativity and the independent zero square of odd homogeneous elements. The statement needs exactly those hypotheses; no freeness, flatness, torsion-freeness or vanishing of D squared is added.

I opened and read the complete statements of both cited nodes. The strict-graded-algebra definition supplies finite homogeneous decompositions, the parity submodules, commutation of even elements and zero squares of odd homogeneous elements. The divided-power definition supplies the positive-even domain, gamma zero convention, all five ordinary axioms and the extra homogeneous odd-product vanishing. These are statement clauses, not details inferred from their proofs. The nine verbatim citation entries are checked against these statements.

Step 1 uses these two definitions to extend signs by finite distributivity, observe D(1)=0 from the negative-degree convention, and apply the scalar axiom with zero to show gamma_n(0)=0. There is no division or assertion that an arbitrary degree-changing map is a ring homomorphism. The n=1 boundary case is established here for every input.

Step 2 uses exactly the sum axiom and even commutation. Differentiating the two factors gives the two written sums, the gamma_0 derivative terms vanish, and reindexing gives the desired equation. Both inputs are in the positive even ideal as required; the n=1 instance is treated without using a sum axiom outside its positive-index range.

Step 3 uses the product/scalar axioms and parity. The displayed induction differentiates a^n even when a is a finite sum of even homogeneous elements. Importantly D(a) need not vanish. Its term is converted using x gamma_(n-1)(x)=n gamma_n(x); dropping that term would be an incorrect proof. The positive even part is an ideal, so ax is an allowed input. The n=1 boundary is separate. There is no cancellation of n in the algebra.

Step 4 uses only the divided-power definition. The iteration and product axioms give the two displayed coefficients. Their equality follows by substituting factorial formulas as rational numbers and then using their known integrality; it is an equality in the integers before they act on A. It neither embeds A in a rational algebra nor cancels a factorial in A. The cases n=1 and m=1 are separated, so the remaining coefficient formulas have strictly positive arguments. The equality of integer rational expressions is elementary arithmetic, not a hidden comparison theorem.

Step 5 uses the odd-product axiom and strict commutativity. Odd homogeneous degrees are positive in a nonnegative grading. D(u) and D(v) have even degree, allowing the two explicitly written reorderings. For n=2 the potentially nonzero right side is killed separately by v squared and u squared; for n>=3 the lower divided power itself vanishes. It is essential to distinguish n=2 from n>=3. No inference about gamma on a sum of odd products is made.

I tested the zero ring, a degree-zero-only algebra, the zero operator, n=1, m=1, n=m=2 (both iteration coefficients are 3), and characteristic two. The odd-square axiom is used directly, so no cancellation of 2 is concealed. The example with an exterior generator u of degree 1 and a divided-power generator x of degree 2, with D(u)=1 and D(x)=u and D(gamma_n(x))=u gamma_(n-1)(x), has D squared of x equal to 1; all five arguments still apply. This checks that the proof does not silently assume a differential. For nonhomogeneous even scalars the parity extension in step 1 and power induction in step 3 supply the actual argument.

Against delivery-errors B-E: no statement-only subnode contains a proof because there are no new nodes; each nontrivial input is an axiom explicitly stated by a cited node; every other inference is a written finite differentiation, reindexing or coefficient calculation. There is no new dependency cycle (the item's two statement dependencies are already its only proof dependencies). No step merely applies a renamed copy of a clause. Every step is under 1000 characters, with no hidden long-step extraction. Only Stacks and the current blueprint are used; no SGA route is introduced.

## Validation

The required server dry run is run after writing this report; its final result is recorded below before pushing.

Server dry run on 2026-10-24 exited 0: `OK (not pushed)` at `e3fc32b9226`, preflight passed (including the required DAG and split checks). The final report is checked once more before direct delivery.
