# Stage-1 report: lem-sp-compact-support-tower-reduction

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-compact-support-tower-reduction.json`: statement, split; statement and statement dependencies retained exactly. Four proof steps reuse existing nodes. The item is not in Mathlib.
- `citations.json`: twelve verbatim statement quotations for all step/node citation pairs.
- No new nodes, no Mathlib leaves, no unit edits. `searches.jsonl` contains the five actual Mathlib searches for this attempt; the node retains its earlier search records as well.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for compact-support towers, reduction/lower-shriek, and tower Tor notions, and checked `dag/lean_names_upstream.json`. No project declaration states all clauses. `AlgebraicGeometry.Etale.AdicSystem.compactSupportTower` in `SixFunctors/Etale/Derived/AdicSystem.lean:305` is a normalized tower of global compact cohomology over a point, not an operation on arbitrary nonnormalized strict sheaf towers with the stated uniform interval. The reduction isomorphism in `SixFunctors/Etale/Derived/Exchange.lean:198` does not identify the actual strict-tower reductions or give the uniform bound. Neither is claimed as an attachment.

## WANTED

None. The proof assembles existing DAG theorems along the recorded route. Its source is agent-written, not a claim that Stacks proves this combined tower statement directly.

## Issues corrected

The imported item had no proof. Its statement is consistent with the main-20261015 tower-geometric gamma proof (3), and was not changed. I made explicit the bounded-below input needed for finite evaluation, the etale-origin condition of the bound theorem, the geometric-fibre dimension condition, and the preservation hypothesis in the existing shriek calculus. No statement dispute or route departure was found.

## Not duplicates

No new nodes. Existing `lem-sp-coefficient-tower-shriek-calculus` (3) already gives the whole actual reduction identity, while `det-sp-tower-bound-uniform` supplies the bound. Creating a new lemma for either would duplicate existing work. `lem-sp-tower-transition-compatibility` is the underlying section-normalized reduction result; the existing shriek calculus already packages it without the extra coordinate notation. Searches of the whole DAG and `tools/blueprint_refs.py search` for tower reduction, compact support and coefficient-independent bounds found no separate blueprint node equal to the full item, so `blueprint.same_as` stays empty. The ancestor tool gives `det-sp-integral-adjunction-bijection`, as retained in the item.

## Review by Q142

I read the worker brief, stage-1 contract, SETUP's three levels and human requirements, GOAL, the item's chapter and integral-adjunction unit, both copies of delivery-errors B–E, the current gamma proof (3), the current uniform-bound statement, the gluing proof's Uniformity and Levels paragraphs, and the integral-adjunction-bijection proof's Normalization paragraph. These sources prescribe the strict-tower route used here; no finite-purity proof or SGA route is invoked. The Lean 4 skill was used only for reading/search guidance. I created no Lean files and ran no compiler.

For step 1, I opened the statements of `def-weil-l-adic-coefficient-extension`, `sk-def-sp-normalized-towers`, `det-sp-coefficient-towers-abelian`, and `det-sp-tower-shriek-levels`. They respectively give finite quotients, common intervals, exact level evaluation with levelwise kernels/cokernels, and the bounded-below compactification evaluation. Exact evaluation gives the displayed cohomology equality; a tower sheaf with zero at every level is zero, so bounded-below membership follows without asserting faithfulness of derived evaluation. This checks the evaluation theorem's input domain.

For step 2, I opened `lem-sbc-smooth-relative-dimension-permanence` and `def-sbc-smooth-morphisms`: base changing to a geometric point still has smooth relative dimension d, hence its nonempty fibre has dimension d. The empty fibre satisfies the bound. I opened `lem-weil-pbc-finite-ring-constructible-derived-origin`; its statement covers arbitrary finite commutative rings, so it gives the witnesses required for the etale-origin interpretation of the finite functor. The statement of `det-sp-tower-bound-uniform` explicitly gives constructible output, the Tor interval [a,b+2d], and cohomology vanishing outside it for a tower of the stated finite rings. These are precisely the uniform conditions in `sk-def-sp-normalized-towers`. Thus preservation of the relevant full category is proved before applying the calculus that assumes it. No normalization of C is used.

For step 3, I read all of `lem-sp-coefficient-tower-shriek-calculus`, especially (3), and `det-sp-reduction-direct-image`. The former states equality of the actual derived reductions, not just existence of coefficient isomorphisms, and explicitly identifies the proper part as the scalar-adjoint counit transpose followed by the open tensor comparison. The latter fixes exactly the comparison b in the item and explicitly removes flatness and finite-projective-dimension assumptions. Its coefficient rings are finite and killed by powers of ell, as checked in step 1. Both apply to the same compactification and ordinary uncompleted coefficient derived categories. I did not cite only a definition for this non-elementary equality.

For step 4, `det-sp-coefficient-towers-abelian` (3) explicitly supplies the quotient-composition coherence for canonical reductions in the ambient derived category. Step 3 has already identified our formula with those maps, so the conclusion uses the statement, not an unstated computation in its proof. At an identity index the strict transition is the identity and the scalar-adjoint map is the tensor unitor. This is a direct definition check, not a new lemma about mates.

I tested the assembly for n=m, a three-level quotient chain, d=0, zero and empty schemes, ramified E (the levels are en, not n), and a nonnormalized tower with zero transitions. The latter retains zero image reductions, which is allowed: the proof never treats them as isomorphisms. Nonflat examples such as Z/ell^2 to Z/ell require no extra hypothesis because both reused results explicitly work with derived scalar extension. There are no new statements to test. Each proof step is under 2000 characters and hides no new intermediate claim. All citations in citations.json were checked as exact substrings of the live statements. I checked that the reused proof dependencies do not transitively depend on this item. The off-unit generic hypothesis checks are declared as tool uses; the compact-support formula and bounds follow the unit's existing tower route. There are no changes to the target, unit or chapter statements.

## Unfinished work

None in this stage-1 item. New prerequisites were unnecessary because the DAG already contains the needed theorems. The maintainer's independent mathematical review remains part of normal delivery.
