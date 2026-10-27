# Stage-1 delivery: lem-trf-graded-power-torsion-polynomial-devissage

## 1. Files written

- `dag/nodes/sec-trace-formula/lem-trf-graded-power-torsion-polynomial-devissage.json`: statement, split; no exact or one-line Mathlib match. Statement and statement dependencies retained exactly. Seven complete proof steps replace the empty proof.
- `citations.json`: one verbatim statement quotation for each citation in each item proof step.
- `report.md`: this report. `searches.jsonl` was populated only by the required msearch.py command.

No new nodes; no new Mathlib leaves. Existing leaf `lem-weil-pbc-noetherian-submodule-finite` supplies the sole non-elementary algebraic input. No Lean files were written and no compiler, Lake or build tool was run. All writes are in the assigned sandbox; repository and launcher scripts were only read or invoked as instructed.

## 2. Attachments

None. Searched `lean/WeilConjectures/` by the exact item id and by graded torsion, nilpotent devissage and Hilbert-polynomial concepts. The ring-theoretic item has no project declaration giving all its clauses. The source contains scheme-theoretic Hilbert-polynomial results, which do not state this conditional graded-module assertion. The parent Hilbert-function theorem uses this item, so cannot supply an acyclic proof of it.

## 3. WANTED

None. All literature used is present locally.

## 4. Issues found and repaired

The item statement is correct; no STATEMENT-DISPUTED correction is needed. Its proof was empty. Stacks 00K1 says one can find a smaller-exponent exact sequence and then takes the largest nilpotent submodule without spelling out its finite generation, common exponent or grading. Those are now actual steps, not references: use xL and L/xL with their induced gradings, compute exactness in degree n and prove dimension additivity by bases; then construct the torsion submodule, prove homogeneity componentwise, use the existing finite-submodule theorem, take a maximum of generator exponents and test the quotient kernel directly.

I read the chapter and unit records and the current main-20261015 `lem-trf-local-term-locality.md`. This item is a historical algebra descendant recorded through the Hilbert--Samuel and formal-monoid ancestry. Its split refines that algebra only; it makes no change to the current contracting-correspondence unit route. Blueprint searches for Hilbert, graded, torsion and submodule found no imported node stating this item. Its `blueprint.from` and ancestry were retained and `same_as` is empty.

The first new Loogle query contained an unknown identifier (`graded`); it is recorded honestly as a query error, not evidence of absence. A corrected quoted `torsionBySet` query ran successfully. All old item search records are preserved. New queries and their results are copied from the actual command log; second semantic phrasing was tried. Read Mathlib `Algebra/Module/Torsion/PrimaryComponent.lean:49-64`: the ungraded power-torsion construction does not give this Hilbert-function assertion. Read `RingTheory/Polynomial/HilbertPoly.lean:18-42`: it assumes a formal rational-series presentation and explicitly lists module Hilbert polynomials as TODO. Filtration and Artin--Rees hits are also different assertions. Thus the item is split, not a Mathlib leaf.

## 5. Unfinished work

None in this one-level split. No new unsplit obligations were introduced.

## Not duplicates

No new node was created. The whole DAG was searched for 00K0, 00K1, finite graded components, Noetherian finite submodules and torsion. I read the general finite-submodule leaf, the specialized two-variable polynomial-ring leaf `lem-sc-p1-ungraded-submodule-finite`, and the stronger same-unit leaf `lem-trf-noetherian-submodule-finitely-presented`; the general existing finite-submodule leaf is exactly the needed input. The parent `lem-trf-standard-graded-hilbert-function` depends on this item and cannot be cited back. Its sibling `lem-trf-graded-injective-multiplication-polynomial-lift` assumes x injective and proves an unrelated recurrence, so is not a replacement for this split.

## Review by Q102

I checked delivery-errors B through E with the node and sources open. For the item I read Stacks `algebra.tex`, Tag 00K0 (`lemma-graded-module-fg`), Tag 00K1 (`proposition-graded-hilbert-polynomial`, particularly the first two middle paragraphs), and Tag 00IK (`lemma-Noetherian-basic`, second assertion). I read the existing parent and sibling in full to check the intended proof division and avoid a cyclic appeal to unconditional polynomiality. There are no new nodes requiring independent source or hypothesis checks.

Step 1 cites the statement of `def-pc-standard-graded-algebra`, which explicitly provides finitely many degree-one algebra generators. Splitting finite module generators into their finitely many components still spans the module; projecting onto degree n gives the finite monomial list. This proves finite-dimensionality without importing the parent Hilbert theorem. The same calculation applies to A, B and T once their finite graded structures have been shown.

Step 2 has no hidden cited theorem: I wrote out finite generation of xL and of L/xL by images of generators, computed the homogeneous components of xL and proved directness of the quotient decomposition. The induction claim is simultaneous for all finite graded modules at exponent r, so applying it to xL at r-1 is justified even if its minimal exponent is smaller; r=1 uses the actual hypothesis. Since r>1, r-1 is positive. L/xL is killed by x and uses the given hypothesis, not an induction assertion at exponent zero.

Step 3 proves degreewise exactness from the quotient grading and proves dimension additivity by a basis and lifts of a basis. I verified that finite-dimensionality comes from step 1, both eventual polynomial thresholds are present, and their maximum suffices. This is elementary assembly of the induction rather than a new lemma duplicating the item's first clause.

Step 4 writes out closure of T and checks the grading: commutativity of the standard graded algebra permits scalar closure, and the degree shift n+r is injective on nonnegative integers, so each component of an annihilated sum is annihilated. No claim that multiplication by x preserves degree is made.

Step 5 cites exactly `lem-weil-pbc-noetherian-submodule-finite`. I opened its statement and copied it verbatim into citations.json. It says every submodule of a finite module over a Noetherian ring is finite. Here the ring S is Noetherian by an explicit item hypothesis, M is finite by hypothesis, and T is a submodule by step 4. It needs no domain, regularity or injectivity assumption. I also read the pinned Mathlib `Submodule.FG.of_le` at `Noetherian/Basic.lean:381`, which supports that leaf. This is a Mathlib tool, hence requires no off-route declaration.

Step 6 uses finite generators of T from step 5 and the definition of T from step 4. The maximum includes 1 so it works with an empty generating set. Annihilation extends to all of T by linearity. Applying the already established induction theorem supplies the asserted polynomial and threshold, with no circularity.

Step 7 proves that the quotient grading is a direct sum by the homogeneity established in step 4, verifies the scalar degree rule, and proves injectivity by increasing an annihilating exponent: x times the class of m is zero implies x^a(xm)=0, whence m belongs to T. Finite generation is directly by images of generators. Each fact is an explicit elementary argument; it does not require a new node for a clause of the item.

Small cases checked: M=0 gives T=N=0 and zero polynomial; x=0 gives T=M, exponent 1 and N=0; r=1 is precisely the assumption; for k[x]/(x^r) the submodule xL has exponent at most r-1 and quotient k, so the induction terminates; for k[x] plus k[x]/(x^2), T is exactly the second summand and quotient k[x] has injective x; S=k concentrated in degree zero forces x=0 and all sufficiently high pieces to vanish. Generator degrees greater than zero merely change the threshold. No finite-dimensionality of the entire module over k is used. Every proof step is shorter than 2000 characters; none hides a comparison lemma or an omitted standard argument. Every non-elementary input is the cited existing leaf; no source restricted by the no-SGA route lock is used.
