# Worker report: lem-sfb-coordinate-weighted-adjoint

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-coordinate-weighted-adjoint.json: statement unchanged; split into five steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-scalar-integrable-integration-by-parts.json: statement; Mathlib leaf, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable, Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean:226–237.
- dag/nodes/sec-six-functors-basics/lem-sfb-continuous-compact-support-integrable.json: statement; Mathlib leaf, Continuous.integrable_of_hasCompactSupport, Mathlib/MeasureTheory/Function/LocallyIntegrable.lean:622–626.
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-nonzero-complex-reciprocal.json: statement; Mathlib leaf, ContDiffOn.inv, Mathlib/Analysis/Calculus/ContDiff/Operations.lean:802–804.
- citations.json: full verbatim statement quotes for every proof-step citation.
- searches.jsonl: the actual msearch.py log. Each new leaf records only searches present in this log, with the exact query text and observed hits. The item's inherited searches are retained.

## Attachments

None. Searches under lean/WeilConjectures for the blueprint tag, weighted/formal adjoint and integration-by-parts terminology found no project declaration stating the item. None of the three new facts is already stated by a project declaration found in the corresponding declaration-name searches.

## Wanted literature

WANTED: a local archived copy of Wenrui Kong, Notes on Complex Geometry, §6.1 Lemmas 6.2–6.3, printed pp.21–22, for lem-sfb-coordinate-weighted-adjoint. The referenced PDF is absent from literature/. I inspected the public PDF at https://cims.nyu.edu/~wk805/files/Complex_Geometry_Notes.pdf with the web reader; no repository or literature file was written. It states formal adjunction for the Dolbeault operators and their bundle-valued analogues, rather than this explicit arbitrary-weight coordinate formula. The item already identifies the coordinate formula as agent supplied. Accordingly proof_origin.by remains agent: the proof is the explicit calculation below, with Mathlib as the checked analytic input, not a claim that Kong printed this formula.

## What was wrong or incomplete

The item was unsplit with no proof. Its inherited search verdict treated open-domain localization as requiring cutoff/extension work; the actual Mathlib theorem has the stronger supportwise differentiability hypotheses needed to use zero extensions directly. I checked those hypotheses rather than asserting that both extended functions are globally smooth. The item statement is correct and was not changed. In particular, compactness of only one section suffices, no smooth boundary of U is required, and the metric on the target need not be constant.

The current blueprint chapter, the unit record sk-thm-sf-ctf-stability and the latest sk-thm-sf-ctf-stability-direct-images.proof.md (paragraph (3)) were read. This analytic auxiliary is deep in the inherited prerequisite chain of that paragraph, not a new unit route. Its inherited blueprint.from.node is null: tools/blueprint_refs.py ancestor reports None for this existing chain. The new nodes retain that ancestor and prepend the item to the inherited via list. No unit or chapter file is changed.

## Not duplicates

No Stacks tag is used: these are real-analysis facts whose direct sources are Mathlib. The whole DAG was searched by the exact declarations and by integration-by-parts, smooth inverse/reciprocal, compact-support integrability and normed-algebra terminology. Statement-only scans distinguished real smoothness from algebraic smoothness and condensed scalar material. tools/blueprint_refs.py searches for integration by parts, formal adjoint, smooth inverse, normed algebra, integrable and the three exact declaration names found no matching blueprint theorem. The broad integration/reciprocal/inversion hits concern étale trace, Fourier inversion and reciprocal roots, not these facts. The Lean project was also searched by each declaration name.

The scalar integration-by-parts leaf has arbitrary global scalar functions and explicit integrability and supportwise differentiability hypotheses; it says nothing about weighted matrices or the construction of Q. The integrability and reciprocal leaves are generic analytic tools, not clauses of the item. Their exact Mathlib declarations are used directly. The localization, coefficient computation and weighted adjoint assembly stay in the item's proof; no clause has been moved into a new unsplit node.

## Review by Q02

I read B–E of coord/delivery-errors.md in full, including its repeated imported block, against the written files. I also read each actual Mathlib signature listed above, its surrounding assumptions and its proof. Each new file introduces its objects and uses the fields of def-weil-field; support, derivative convention and smoothness are explained inline where needed. All three leaves have empty proofs and proof dependencies, complete source/file/line matches and successful semantic, Loogle and source searches recorded with the actual queries. The initial Loogle query HasCompactSupport.integrable returned no hits; the corrected query Continuous.integrable_of_hasCompactSupport returned the exact result, and both are reported honestly. No service failure was interpreted as absence. No Stacks tag or prohibited SGA source has been invented.

Step 1 uses precisely the reciprocal conclusion of lem-sfb-smooth-nonzero-complex-reciprocal. I checked its nonvanishing assumption on det(rho H_E): positivity rules out a nonzero kernel vector, hence the determinant is nonzero. Determinant and adjugate entries are explicit finite polynomials, so the inverse formula gives smooth coefficients once the scalar reciprocal theorem is applied. This is an elementary finite-dimensional algebra reduction rather than an uncited matrix inversion theorem.

Step 2 is the entrywise product rule, with C_j = rho A_j^dagger H_F and D = rho B^dagger H_F. I verified the dimensions r by s, the leading coefficient -M^{-1} C_j and the zeroth coefficient M^{-1}(D - sum_j partial_j C_j). No derivative of M^{-1} occurs in this formula. The variables are v and its real coordinate derivatives, with no complex conjugation of v, so this verifies complex linearity as well as order at most one. Finite sums/products, conjugation and differentiation of smooth scalar functions here are elementary calculus operations with their expressions written out.

Step 3 has no black-box citation: it gives the local argument for zero extension at every point, using the open cover U union (R^m minus K). I checked both alternatives separately. If u is compact, f = conjugate u_a is smooth globally and g is smooth near tsupport f. If v is compact, g = (C_j v)_a is smooth globally and f is smooth near tsupport g. The unrestricted extension may fail to be continuous on the boundary of U; the proof never assumes that it is. Both differentiability hypotheses of the cited Mathlib theorem nevertheless hold. The three product integrands are smooth on U, zero outside K, and thus continuous after zero extension. This local verification is specific to the factors in the current calculation and does not hide a separate general extension theorem.

Step 4 uses the full continuous-compact-support implication from lem-sfb-continuous-compact-support-integrable on those three integrands. Euclidean Lebesgue measure meets the source's finite-on-compacts assumption. It then uses exactly the equality in lem-sfb-scalar-integrable-integration-by-parts: both supportwise differentiability requirements and all three integrability requirements have been checked. Direction w is e_j, and real differentiation of conjugate u_a is conjugate partial_j u_a. The global integrals equal the U integrals because the integrands vanish outside U. I also checked integrability of the zero-order summands before adding them.

Step 5 is the finite matrix/finite integral expansion and cancellation MQv = rho H_E Qv. The minus sign is the integration-by-parts minus sign, rho is real so is unchanged under conjugation, and A_j^dagger has the order needed for (A_j partial_j u)^dagger H_F v. Finite-sum linearity of the integral applies to the integrable scalar functions established in step 4. The hypotheses provide no bound on the noncompact section, but only its values near the compact K enter this argument.

Small cases checked: U empty (all identities vacuous or zero); u=0 or v=0 (empty support); m=r=s=1 and constant unit metrics/density (Qv = -conjugate A times v' + (conjugate B - derivative conjugate A) times v); A_j=0 (pure multiplication adjoint); variable positive rho with A=1 (Qv = -v' - (rho'/rho)v when H_E=H_F=1); rectangular r != s; either section compact independently, including the noncompact factor unbounded near the boundary of U. The three new leaves likewise admit zero/empty support, empty U, and arbitrary direction w=0 in the scalar integration statement. No statement dispute was found.

I checked every citation against the node statement and copied the full statement into citations.json, so the supportwise qualifications cannot be lost in a short quote. Every step is under 2000 characters (600, 607, 1043, 729, 561); the two non-elementary steps cite the actual analytic results. No Lean was written and no compiler, Lake or build command was run. All writes are in the designated sandbox.

## Unfinished work

None for this one-level split. The three new analytic facts already match Mathlib, so no new unsplit item is introduced. The independent maintainer review remains the delivery process's next stage.
