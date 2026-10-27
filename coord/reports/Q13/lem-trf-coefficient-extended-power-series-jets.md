# Q13 stage-1 delivery: lem-trf-coefficient-extended-power-series-jets

## Files written

- dag/nodes/sec-trace-formula/lem-trf-coefficient-extended-power-series-jets.json: item, statement, split; no full Mathlib match. Nine proof steps, unchanged statement and statement dependencies.
- citations.json: one verbatim statement quotation for each of the 23 step/node citations.
- searches.jsonl: actual msearch output records; the item retains its inherited searches and appends this attempt's searches.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the project under lean/WeilConjectures by the exact blueprint docstring tag and by power-series, jet, coefficient-extension, tensor and graded terminology. No declaration states every clause. The existing combined-ideal coefficient theorem is only an input, not an attachment for this item. Its project source was read at lean/WeilConjectures/RingTheory/PowerSeriesCombinedIdealCoefficients.lean, especially the statement at line 172. No Lean was written or compiled.

## WANTED

None. The proof is explicitly agent-written; no external theorem about completed tensor products or coefficient-extended formal series is assumed. The needed exactness sources are available in literature/stacks-project/algebra.tex.

## What was wrong or missing

The item was unsplit and had no proof. Its statement is correct; no STATEMENT-DISPUTED correction is necessary. The former parent argument has now been replaced at this level by an explicit finite relation calculation and a kernel calculation. In particular, the proof does not identify the full algebraic tensor product L tensor K[[X]] with L[[X]], which would be false for general infinite field extensions.

The latest blueprint snapshot is main-20261023-1620 (7284bb09daf97437d544c51882b325f9c52cd345). I read its trace-formula chapter, sk-i-curve-zero unit and lem-trf-local-term-locality proof. They now use the contracting-correspondence route. This auxiliary item comes from the retained historical nearby-duality/alteration branch through the parent smooth-local tangent-cone comparison, as its inherited blueprint.from records. No chapter or unit was changed and the historical ancestor chain was retained. Searches of the entire imported blueprint for power series, finite jets, coefficient extension and associated graded did not find a node stating this comparison. The item is not the unit's key node, so no realization record was edited.

## What could not be finished

Nothing mathematical remains. Delivery validation is recorded below after the required server checks.

## Not duplicates

No new nodes were created. The existing combined-ideal coefficient criterion handles powers of variables and a coefficient ideal, but not field extension of an arbitrary ideal quotient. Existing flat tensor exactness, tensor right exactness and field-module flatness nodes provide exactly the needed generic tools. The polynomial-coefficient conormal tensor quotient node has different objects and conclusion, and was not used. The associated-graded ring structure node supplies the ring laws and homogeneous representative product formula. No clauses of this item were repackaged as new nodes.

## Review by Q13

I read coord/delivery-errors.md B--E in full, the stage-1 brief, stage and worker rules, the three blueprint levels in SETUP.md, GOAL.md, the chapter and unit records, the current blueprint files named above, the parent tangent-cone node, and every cited node's statement. For the item the substantive source is the explicit finite coefficient argument written here; Stacks algebra.tex Tag 00DF (lemma-tensor-product-exact, lines 1993ff) and Tag 00HD (lemma-flat, lines 8707ff) were read in full statement and proof context, with their tags verified in tags/tags. Definition 00HB (definition-flat, lines 8620ff) was also checked. These sources give exactness, not the complete jet theorem. For the variable-power input I read the existing combined-ideal node, its upstream proof and the current blueprint's complete-over-complete-base proof, paragraphs 1--3. There are no new nodes whose source needs a separate review.

Step 1 uses the combined-ideal criterion with coefficient ring K or L, respectively e or e+s variables, zero base ideal, and positive power. Its statement explicitly allows any commutative coefficient ring and zero variables. The associated-graded definition supplies the ideal-power convention. The quotient equalities follow directly by lifting finite sums of products of generators. Nothing about closedness or finite generation of I is used.

Step 2 uses exactly the tensor universal property and bilinearity and the power-series finite Cauchy product. Both inverse coefficient maps are written down. The finite set of monomials is finite because e and m are finite, regardless of the dimension of L over K. This is an elementary coordinate calculation, not an unquoted theorem about completed tensor products.

Step 3 uses the power-series, tensor and direct-sum definitions. The exact relation subspace is proved in both directions using finite expansions: a multiple h f contributes finitely many scalar multiples of X-monomial multiples of f; conversely lambda f T^beta is itself in the extended ideal. It does not assume that every arbitrary infinite tuple of ideal elements is represented by finitely many ideal generators. There is no auxiliary comparison left unstated.

Step 4 uses tensor right exactness on the exact sequence that it displays, with base ring K and arbitrary K-module L. The cited statement includes both exactness and surjectivity after tensoring. The direct-sum definition justifies the finite componentwise quotient by explicitly checking when each component vanishes. This yields the actual coefficient map and inverse, not merely an unspecified vector-space isomorphism.

Step 5 uses only coefficient deletion from the power-series definition. It states both the smaller X cutoff and the disappearing boundary T components. The same image-of-I subspaces are reduced, so no assumed transition naturality is hidden.

Step 6 uses the power-series product formula and tensor bilinearity. It checks independence of representatives using I and the precise total-degree inequality. In particular, multiplying a beta coefficient error of X order at least N-|beta| by a gamma coefficient gives total degree at least N+|gamma|. No choice of representative can alter the retained coefficient. This is the stated coefficient-convolution product.

Step 7 uses the field-module-flat node exactly for L as a K-module. The cited flat tensor exactness statement gives the injection and the kernel after tensoring; tensor right exactness gives the quotient surjection. All the displayed terms are K-modules; the ordinary short exact sequence comes from successive ideal powers. The associated-graded definition identifies those powers and their quotients. I checked the case d=0 separately: C/a^0=0, so the boundary component that disappears is precisely L tensor (C/a). The map on the kernel is the inverse coefficient map already constructed, so there is no use of the proof of a cited node beyond its statement.

Step 8 uses only the definitions of direct sum, tensor, polynomials and associated graded. It supplies the inverse finite-support expansion and the degree reindexing explicitly. Every tensor has a finite expression in pure tensors, and every graded coefficient and polynomial has finite support; hence this argument makes no assertion that tensor commutes with an infinite product.

Step 9 uses the associated-graded ring structure theorem's homogeneous multiplication rule and unit, together with the polynomial and tensor definitions. The cited statement was read clause by clause, including the ring laws and scalar action. Multiplicativity is checked on homogeneous pure tensors and extended by finite addition; the scalar and unit maps and the beta=0 restriction are explicitly identified. This verifies that the comparison uses the specified j. The associated-graded structure input is Lean-closed, so it is permitted as a generic tool. The off-unit combined-ideal coefficient criterion is declared in split_report.tool_uses; it supplies a generic coefficient test, with no change of the unit route.

I checked the small cases directly. If e=0 then R=K, I=0, C=K and D=L[[T]], and the formula is the usual monomial basis of its finite truncation. If s=0 there is a single beta=0 component, giving precisely L tensor (C/a^N); step 3 still proves its relation subspace. For N=1 only the zero monomial survives, and I contained in (X) gives both sides L, with the degree-zero graded map the identity of L. For e=s=0 both assertions reduce to L. For I=0 the formula is the ordinary finite monomial decomposition. A nonhomogeneous example I=(X^2+X^3) in one variable gives the same finite relations as (X^2), since 1+X is a unit; the proof uses the truncated image U_m rather than incorrectly treating I as homogeneous. With I=(X^2) and N=3 the basis is 1,X,T,XT,T^2, matching the beta cutoffs 3,2,1. Characteristic and separability are unrestricted: only field flatness and finite monomial sums are used.

Every non-elementary imported fact is cited as a node; elementary steps contain their coefficient or finite-support argument. I checked C1 and C4 for all 23 citations against the open statements and copied their text verbatim into citations.json. No proof step exceeds 2000 characters (the longest is below 800); none hides a separate non-elementary lemma. The new-node form, unsupported-citation, duplicate, whole-clause relabelling, circularity and wrong-hypothesis failures of B--E were checked against the actual proof. All item metadata was retained, the statement was not weakened, and all writes were confined to this sandbox.

## Validation

The required deliver.py --no-push exited successfully on 2026-10-23: OK (not pushed), ac9902a3fda, preflight passed. Local JSON/dependency and all 23 verbatim-citation checks also passed. Maximum proof-step length: 768 characters. No compiler, Lean or Lake command was run. The final report is revalidated before direct push; the final delivery commit is printed by deliver.py.
