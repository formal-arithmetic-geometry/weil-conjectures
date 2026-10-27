# Stage-1 report: lem-per-affinoid-jacobian-certificate-regular

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-affinoid-jacobian-certificate-regular.json: statement, split; the statement and statement dependencies are unchanged. Seven proof steps, all using existing nodes. Existing searches and provenance retained; Q149 searches appended.
- citations.json: one entry for every step/node citation, copying the cited statement verbatim.
- report.md: this report and the author's review.

New nodes: 0. New Mathlib leaves: 0. No Lean files or compilation. There was no earlier node copy or completed report in this sandbox, and no released repair note was found in the read repository.

## Attachments

None. Searched lean/WeilConjectures both for the exact blueprint tag and for affinoid, TateAlgebra, and Jacobian/regularity language. The polynomial regular-maximal-Jacobian presentation declaration is not a declaration about analytic restricted-series quotients. It does not attach this item. Existing sorry declarations were not counted as proofs.

## WANTED

WANTED: archival copy of Michael Temkin, Desingularization of quasi-excellent schemes in characteristic zero, arXiv:math/0703678v2, Proposition 3.3.2 and proof, printed pp.20--21, for lem-per-affinoid-jacobian-certificate-regular. Read the author's PDF online at https://math.huji.ac.il/~temkin/papers/Excellent_Desingularization.pdf on 2026-10-24; no downloaded file was written to the repository. The proof is explicitly an agent reconstruction, since the arbitrary real-valued complete-field generality is established here using the existing polynomial/Tate completed-local-ring comparison, rather than invoked as a verbatim special case of the discretely valued formal-model proposition.

## Problems found and changes

The node had no proof. Its mathematical statement is true, including over imperfect fields and in positive characteristic. No statement correction was needed. Temkin defines the radical of the sum of colon-times-minor ideals; the item uses the sum itself. Their being the unit ideal is equivalent: if 1 is in the radical then a power of 1 is in the sum. Thus this convention does not change the hypothesis. Temkin's ambient setup is discretely valued; I have not asserted that the entire formal-model proposition covers arbitrary real-valued fields. Instead Steps 1 and 3 use the existing comparison node, whose statement explicitly permits the arbitrary real-valued complete fields required here.

The initially tempting local-chart node lem-per-perfect-affinoid-local-jacobian-chart goes in the opposite direction and assumes a perfect field. It is not cited. The item is proved by finding independent equations in the cotangent space of the ambient Tate local ring, without asserting injectivity of that entire cotangent space into continuous differentials. That stronger assertion fails at inseparable closed points and is unnecessary.

The latest blueprint ancestor proof was read at literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.proof.md. Its Step 3 is duality and has no formal-algebraization paragraph. The inherited branch and its via list are retained and described honestly in split_report.blueprint. No unit or chapter statement, realized field, target, or route has been changed.

## Existing-node and Mathlib searches

Read the sandbox searches.jsonl and the recorded hits before reusing them. Ran msearch.py for this item with LeanFinder, Loogle, grep and LeanSearch. The first two unquoted Loogle requests were rejected for unknown identifiers and are recorded as such, not treated as successful evidence of absence. A corrected quoted query, `"jacobian", "IsRegularLocalRing"`, returned no hits. The second semantic phrasing sought independent continuous derivatives at a restricted-series closed point. Polynomial SubmersivePresentation and IsStandardSmooth hits do not concern the Tate algebra. Read Mathlib/RingTheory/Smooth/StandardSmooth.lean, especially the definition at line 63 and the presentation theorem at line 69. PowerSeries Noetherian results concern unrestricted formal power series, not the restricted algebra. The generic quotient Noetherian result only supplies an elementary consequence once the ambient Tate algebra is known Noetherian. There is no match for the item.

Searched the whole DAG by parsed statements for Tate algebra, affinoid, restricted series, Noetherianity, cotangent independence, regular local quotient and completion; read the neighbouring affinoid nodes and the statements of every cited node. Ran blueprint_refs.py ancestor and whole-blueprint searches for affinoid, Jacobian, restricted series, continuous Jacobian, and Jacobian certificate regular affinoid. The analytic prerequisites are already supplied by lem-trf-affinoid-polynomial-closed-point-comparison at J=0; the local-algebra results are existing nodes. Consequently no new node is justified or created.

## Not duplicates

No new nodes. The existing comparison, completion, hypersurface, localization, determinant and ideal-existence nodes are reused. The perfect-affinoid local-chart and geometric-affinoid Jacobian-unit nodes are converses with additional hypotheses, not this item.

## Review by Q149

This is the author's self-review required by the direct-delivery brief. I read sections B--E of coord/delivery-errors.md, the current item and its citer, the unit and chapter, the latest ancestor proof, Temkin Proposition 3.3.2 including its preceding ideal formula and the converse on printed p.21, and Stacks algebra.tex at lemma-Noetherian-permanence (00FN), lemma-regular-ring-CM (00NQ), and lemma-localization-of-regular-local-is-regular (0AFS), and more-algebra.tex at lemma-completion-regular (07NY). I compared the proof with the full statement of every cited node; citations.json contains those actual statements, not quotations bent to fit a desired use.

Step 1 uses lem-trf-affinoid-polynomial-closed-point-comparison only at polynomial J=0. Its statement supplies Noetherianity of exactly the Tate algebra T. It does not claim that arbitrary analytic equations come from polynomial equations, and I never use it that way. The quotient Noetherian assertion is proved directly by taking inverse images of ideals and their finite generators, using the actual definition def-weil-pbc-noetherian-ring. The zero quotient is regular by the all-primes definition def-weil-regular-scheme, since it has no primes.

Step 2 uses def-weil-pbc-localization-at-prime for the fractions and local maximal ideal, which its statement explicitly gives. Because H is the sum of the image-colon ideals times minors, H=B forces a generator aD outside the chosen maximal ideal. Both a and D are outside its inverse image in T. Inverting a then proves IR=I_ER directly from aI subset I_E. This is an elementary consequence of the certificate; no colon base-change theorem or prior reducedness is hidden.

Step 3 checks the complete, nontrivial, real-valued nonarchimedean hypothesis of the comparison node, with n=r and J=0. That node supplies maximality of the contracted polynomial prime and the induced completed-local-ring isomorphism. The polynomial regular-ring node supplies regularity of P_p at every prime, and the completion-regular-local node supplies both directions of regularity under maximal-ideal completion. Its Noetherian-local hypothesis for T_n is checked using the existing localization-Noetherian node and Step 1. The regular-local ring-isomorphism node really states invariance for arbitrary ring isomorphisms, so it applies to the completions. These results establish ambient regularity independently of any property of B.

Step 4 is an elementary calculation of derivations on fractions, written explicitly. Integer norms are at most one, so termwise derivatives of restricted series remain restricted in every characteristic. Coefficientwise finite Cauchy sums prove Leibniz. Differentiating a denominator-cleared equality proves the localization formula is well defined. Reduction kills products of two maximal-ideal elements, and its product rule gives residue-field linearity on q/q^2. This is a routine formula check, not an unstated analytic smoothness theorem. The residue identification is written with its inverse, not presumed to be separable over F.

Step 5 cites the determinant definition for commuting reduction with its finite sum and the matrix-adjugate-identity node for adj(M) M=det(M) id. It derives linear independence by applying the localized derivatives, selecting precisely the U rows, and cancelling the nonzero scalar determinant in the residue field. It does not use a general assertion that continuous differentials detect all tangent vectors. Empty matrices give the empty independent family.

Step 6 carries out an explicit induction on the chosen number c of equations, starting with the regular ambient ring. In each quotient, membership in the square of its maximal ideal lifts to q^2 plus the previous equations. Reducing coefficients would contradict Step 5. Thus the cited hypersurface criterion applies with its exact hypotheses: the preceding quotient is regular local and the next equation is in the maximal ideal but outside its square. The localization-at-prime-of-quotient node states exactly R/IR isomorphic to B_m with its fraction formula; ring-isomorphism invariance gives regularity of B_m. This uses the statement of the hypersurface node, not the proof of a converse quotient-parameters node. No new lemma merely restates the item's conclusion.

Step 7 obtains a containing maximal ideal using the proper-ideal-contained-in-maximal node, which applies to any proper ideal, hence to the given prime. The primality criterion for its extension to B_m is written using fractions. The regular-local-localization node applies to that prime in the regular local ring B_m. The localization-of-localization node explicitly gives the intermediate localization at the images of B minus the prime, and the displayed fraction formula identifies it with the prime localization. The isomorphism node transfers regularity. Together with Step 1 this is exactly the definition of a regular Noetherian ring, not merely regularity at its maximal ideals.

For the off-unit generic tools, split_report.tool_uses declares the polynomial/Tate comparison, completion regularity, hypersurface regularity and regular-local localization. They are analytic or commutative-algebra inputs, not alternative perverse-sheaf proofs. Other off-unit statements are Mathlib leaves and definitions. No same-unit result supplies these generic inputs. No new node, duplicate, unsupported Stacks assertion, clause transfer, or source-route substitution was introduced. All seven steps have fewer than 2000 characters; the longest is Step 7 at 1131 characters.

Small cases: B=0 is discharged before choosing a maximal ideal; s=0 gives the empty equations and T itself; r=0 leaves a quotient of the field and the empty determinant. An inseparable equation x^p-a has derivative zero and cannot supply the needed nonzero minor at a maximal ideal; no false perfectness inference enters. The singular quotient F<x>/(x^2) has no unit certificate, including in characteristic two. The equation x has derivative one and yields the field quotient as expected. A redundant equation x^2 alongside x is harmless because the colon element for E={x} is 1. When the selected E is empty, the invertible colon element kills I locally, and the proof correctly takes no hypersurface step. No equidimensionality, reducedness, field perfection, or valuation discreteness was introduced.

Corrections during self-review: I discarded the unnecessary search for a new Tate-regularity node upon finding the existing completed-local-ring comparison; I replaced any proposed analytic Jacobian black box with explicit cotangent independence and hypersurface induction; I recorded malformed early Loogle queries accurately and added a valid quoted query. The item statement remains unchanged.

## Unfinished work

None in this stage-1 split. Existing unsplit dependencies remain existing DAG work. The maintainer's independent mathematical review remains the delivery protocol's next step.
