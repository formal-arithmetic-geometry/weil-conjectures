# Stage-1 report: lem-trf-formal-jacobian-generator-minor-expansion

## Files written

- dag/nodes/sec-trace-formula/lem-trf-formal-jacobian-generator-minor-expansion.json: statement, split; no exact Mathlib match. Preserved the statement, all original citations/searches and provenance, and added a four-step proof and six fresh logged searches.
- citations.json: six entries, one per cited node per proof step, with verbatim statements copied from the current repository.
- report.md: this report and Q72's direct-delivery review.
- searches.jsonl: actual search-command output log, created by msearch.py.

New nodes: 0. New Mathlib leaves: 0. Existing nodes reused: the formal derivative and derivation definitions, matrix/submatrix/determinant definitions, and lem-weil-pbc-cauchy-binet.

## Attachments

None for this item. Searching WeilConjectures by its exact blueprint id and quotient-Jacobian/generator/minor vocabulary found no declaration proving the item. Matrix.cauchy_binet (WeilConjectures/LinearAlgebra/Matrix/CauchyBinet.lean:44) belongs to the already attached lem-weil-pbc-cauchy-binet; its statement was read, and the node records closed Lean with no open dependencies. It proves the generic matrix formula, not this formal-derivative item.

## WANTED

None. Both sources needed are in literature/stacks-project/.

## Corrections and provenance

The item was an unsplit statement, with no proof in the initially empty sandbox. Its statement is correct and is unchanged. No STATEMENT-DISPUTED issue arose. Neither finite list is required to generate I: only membership of each f_b in I is used. There is no differentiation on the quotient; all differentiation happens in T before applying the quotient map.

The current blueprint was read under literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/: lem-trf-local-term-locality.md and its proof, as well as the chapter/unit records. The inherited blueprint ancestor now discusses contracting correspondences, not a generator-change calculation. The item's from.place names the actual generator-change paragraph in Stacks 0C4B within its inherited chain of auxiliary geometric reductions. The split_report states this provenance explicitly rather than attributing that paragraph to the latest ancestor's proof. No unit/chapter record or route was edited.

The generic off-unit tool lem-weil-pbc-cauchy-binet is already Lean-closed. It is used solely for its displayed determinant formula over the quotient commutative ring, on two explicitly defined rectangular factors. The use is also recorded in split_report.tool_uses. No other unit's geometric route is substituted.

## Unfinished work

None in the authorized stage-1 split. No Lean was written, and no compiler, Lake or build command was run. Only the sandbox was written. The required server dry run and delivery are invoked after this report is written.

## Not duplicates

No new nodes. Whole-DAG searches for Tags 0C4B/0F0K and generator/minor/derivative vocabulary, and blueprint_refs searches for Jacobian, Cauchy and linear combinations, were read. The existing derivative definition already calls the operation a derivation and states its Leibniz law. The existing Cauchy-Binet node states exactly the general rectangular product identity needed. Thus creating either a derivative-product lemma or a selected-minor lemma would add an unnecessary node. The sibling coordinate-minor expansion is about change of coordinates, not change of a list; the parent minor-invariance node proves equality of generated ideals and depends on this item, so cannot be used here. The minor-inclusion node states an ideal containment, not the coefficient-by-coefficient selected-minor formula.

## Review by Q72

I read Curves Tag 0C4B, label lemma-fitting-ideal-well-defined, in curves.tex:4065-4098, including the displayed derivative-error matrix and the sentence that its final term vanishes in A/I. I also read Algebra Tag 0F0K, label item-cauchy-binet, in algebra.tex:282-288 and verified both tags against tags/tags. The source's generator hypothesis is not needed for the displayed calculation: taking arbitrary f_b in I suffices. There are no new nodes needing separate sources.

For step 1 I opened def-trf-formal-power-series-partial-derivative and def-weil-pbc-kahler-differentials. The first states that the coefficientwise partial derivative is an F-derivation; the second explicitly defines derivations as additive maps satisfying the product rule. This supplies precisely the two laws used, so the step writes out their finite-sum application instead of citing a definition for an unstated theorem. I checked MvPowerSeries.pderiv at Derivative.lean:118-124, which really packages additivity and the Leibniz rule, and its coefficient formula at 130-132. The finite sums involve no convergence or interchange of infinite sums. Step 1 is elementary from these definitions.

For step 2 I opened def-weil-matrix, whose statement defines a matrix entrywise. The proof writes the product's finite-sum entry explicitly and applies the quotient homomorphism to step 1. Every error summand has a factor f_b, whose residue is zero by the given membership f_b in I. Multiplicativity and additivity of the quotient map then give exactly the claimed matrix entry. No assumption that I is proper, invariant under differentiation, or generated by f or g is introduced. This is elementary quotient-ring arithmetic.

For step 3 I opened def-weil-submatrix and the entire statement of lem-weil-pbc-cauchy-binet. The former selects exactly the stipulated rows and columns. The latter assumes only a commutative ring, factors of dimensions m by n and n by m, and an increasing ordering for each common subset. Here R=T/I is commutative, m=r, n=s, U has dimensions r by s, and V has dimensions s by r. I verified the entry identities UV=J_x(g)_{A,B}, U^S=overline C_{A,S}, and V_S=J_x(f)_{S,B} directly from the increasing enumerations. Thus the cited statement supplies the precise determinant sum with no transposes, sign, factorial, missing ordering, or assumption about a field quotient. The step is marked non-elementary because it invokes that theorem.

For step 4 I opened def-weil-pbc-matrix-determinant; its statement explicitly makes the zero-size determinant 1. There is one zero-element subset and no r-element subset of an s-element set when s<r. Substitution into the identity already proved gives both edge cases. I checked s=0 (g is the zero list of combinations), l=0 and n=0 (only r=0 can have both selected sets), and r exceeding l or n (no selected sets, so the assertion is vacuous). I checked I=T as well: the zero ring is allowed by Cauchy-Binet, and the unit/zero equalities remain valid. In positive characteristic the derivative is still a derivation; the argument divides by no integer. This step uses only the determinant definition and finite-set counting.

Against delivery-errors B-E: the existing statement introduces its objects and defines its quotient Jacobian inline; every cited non-elementary assertion is in the cited node's statement. All six quote entries were generated from those statements verbatim. There is no new statement-only node, hidden theorem transferred to another node, proof sketch masquerading as a statement, uncited chain rule, hypothesis strengthening, or dependency on the parent. The only substantive tool is the already existing Cauchy-Binet theorem. All four steps are under 2000 characters (525, 505, 731, 387), so no long step conceals a further lemma.

I ran leanfinder in two distinct phrasings, loogle with MvPowerSeries.pderiv and Matrix.det, leansearch in words, and two grep queries through the prescribed msearch.py command. All services returned successfully. The hits about PreSubmersivePresentation are polynomial-presentation Jacobians, not arbitrary formal series or every quotient minor; I read the relevant declarations in Submersive.lean:131-158,367-376 and Core.lean:265-267,299-306. The derivative grep hits supply the already existing derivative definition, not the whole item. All exact tool/query pairs and raw command-log results were appended to mathlib_searches, while original search records were retained.
