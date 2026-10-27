# Stage-1 delivery: lem-sf-pod-smooth-dual-reduction-data

## Files written

- dag/nodes/sec-six-functors/lem-sf-pod-smooth-dual-reduction-data.json: statement, split into seven proof steps; no Mathlib match.
- citations.json: one exact verbatim statement quote for each of the 22 step/node citations.
- report.md: this worker review.
- searches.jsonl: actual search-command results, retained without alteration. write_split.py is sandbox-only drafting support.

There are zero new nodes and zero Mathlib leaves. The existing item statement, statement dependencies, source, creation record and blueprint ancestry remain unchanged. Only the split-owned proof, proof dependencies, proof origin, search records, status and split report were updated.

## Attachments

None. Searches of lean/WeilConjectures/ for the exact blueprint tag and for smooth dual reduction found no declaration stating the entire item. The coefficientDual and Orientation declarations provide partial derived-duality results on the small etale category, not all the site's coefficient-change, local-model, normalized-trace and compact-support clauses. They do not warrant ATTACH.

## WANTED

None. The argument follows the existing main-20261015 blueprint route and existing DAG theorem interfaces. Its expanded assembly is marked proof_origin.by = agent.

## Problems found and repairs

The item was unsplit and its original proof was empty. I retained its complete statement and wrote out the local reduced splittings, K-flat computation, typed finite-Tor reduction, perfect dual and twist, evaluation comparison, orientation comparison, trace equation and final compact-support naturality calculation. In particular, finite-free as a sheaf does not mean projective in the global sheaf category: the proof uses exactness of tensor with a retract of a finite sum of the coefficient unit, followed by the ringed-site K-flat theorem. No K-projectivity assertion is used.

The blueprint's finite-purity proof contains a fibrewise uniqueness discussion; I do not use its assertion that conservativity proves equality of derived morphisms. This split uses only the existing finite-reduction-of-purity node's stated orientation and trace compatibility, whose proof is maintained separately. No statement dispute or change of the unit route is needed for this item.

The statement's phrase “same ranks” is realized literally by the same finite-free splitting sizes N_j; no assertion that arbitrary projective summands have a chosen constant rank is inserted. The compact-support comparison is used on its stated finite-Tor domain, not on unrestricted unbounded complexes. The evaluation tensor objects belong to that domain by lem-sf-tensor-ctf.

## Unfinished work

None for the requested one-level split. The cited existing nodes remain independently owned. No Lean was written and no compiler, Lake or build command was run.

## Not duplicates

No new nodes. Whole-DAG and whole-blueprint searches for coefficient dual, finite reduction, bounded-above complexes and the relevant Stacks tags located the existing lem-pod-coefficient-dual-perfect, lem-fix-site-perfect-scalar-hom, lem-pc-bounded-above-flat-kflat-site and finite-purity comparisons. I cite those rather than introduce elementary, duplicated or clause-restatement nodes.

## Review by Q22

I read the item and its ancestor's first proof paragraph in literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/thm-pod-finite-reduction.proof.md, the six-functor chapter and sk-thm-sf-package unit records, and the main-20261015 unit text. The ancestor explicitly delegates site-perfect Hom/evaluation and compact support to lem-fix-operation-reduction, normalized trace and orientation to thm-pur-finite-reduction-of-purity, and the dual identification to thm-sf-dual-perfect. The seven steps follow this route. I opened every statement named in the steps, checked its actual hypotheses, and copied its full statement verbatim into citations.json. No statement is inferred from a cited node's proof alone.

Step 1 uses the definition of site-perfectness for bounded finite-projective local models and their splittings. I read Stacks sites-cohomology.tex Tag 06YS, label lemma-bounded-flat-K-flat, and Tag 06YY, label lemma-derived-base-change: the former is for arbitrary ringed sites and bounded-above flat complexes, the latter computes derived pullback on these models. These are precisely the hypotheses established by the explicit retract argument. The coefficient map is the identity on the underlying topos, with the constant-ring quotient. The ringed derived-monoidal comparisons statement gives pullback composition, which identifies restriction followed by coefficient change with coefficient change followed by restriction; I read Tag 0D6D, lemma-derived-pullback-composition, and Tag 07A4, lemma-pullback-tensor-product, as well. This is a generic tool, not a geometric purity argument. The splitting equation after tensoring is elementary and does not need a new node. I checked zero terms and zero splitting sizes: they remain zero; n=m gives the original splittings and model.

Step 2 uses exactly the typed reduction functor in thm-pur-finite-reduction-of-purity's statement, not merely the proof of its domain preservation. I checked that X and s are separated finite-type k-schemes, both quotient indices are positive and ordered, and ell is invertible. Its conclusion is D^b_ctf at the target coefficient ring. The two cited perfectness definitions identify the already constructed local models with the perfectness required below. It would be insufficient to cite lem-sf-reduction-flat-model alone for constructibility, since its statement only supplies the flat model and Tor bound; this split does not make that inference.

Step 3 uses lem-pod-coefficient-dual-perfect's explicit assertion of both perfectness and membership in D^b_ctf. I read its main-20261015 proof under sec-poincare-duality/sk-def-ops and the ringed-site perfect-dual computation in Stacks Tag 08JJ, lemma-dual-perfect-complex. The finite-level interpretation agrees with the direct-summand definition. The statement of prop-weil-twist-preserves gives both the locally constant rank-one line and preservation of D^b_ctf; I read its main-20261015 proof under sec-six-functors-basics/sk-prop-sf-existence. A common local refinement trivializes the line, so preservation of site-perfectness is a direct local-model calculation. Shifting translates the cohomological and Tor intervals in the cited finite-Tor definition. These facts are not hidden new lemmas. Zero K and d=0 satisfy these constructions, and arbitrary nonnegative d only changes the shift and invertible line.

Step 4 uses lem-fix-site-perfect-scalar-hom's actual statement with P=K_n and Q the unit. That statement explicitly allows a nonflat ring map and defines its isomorphism by the transpose of reduced evaluation; it therefore gives the desired evaluation square, not an arbitrary isomorphism. I read the main-20261015 lem-fix-operation-reduction proof under sec-six-functors-basics/sk-prop-sf-pf-reduction, including its bounded projective local Hom argument. The finite-tensor-presentation-reduction statement supplies the natural twist/shift comparison and its twist-reassociation compatibility. I also read the corresponding main-20261015 finite-reduction-of-purity proof in sk-lem-sp-reduction. The operation-reduction statement explicitly preserves evaluations and tensor associators. These are exactly the ingredients used to define v, lambda, h and b and to identify the reduced shifted evaluation. No arbitrary ordinary-global-sections comparison or its invertibility is used.

Step 5 uses thm-sf-dual-perfect's stated finite-reduction and canonical-evaluation compatibilities, after steps 1-3 establish its perfect and finite-Tor hypotheses. I read the main-20261015 thm-sf-dual-perfect proof. Its isomorphism is the specified normalized orientation followed by Hom twist interchange, agreeing with the definitions in the item. The finite-purity node's statement supplies compatibility of that orientation with reduction. I did not introduce a different orientation or invoke SGA.

Step 6 uses lem-fix-operation-reduction's finite-Tor compact-support isomorphism, which is natural and preserves the relevant adjunction maps. The actual definition of def-pur-smooth-trace is the counit after the smooth purity map. The finite-purity theorem explicitly states compatibility of those smooth traces, so this citation says exactly what is needed. I checked f=a_X is smooth separated, of pure relative dimension d, and both finite-stage admissibility assumptions are available. Writing the intermediate R Gamma_c(h) explicitly prevents an ill-typed equation: the displayed equation of the item is read under the same orientation-unit identification.

Step 7 first uses lem-sf-tensor-ctf to put B_i=K_i tensor^L L_i in the finite-Tor constructible domain. I read its main-20261015 proof under sec-six-functors-basics/sk-prop-sf-biduality-general. The operation-reduction naturality assertion then applies to e_n. The four displayed equalities substitute the trace equation of step 6 and evaluation equation of step 4 into that naturality square, with every source and target specified. The remaining argument is composition and functoriality, so elementary=true is appropriate even though the two existing domain/naturality facts are cited. This is the substantive final calculation rather than the phrase “the squares commute”.

I checked delivery-errors B through E against these files: there are no new-node form, hollow statement, duplication or Mathlib-leaf issues; all non-elementary inputs are existing cited statements, the union of their uses is proof_deps, no citation reaches this item back, and no step moves the whole item into a fresh lemma. Every step is shorter than 2000 characters. Generic off-unit tools are declared in split_report.tool_uses; their role is K-flatness, restriction/composition, tensor closure, dual preservation or invertible twisting, not replacement of the unit's geometric route. A server review_split check passed with zero new nodes.

I read every actual current msearch result and retained the item's earlier recorded searches. Current LeanFinder, Loogle, grep and LeanSearch commands are preserved in searches.jsonl and appended with exactly their tool and query text. The second phrasing returned LightCondensed internal Hom and sheaf free-pullback facts; the first returned generic sheaf cohomology and derived-localization facts. LeanSearch returned ordinary module dual base change and linear trace base change. I read Mathlib/LinearAlgebra/Dual/BaseChange.lean around its toDualBaseChange and Mathlib/LinearAlgebra/Trace.lean at trace_baseChange: these are ordinary modules (the displayed equivalence uses finite free modules), not the derived sheaf smooth trace or full conjunction of this item. They are not an exact match or a one-line specialization. The earlier unavailable service record remains unavailable rather than being recast as no match.
