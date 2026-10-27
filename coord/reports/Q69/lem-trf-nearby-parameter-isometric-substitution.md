# Stage-1 delivery: lem-trf-nearby-parameter-isometric-substitution

## Files written

- dag/nodes/sec-trace-formula/lem-trf-nearby-parameter-isometric-substitution.json: item, split into seven steps; statement unchanged; existing searches retained.
- dag/nodes/sec-trace-formula/lem-trf-closure-isometric-field-extension.json: statement, unsplit; no exact Mathlib match for the concrete-closure formulation. Abstract completion maps are candidates, not the concrete-closure identification.
- citations.json: the verbatim statements used in steps 2 and 6.

One new node, zero new Mathlib leaves. The existing leaf lem-weil-alg-closed-linear-factorization is reused.

## Attachments

None. Searched lean/WeilConjectures for the blueprint tag, nearby parameters, isometric substitution, Temkin, and isometries. The hits concern p-adic exponential/logarithm and coefficient inclusions, not this statement. No project declaration states every clause.

## Wanted literature

WANTED: Michael Temkin, Stable modification of relative curves, arXiv:0707.3953v3, Lemma 6.3.2, printed page 48, for lem-trf-nearby-parameter-isometric-substitution. The named file literature/temkin-stable-modification-arXiv-0707.3953v3.pdf is absent from this clone. I did not write to literature or download a file. I read the author-hosted PDF online at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf (printed page 48) and compared the argument with it. The proof remains marked agent-written: the local source is absent, and the explicit non-strict bound and concrete-closure assembly are supplied here.

## What needed repair

The input was statement-only. Its statement is correct; no STATEMENT-DISPUTED correction is needed. Temkin states a strict relative bound for nonzero elements; the item's closed bound follows from the explicit product and quotient estimates written here. The zero case is separately included. No strict bound is inferred by taking limits of strict inequalities.

The current blueprint latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md has a different high-level locality argument from the inherited old analytic-support trail. I preserved the item's existing statement and ancestry, and realized the already-assigned analytic supporting input; no chapter or unit route was rewritten. The current blueprint does not itself state the nearby-parameter or concrete-closure lemma. The unit's realization fields are not this supporting item's responsibility.

## Searches and Not duplicates

Whole-DAG statement/title searches were made for isometry, isometric extension, closures and completions, polynomial linear factorization, and ultrametric facts. Blueprint searches used `isometric`, `isometry`, `completion`, and `factorization`, and the ancestor command gives lem-trf-local-term-locality. The factorization search found lem-weil-alg-closed-linear-factorization, which was read and reused. None states the new concrete-closure extension theorem.

All eight new Mathlib searches in searches.jsonl were run through the required msearch command; their exact tool and query texts, results, and verdicts are recorded on the new node. I read the hits and the Mathlib source, specifically Topology/MetricSpace/Completion.lean lines 193–214 and Topology/Algebra/UniformRing.lean lines 181–188. Isometry.extensionHom extends to an abstract completion and Isometry.completion_extension preserves distances there; mapRingEquiv compares abstract completions. The identification of those objects with the actual closures inside H is additional content, so I did not label the concrete-closure theorem a one-line Mathlib specialization. The second natural-language wording specifically asks for field isomorphisms between concrete closures. All search services answered; none was falsely recorded unavailable or as absent from an unconsulted index.

## Not duplicates

- lem-trf-closure-isometric-field-extension vs lem-sfb-normed-field-completion: the existing node provides a completion and its canonical embedding; it does not extend a specified isomorphism between two arbitrary subfields to their concrete closures.
- lem-trf-closure-isometric-field-extension vs lem-sfb-metric-completion-isometry: the existing node proves that the canonical map of a Q_l-vector space into its completion preserves distance; it neither constructs an extended field isomorphism nor identifies two concrete closures.
- lem-trf-closure-isometric-field-extension vs lem-trf-nearby-parameter-isometric-substitution: the new node assumes an isometric isomorphism already exists, with arbitrary subfields and arbitrary real absolute values; it has no parameter substitution or relative perturbation estimate. Steps 1–5 and 7 of the item supply those substantive arguments.
- lem-trf-closure-isometric-field-extension vs lem-trf-analytic-close-embedding-degree: the latter assumes complete fields and two close embeddings and compares finite degrees, whereas the new node supplies extension across closures and has no finiteness or closeness assertion.

No Stacks tag supplies the analytic extension result; no tag was assigned artificially. There are no new nodes with a Stacks tag shared with an existing node. The source of the support node names the exact Mathlib declarations and the additional concrete identification, rather than claiming a nonexistent Stacks citation.

## Argument retained for the new unsplit node

For future splitting of lem-trf-closure-isometric-field-extension, the intended argument is as follows; its JSON deliberately has a statement only. For x in the closure of F, choose x_n in F converging to x. The isometry makes f(x_n) Cauchy, so completeness of H gives its limit in the closure of G. If y_n is another such sequence then |f(x_n)-f(y_n)|=|x_n-y_n| tends to zero, so the limit is independent of the sequence. The extended map preserves distances by the ordinary triangle inequalities for limits, and addition and multiplication by their limit formulas. Closures are closed under addition and multiplication by those same formulas. For nonzero x, the approximating x_n are eventually nonzero with |x_n| bounded below by |x|/2; the identity x_n^{-1}-x^{-1}=(x-x_n)/(x_n x) proves convergence of inverses and hence closure under inverses. Apply the construction to f inverse: composing on approximating sequences proves both composites are the identity. Distance preservation proves continuity and uniqueness by density. These constructions are exactly the extra concrete-range content beyond the abstract-completion Mathlib hits. No perturbation estimate is moved into this node.

## Review by Q69

I checked the statement against Temkin's author-hosted Lemma 6.3.2, printed p. 48. Its proof starts with linear factors, passes to products and quotients, and concludes by continuity. Here k is algebraically closed, so all roots used for factorization belong to k and there is no extension-of-absolute-value hypothesis to supply. The factorization node's entire statement was read: it applies to any nonzero polynomial over an algebraically closed field and explicitly allows degree zero. Its Mathlib source Splits.eq_prod_roots at Algebra/Polynomial/Splits.lean line 299 agrees. I also read def-weil-field and the chapter and unit records, the current latest blueprint ancestor, and the Mathlib completion sources cited above.

Step 1 uses only the given positive infimum, c<1, and the ultrametric inequality. It proves rather than assumes the equal-norm consequence of strict domination. This shows v is outside k even when the original closeness inequality is equality.

Step 2 cites lem-weil-alg-closed-linear-factorization. Its quoted statement supplies exactly the coefficient and linear factors used. The hypothesis k algebraically closed is present; P is explicitly nonzero. Since u and v are outside k, no factor can vanish. This also proves the injectivity of polynomial evaluation needed later, without assuming a transcendence theorem as an unlisted dependency.

Step 3 uses those already constructed factors and writes the full finite-product induction. The empty product starts at 1 with zero error. There is no new polynomial perturbation node duplicating a clause of the item. The displayed ultrametric recurrence is elementary and has no unlisted analytic input.

Step 4 checks the field-of-fractions construction directly: all denominators are nonzero by step 2, and equality of fractions becomes a polynomial identity by injectivity at u. Evaluation at v respects that identity. The inverse is the same construction with the parameters reversed; no claim that the error hypothesis must be re-proved for that inverse is needed.

Step 5 writes the quotient error with A and B, checks both norms equal 1, and bounds A-B via their errors from 1. This is where a casual appeal to rational substitution could have hidden a missing argument; the calculation is included. Zero is checked separately, and the distance equality follows from additivity.

Step 6 cites the new closure-extension statement, whose entire statement was read against its use. The ambient H is complete, F and G are actual subfields of H, and step 5 supplies precisely its isometric-isomorphism hypothesis. The conclusion supplies a surjective field isomorphism between exactly the concrete closures named in the item. Restriction to k and the image of u follow from extension of f, not from uniqueness of an unspecified embedding. The support statement also applies to equal subfields, an identity map, the case of already closed subfields, and trivial absolute values; completeness and separation suffice, and no nonarchimedean assumption is illicitly needed there.

Step 7 is an explicit density argument, not a hidden continuity comparison. For b nonzero the positive radius min(|b|,c|b|) is available because c>0. The chosen rational element has the same norm as b by step 1, and the extension's distance equality bounds both approximation errors by the same radius. The three-term maximum proves the non-strict bound exactly, including equality at cr; b=0 again gives zero. Thus every non-elementary input is a node citation (steps 2 and 6), and citations.json quotes those statements verbatim. No step is longer than 2000 characters; the longest is 571 characters. Elementary steps are explicit algebraic or metric calculations, not relabelled copies of the item.

Small cases checked: u=v gives the identity substitution with zero error; nonzero constant polynomials and the empty product satisfy the induction base; the zero numerator gives b=0; nonzero denominators never vanish; repeated roots do not change the finite-product proof; equality |u-v|=cr is allowed because cr<r and c<1; the density radius remains strictly positive for every nonzero b. No source or statement correction was needed. No SGA source, Lean edit, compiler, or library build was used.

## Unfinished work

None for this one-level stage-1 split. The one new statement-only support node is intentionally left unsplit for a later item. Server-side check_dag and review_split passed before the final delivery dry run.
