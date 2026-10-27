# Q44 — lem-sfb-symbol-cutoff-scaled-derivatives

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-symbol-cutoff-scaled-derivatives.json: existing statement, now split into four steps; no exact Mathlib match for the complete statement.
- citations.json: one verbatim statement quote for each of the three cited dependencies at its using step.
- searches.jsonl: actual search-tool output, retained without alteration.
- report.md: this report.

Zero new nodes; zero new Mathlib leaves. Three existing Mathlib leaves are reused.

## Attachments

None. Searching the upstream project for the exact blueprint id and the scaled-cutoff expressions found no declaration giving this statement. General cutoff matches concern homological truncations or weights; formal polynomial partial derivatives are different notions. No completed project proof was found.

## WANTED

WANTED: Demailly, Differential and pseudodifferential operators on manifolds, §3.7, printed pp.7–8, cutoff proof of asymptotic expansions, for lem-sfb-symbol-cutoff-scaled-derivatives. The inherited source.document is literature/demailly-hodge-ams.pdf, absent locally; the inherited parent identifies the separate pseudodiff.pdf lecture notes as the actual intended reference. A browser attempt at that URL failed to retrieve the PDF; an HTTP header request succeeding is not a reading of its contents. I did not download the missing document, claim to have read it, or rely on it. This complete proof is explicitly agent-written from the existing Mathlib leaves and definitions.

## Problems checked

The mathematical statement is unchanged and no STATEMENT-DISPUTED correction is needed. In particular, smoothness and the two constant-region conditions do not imply 0≤θ≤1 in the transition annulus; the proof uses a compact-set bound instead. The distinction between R^{-k} and (1+R)^{-k} costs 2^k; omitting that factor would not prove the stated estimate.

The inherited blueprint.from.node is null. The ancestor command returned None. I preserved this metadata and filled the proof-location explanation rather than inventing a blueprint id. I read the latest sk-thm-sf-ctf-stability unit and its direct-image proof: paragraph (3) has the proper/open factorization, not an analytic cutoff argument. The cutoff argument is an already present supporting expansion below that paragraph and its long recorded via chain. No chapter, unit route, target or statement is altered.

## Not duplicates

No new nodes were created. A proposed closed-ball compactness leaf was discarded after the whole-DAG search for isCompact_closedBall located lem-sfb-finite-dimensional-normed-proper. The general chain rule and compact bound already occur as lem-sfb-real-smooth-differentiation and lem-sfb-compact-continuous-norm-bound. The parent lem-sfb-symbol-dilated-cutoff-estimates and sibling lem-sfb-symbol-product-derivative-bound have different statements (symbol seminorm product estimate and Leibniz rule respectively), and are not used cyclically.

Whole-blueprint searches for derivative, cutoff, differentiation, closed ball, and closed Euclidean found no blueprint node stating this cutoff estimate. The broad bounded search returned many unrelated constructibility statements; none supplied this analytic statement. Whole-DAG statement searches additionally distinguished formal/algebraic derivatives and complex analytic derivative rules from the existing real smooth differentiation leaf used here.

## Review by Q44

I read the item, its parent cutoff estimate, the existing smooth-manifold and real-field definitions, the full statements of all three proof dependencies, and the latest blueprint unit and direct-image proof. I read delivery-errors B–E and checked the proof for both missing non-elementary inputs and citations claiming more than their statements. Sources available and read are the Mathlib signatures referenced by the existing leaves: real differentiation operations and composition, FiniteDimensional.proper/proper_real and the definition of ProperSpace, and IsCompact.exists_bound_of_continuousOn at its generated additive declaration. The original Demailly source is unavailable as detailed above. There are no new nodes needing an additional source review.

Step 1 cites lem-sfb-real-smooth-differentiation for smooth linear maps, compositions, smooth differentials, and the differential chain rule. Its statement explicitly gives each. Scalar evaluation on a fixed coordinate vector is linear and continuous, so iterating differential and evaluation shows that the coordinate partial functions are smooth. I wrote the induction for every ordered list of coordinate directions: the empty list is the base and applying the chain rule adds exactly one R^{-1}. Thus the proof uses no uncited higher chain formula or interchange of mixed derivatives, and does not turn a clause of the item into a new node.

Step 2 uses only the hypotheses and the local difference quotient. The strict inequalities |x|<R and |x|>2R give open neighborhoods on which the function is constant, and iterating the zero derivative on those neighborhoods proves vanishing of every positive-order derivative. The statement permits nonzero derivatives at the endpoints of the closed annulus, so no boundary assertion or hidden continuity extension is needed. At order zero the closed ball |x|≤R is handled directly by the stated cutoff values, including its boundary. This is an elementary step, with its argument written out.

Step 3 cites lem-sfb-finite-dimensional-normed-proper precisely for compactness of the closed radius-2 ball, after specialization to the usual real field and its Euclidean coordinate space. The field is nontrivially normed and locally compact, and the standard m coordinate vectors span the space; the node imposes no missing completeness hypothesis. It cites lem-sfb-compact-continuous-norm-bound precisely for a uniform norm bound on each continuous scalar-valued derivative on that compact set. The scalar target is R^1, allowed by the node; smoothness of each partial came from step 1. Finiteness of the set of indices is the elementary inclusion into {0,…,n}^m. Taking a finite maximum with 1 and using the constant/zero values outside the ball yields one global C_n depending only on the fixed data. I checked each cited quote directly in its node statement and included its verbatim statement in citations.json.

Step 4 uses no further theorem: R≥1 gives (1+R)/R≤2, so A_n=2^n C_n works simultaneously for k≤n and every R. I checked n=0, γ=0, R=1, m=1, points on |x|=R and |x|=2R, large R, and cutoffs with arbitrarily large transition-region overshoot. The proof handles all of them and makes no monotonicity, radiality, positivity, or upper-bound assumption on θ. Each step is shorter than 2000 characters; none conceals a comparison lemma or a source's omitted argument. The assembly is less than 3000 characters.

The full item was searched twice by mathematical meaning, as well as with Loogle, LeanSearch and source grep. Returned higher-calculus/bump/Schwartz declarations are useful infrastructure, but they do not state every clause for this arbitrary θ. For instance, θ itself equals 1 at infinity and is not compactly supported, so a compact-support derivative bound is not a one-line application to θ. The closed-ball searches prompted reuse of an existing leaf, not creation of a duplicate. All newly recorded searches are copied from the actual searches.jsonl entries; no invented query or unavailable-service result is called a negative search.

## Unfinished work

None in this stage-1 split. No Lean was written or compiled, no repository or launcher file was modified, and no agents were started. Delivery validation is performed by the required server-side dry run.
