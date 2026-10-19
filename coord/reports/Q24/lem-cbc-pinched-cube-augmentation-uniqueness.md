# Q24 — lem-cbc-pinched-cube-augmentation-uniqueness

## Files written

- dag/nodes/sec-smooth-purity/lem-cbc-pinched-cube-augmentation-uniqueness.json — statement split into three elementary steps; no full Mathlib match.
- citations.json — verbatim excerpts for both cited nodes in every step.
- report.md — this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches in /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact blueprint tag, pinched/PinchedCube/maximumMap/pinched_cube and cosimplicial found no declaration of this result. The unrelated Cech and Amitsur cosimplicial declarations do not concern this quotient. The item's current repository record has no Lean audit or Lean declaration to attach. No upstream-master sorry is treated as a proof.

## Wanted literature

WANTED: a local archive of Lurie, Higher Topos Theory, Section 2.2.2 (printed p.76) and Proposition 3.2.1.14 (printed p.177), for lem-cbc-pinched-cube-augmentation-uniqueness. I read those places online in the official Harvard PDF, https://people.math.harvard.edu/~lurie/papers/HTT.pdf (PDF pages 93 and 194). No literature was downloaded or changed. The proof is agent-written: these places give the construction and normalization context, not this standalone uniqueness assertion. No Stacks tag states this specialized pinched-cube lemma; none is invented. No SGA source is used.

## Audit findings and changes

The statement is true and is kept verbatim. Its original source pointer to Proposition 3.2.1.14 gives the marked comparison context; the actual quotient and maximum augmentation are described in Section 2.2.2. This distinction is explicit in proof_origin and the proof-step sources. No mathematical dispute, coefficient-category identification or target change occurs.

The pre-existing quotient theorem lem-coef-pinched-cube-latching already states all input about Q, so the proof needs no new nodes. Creating a separate vertex-normalization or standard-simplex-extensionality node would only package a few lines from definitions. Mathlib's SSet.stdSimplex.ext is exactly function extensionality for a single simplex; it is insufficient by itself to prove cosimplicial uniqueness. I read StdSimplex.lean's objEquiv, FunLike and ext declarations after the searches. The rejected unqualified Loogle query is recorded as rejected, not as evidence of absence; the corrected query returned ext and ext_iff.

DAG keyword searches for pinched, maximum-of-subsets, cosimplicial maps and simplex determination, and blueprint_refs searches for pinched cube augmentation uniqueness and maximum-of-subsets found no duplicate of the item. The existing quotient node is reused rather than restated. The blueprint ancestor thm-cbc-finite-level-proetale and the inherited via chain are retained; I read its current main-20261015 statement and proof. This item serves the extracted point-normalization step of the relative-nerve comparison, now its Step 8. It is not the unit's key statement, so no unit record is edited. Its off-unit generic quotient tool is declared in split_report.tool_uses.

## Not duplicates

No new nodes were created; there are no new/existing pairs to compare.

## Review by Q24

I read delivery-errors B through E in full and checked the item against them. I read the complete statements of def-cbc-enhanced-diagrams-cones and lem-coef-pinched-cube-latching, and the latter's quotient-normal-form and direct-image argument. For the source, I checked the explicit quotient and augmentation in HTT Section 2.2.2 and the use of the point comparison in Proposition 3.2.1.14. No new-node source is needed because there are no new nodes.

Step 1 uses the quotient theorem's actual statement, not its proof: at a vertex I, the relation at k=max I identifies it with the singleton k because both tails above k are empty. The nerve definition makes vertices precisely nonempty subsets, and taking the quotient introduces no additional elements. For n=0 the poset has one object and one simplex in every degree. These are direct calculations, not a hidden normal-form theorem.

Step 2 uses exactly the quoted direct-image compatibility, and the standard simplex definition from def-cbc. The map [0] to [n] with value k is weakly increasing for every k, so it is among the naturality maps assumed in the item. Its image of the singleton 0 is the singleton k. The only possible value of b_0 on its only vertex is 0. Consequently naturality fixes every singleton and Step 1 fixes every vertex. No stronger naturality or injectivity of the quotient is assumed.

Step 3 uses the quotient and nerve definitions to choose a chain representative in every simplicial degree, including chains with repeated subsets, and uses the stated descended nerve-of-maximum map to compute mu on that same chain. A simplicial map commutes with restriction along [0] to [r], so the j-th target vertex is the already computed max I_j. The standard simplex statement explicitly defines its r-simplices to be functions [r] to [n]; equality at all j is thus equality of functions, proving b_n=mu_n in every degree. This is why no general nerve fully-faithfulness theorem, density lemma or non-elementary extensionality theorem is needed. All citations in all three steps have literal statement excerpts in citations.json, and proof_deps is exactly their union.

I checked the small cases n=0 and r=0, the two vertices and the chain {0} subset {0,1} when n=1, and chains with repeated terms. In the latter cases the maxima repeat exactly when the target simplex is degenerate; the argument never assumes nondegeneracy. For a relation at i, i is present throughout, so maxima are preserved; under any weakly increasing theta, max(theta(I))=theta(max(I)), including constant theta. Thus the described mu is indeed cosimplicial as stipulated. Every chain is nonempty in each entry, so max is always defined. Empty domains and undefined maxima never enter the argument.

All steps are shorter than 2000 characters and each is an elementary definition/naturality calculation. Every non-elementary construction used is already in the cited quotient theorem. The proof is not a relabelling of the conclusion, there is no new recursive dependency, no inline independent comparison lemma, no unproved standard claim and no added hypothesis. The statement dependencies are exactly the two nodes whose notions it uses. Only the named sandbox files were written; no Lean, compiler, Lake, shared-project or launcher changes were made.

## Unfinished work

None in the requested one-level split. The missing local HTT archive is noted above; the standalone uniqueness proof is fully written as agent work.
