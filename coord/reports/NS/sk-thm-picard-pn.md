# NS — sk-thm-picard-pn

## Files written

- `dag/nodes/sec-picard-framework/sk-thm-picard-pn.json`: split the item into seven steps. Mathlib verdict: no match after two semantic phrasings, two Loogle queries, two source patterns, and LeanSearch.
- `dag/units/sk-thm-picard-pn.json`: only `realized` and `realized_by` changed. The existing statement and sole proof paragraph are untouched.
- `citations.json`: ten entries, one for every step/cited-node pair, using verbatim statement text.
- No new nodes; no Mathlib leaves.

## Attachments

None claimed. Read `WeilConjectures/AlgebraicGeometry/Cohomology/ProjectiveSpaceOverField.lean` (especially the declarations at lines 107 and 121) and `Cohomology/Serre.lean` (the middle/top vanishing declarations), together with `ProjectiveSpace/Canonical.lean` and `ProjectiveSpace/Zero.lean`. The four advertised cohomology declarations do not themselves state every clause of the item: the canonical-module isomorphism and the assertion about every integer twist in dimension zero require separate interfaces. The canonical isomorphism exists elsewhere, but I did not find a single exact declaration or family of exact signatures asserting the entire dimension-zero statement as well as all of this item's clauses. I therefore deliver the natural-language split, making no claim about transitive sorry-freeness and running no compiler.

## WANTED

None. All sources actually used are available locally.

## Corrections and source comparison

The current main-20261015 unit states the same formulas as the repository item, including the restriction of its two top-degree clauses to n >= 1. Its local file has no detailed proof; the unit record preserves the earlier single paragraph about the standard affine Cech cover and Koszul duality. I followed that route using its existing subordinate monomial-computation nodes, writing out what the duality means on bases. I added explicit conventions for Zariski module-sheaf cohomology, k-linear isomorphisms, and omega = the top exterior power of relative differentials. These are explanations of the original statement, with no hypothesis or conclusion changed. There is no statement dispute.

The original statement dependency `sk-def-av-pic` defines the Picard functor, not the notions used here. I removed that dependency and cited the actual twist, cohomology, relative-differential and sheaf-exterior-power definitions. The original proof's phrase “Koszul duality gives the displayed answer” did not justify the dual identification, the n=0 case or the canonical-bundle assertion. Steps 1, 5 and 6 now provide them. The standard-cover method is unchanged; the generic affine-cover comparison `lem-pc-cech-computes` is the precise form needed because every displayed intersection is already a standard affine open. The comparison with ordered Cech cochains is explicit.

Read Stacks `coherent.tex`, `lemma-cohomology-projective-space-over-ring`, including its monomial grading, its three NEG cases, and its contracting homotopy. The precise theorem tag is **01XT**; 01XS is the surrounding section, despite several inherited nodes calling 01XS the lemma's tag. This delivery uses the exact tag and label without editing those other nodes. Also read `lemma-cech-cohomology-quasi-coherent` (01XD), and checked tags 01FJ/01FM for the ordered/alternating comparison. Read the current blueprint files for the projective-space twist cohomology, Serre pairing, canonical bundle and Proj definitions, and the existing canonical node's full chart calculation. The latter supplies the generator-compatible isomorphism independently of the vector-space computation; dimensions alone do not prove a canonical-bundle formula.

## Not duplicates

No new nodes were created. Searches of the entire DAG and `tools/blueprint_refs.py search` for projective-space statements, cohomology and the Euler sequence located the existing monomial calculation, decomposition, exponent-complex homology, pairing and canonical-bundle nodes. I reused them. The commutative-ring cohomology node is more general than the field case here, but lacks the complete canonical-bundle assertion, so it is a dependency rather than a duplicate of the entire item. No new node restates an existing lemma or one of the item's clauses.

## Review by NS

I checked every step against the cited statement itself, rather than extracting facts from its proof. Step 1 uses precisely the final n=0 clause of `lem-pc-projective-space-twist-cohomology`: it explicitly identifies projective zero-space with Spec A and states that every twist is free of rank one and has no higher cohomology. Specializing to A=k gives its global sections k. The degree-zero assertion of `def-sc-sheaf-exterior-power` explicitly gives Lambda^0 = O, including when n=0. Thus the canonical assertion in dimension zero does not use the positive-dimensional canonical lemma outside its hypotheses.

For step 2 I read the statements of `def-pc-proj`, `def-pc-projective-space-twist`, `lem-pc-cech-computes`, `lem-pc-alternating-cech-computes`, and `lem-pc-twist-cech-monomial-decomposition`. Proj makes each D_+(product x_j) affine. The twists are explicitly glued from rank-one free chart modules, so quasi-coherence is the elementary local free-module check. The cover condition follows from exclusion of the irrelevant ideal. These meet exactly the affine-intersection and quasi-coherence hypotheses of the Cech lemma. The ordered comparison is for the ordered set 0,...,n, and the decomposition statement explicitly identifies restriction maps and hence the complex, not only its terms. Here n >= 1, A=k is a commutative ring, and m is any integer, as all these lemmas require. The two off-unit generic comparisons are declared as tool uses in split_report; they implement the required Cech route rather than replacing it.

In step 3 the exponent homology statement states all three cases actually used, including the distinction between empty, nonempty proper and full negative-index sets. The indices and signs agree with the complex specified in the decomposition node. I wrote the finite-support kernel/image argument for passing through the direct sum; no unrecorded exactness theorem is invoked. Step 4 invokes only the polynomial/symmetric-power identification that the existing cohomology node explicitly states in clause (i). Top vanishing is then the written integer inequality, and middle vanishing was already obtained in step 3. Step 5 is elementary finite-basis algebra on those results: the indexing bijection and its inverse, the finite bound on each coordinate, and every dual-basis functional are all explicit. There is no implicit Serre-duality theorem or pairing compatibility claim.

Step 6 uses the full statement of `lem-pc-projective-space-canonical`, read with its hypotheses A commutative and n >= 1 and its definition omega = Lambda^n Omega. Its stated local-generator isomorphism is exactly what the step uses; I did not infer an isomorphism of sheaves from a one-dimensional cohomology group. Step 7 substitutes m=0 into the bases already established, separately retaining the dimension-zero result from step 1. All cited statements were opened and their exact relevant portions are copied into citations.json.

I checked small cases: n=0 and arbitrary positive/negative m, n=1 with m=-1 (no cohomology), m=-2 (one top class), m=-3 (two top classes), m=0 (only the constant global section), and the boundary values m=-n and m=-n-1 in arbitrary positive dimension. These verify the strict negativity and shift -m-n-1, and show why n=0 must be separated before top vanishing. The canonical node gives O(-2) for n=1, with the correct sign dt=-t^2 ds. The proof uses no characteristic restriction, including characteristic 2, and no Noetherian or algebraic-closedness assumption. No new statements remain to check separately. Every step is below 2000 characters, and there is no hidden long-step lemma, circular dependency on this item, new elementary lemma node, or unsplit-node proof. All imported blueprint fields and import flags are preserved. This mathematical self-review is complete. The server validation results are recorded separately below.

## Mathlib searches

The logged LeanFinder queries returned Proj structure-sheaf/localization infrastructure, not twisting-sheaf cohomology. LeanSearch returned generic sheaf/group cohomology and linear projectivization, none of the projective-scheme calculation. The first Loogle query reported an unknown ProjectiveSpace identifier; the second valid Proj/cohomology query returned no hits. Both grep patterns returned zero hits in the specified Mathlib directories. The searches and their results were read and recorded as actually returned in the item and searches.jsonl; no unavailable service is reported as a mathematical absence.

## Unfinished

No mathematical part is left unfinished. No Lean was written or compiled. No repository or launcher file was changed.
