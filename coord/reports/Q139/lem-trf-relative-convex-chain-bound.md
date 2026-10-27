# Q139: lem-trf-relative-convex-chain-bound

## Files written

- dag/nodes/sec-trace-formula/lem-trf-relative-convex-chain-bound.json: statement item, now split; no Mathlib match. Five proof steps, no statement change.
- citations.json: eight step/node entries, each quoting the cited node's statement verbatim.
- report.md: this report. searches.jsonl records the actual searches; write_split.py is a sandbox-only preparation script.

New nodes: 0. New Mathlib leaves: 0. Existing nodes supply every needed non-elementary fact.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and the relative-convex/convex-chain notions; there was no declaration stating the item. The project GroupTheory rationalization hits concern Tate modules and do not state this assertion.

## WANTED

WANTED: local archival copy of Michael Temkin, Stable modification of relative curves, arXiv:0707.3953v3, Section 2.1, printed pp. 7--8, for lem-trf-relative-convex-chain-bound. I read the author's v3 PDF online at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf. The reference already recorded by the item is contextual: Temkin gives the valuation/convex-subgroup correspondence, relative rational rank, Abhyankar inequality and the height consequence, but not this exact abstract arbitrary-subgroup estimate. The proof is therefore explicitly marked agent-written, and no claim of following a verbatim Temkin proof is made.

## What was wrong or missing

The item had no proof. Its statement is correct as written, including that H need not be convex and Gamma/H is only an abelian group. A tempting use of torsion-free rationalization injectivity would be invalid: Gamma/H can have torsion even when Gamma is ordered. For example Gamma = Z and H = 2Z gives quotient Z/2Z. The proof instead uses the general localization kernel criterion and keeps the extra annihilating integer.

The current blueprint latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md was read, together with the chapter/unit records and the immediate parent lem-trf-valuation-height-coarsening. This is a supporting ordered-group calculation for its existing Temkin height-bound branch, with no change of chapter or unit route. The blueprint does not duplicate the abstract relative estimate. Searches with blueprint_refs.py for convex, linear independent and rational rank found no matching blueprint statement. A whole-DAG statement search found the absolute convex-chain bound, torsion-free rationalization injectivity, rational-rank-zero torsion, and the independent-family cardinal-dimension bound. The first three do not by themselves give the relative estimate; the cardinal bound is reused, together with the existing tensor/localization nodes. There is no reason to create a special-case localization lemma.

Mathlib searches were made through msearch.py and recorded exactly. Both semantic phrasings returned generator-rank, module-length or Hahn/Nobeling independence results, without the arbitrary ordered-subgroup estimate. Loogle Convex, AddSubgroup returned Minkowski convex-body results. A second Loogle query LinearIndependent.baseChange returned an unknown identifier, which is recorded as that search result, not as evidence that all scalar-extension theorems are absent. Two source patterns found no relative theorem; the Algebra/Order grep returned zero hits. Old searches on the imported item were preserved as historical records, and the new queries are in this sandbox's searches.jsonl.

## What could not be finished

Nothing in the requested split. The local Temkin archive remains wanted, but its relevant pages were read online. No Lean was written, no compiler or build was run, and no repository or launcher file was changed.

## Not duplicates

No new nodes were created, so there are no new/existing pairs to compare. In particular, lem-trf-convex-chain-rational-rank is an absolute bound using rrk(Gamma); it does not replace a bound using the convex height of H, whose rational rank can be infinite.

## Review by Q139

I read the item source online in Temkin Section 2.1, printed pp. 7--8, and the current blueprint locality proof. I checked the exact statements of every node cited below, and the Stacks source in literature/stacks-project/algebra.tex: the fraction equivalence relation before Definition 07JZ, the localization map, Lemma 00DK (lemma-tensor-localization), and Lemma 00D2 (lemma-tensor-with-bimodule). I also read the reused cardinal-dimension lemma and its Mathlib source, LinearIndependent.cardinal_lift_le_rank at Dimension/Basic.lean lines 84--89, and the Mathlib localization base-change instance at BaseChange.lean lines 244--254. There are no new nodes needing separate source reviews.

Step 1 uses def-trf-totally-ordered-abelian-group only for the inherited translation-invariant total order. It proves intersection convexity directly with x required to lie in H; it never treats H as convex in Gamma. The finite counting argument deletes equal consecutive terms and counts precisely the strict intersection jumps. The assumed bound applies to the resulting chain even when its endpoints are not zero or H.

Step 2 uses the same ordered-group definition to choose positive representatives and compare x_i with m x_i for a positive integer m. Subgroup closure under negation makes the sign replacement legitimate. The saturation observation is written out from convexity and uses no quotient order or Archimedean assumption. It is a two-line consequence of the definition and remains a proof step rather than an artificial new node.

Step 3 uses the full statement of lem-weil-pbc-localization-tensor-over-base with R=A=M=Z, T the nonzero integers, and N=G=Gamma/H, all of which satisfy its hypotheses. The theorem actually supplies the localization/tensor isomorphism and its formula on pure tensors; it is not merely a definition cited for a theorem. def-weil-pbc-module-tensor-product supplies the universal property for the unit and symmetry maps, with both inverses explicitly written. def-weil-pbc-module-localization supplies induced localization maps and, in its statement, the exact kernel criterion m/1=0 iff some u in S annihilates m. The identification of S^{-1}Z with Q is checked by the rational fraction equality criterion. These are elementary specializations and unit/symmetry formulas of existing nodes, not a hidden new comparison theorem. The final sign adjustment turns a nonzero annihilator into a positive integer. In particular G is never asserted torsion-free.

Step 4 uses tensor bilinearity from def-weil-pbc-module-tensor-product, the kernel calculation of Step 3 and the convexity observation of Step 2. It writes the common denominator as an actual product of positive denominators and the integer coefficients explicitly. After applying the positive annihilator, the sum is in H AND C_j. Its membership in C_{j-1} uses exactly the plateau equality C_j intersect H = C_{j-1} intersect H; subtracting all earlier terms isolates the nonzero multiple of x_j. This proves independence directly with no unstated flatness, tensor exactness, dimension additivity or quotient-order theorem. I marked this step elementary because it is the displayed largest-nonzero-coefficient argument from the preceding steps and bilinearity, rather than an appeal to another result. No new node just restates this substantive part of the item.

Step 5 uses lem-trf-independent-family-cardinal-dimension, whose statement explicitly allows arbitrary-dimensional vector spaces and a finite independent family, and def-trf-rational-rank, whose statement gives cardinal-valued dimension. Thus there is no illicit finrank calculation in an infinite-dimensional space. Enumerating I is legitimate because I is a subset of the n indices. The two complementary finite sets give n = |I| + |J| and conclude the required bound.

I checked the B--E delivery cases against these sources and statements: self-contained hypotheses, unchanged statement, correct tags/labels, no invented search records, no cycles or duplicates introduced, and no new clause standing in for the item's proof. Every cited statement is quoted verbatim in citations.json, including definitions where the proof uses their formulas. The two non-elementary steps are under 2000 characters; no long step hides a lemma. The specializations of the general localization theorem and the finite largest-index argument remain explicit proof steps.

Small cases: n=0 is immediate; I empty gives only the h count; H=Gamma makes all strict inclusions intersection jumps; H=0 leaves the usual rational-rank bound. Gamma=Z, H=2Z has quotient torsion and e=0; its sole possible convex jump is detected in H, so no quotient injection is presumed. Gamma=Z^2 in lexicographic order, H=Z(1,0) is a nonconvex ordered subgroup of height one with quotient rational rank one, and its two-step convex chain has one plateau and one intersection jump. Allowing an infinite rational-rank Archimedean H is harmless because the proof uses only its chain bound, never its rational rank. These checks support the arbitrary-subgroup formulation without adding hypotheses.
