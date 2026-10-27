# Q42 stage-1 report: lem-sfb-rational-reflection-simple-base-orbits

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-rational-reflection-simple-base-orbits.json: item, split into six proof steps; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-spanning-reflections-root-pairing.json: statement, Mathlib leaf. RootPairing.mk'' (Basic.lean:260) gives the prescribed pairing and the simultaneous reflection permutations; RootPairing.isRootSystem_mk'' (Basic.lean:269) gives coroot spanning from root spanning and integral pairings.
- dag/nodes/sec-six-functors-basics/lem-sfb-reduced-rational-root-pairing-base.json: statement, Mathlib leaf. RootPairing.nonempty_base (BaseExists.lean:322) with precisely the stated rational, finite, spanning, crystallographic and reduced hypotheses.
- citations.json: verbatim full statements for each of the three proof-step citations. searches.jsonl: actual msearch results. report.md: this report.

## Attachments

None. Searched lean/WeilConjectures/ for the item id and for RootPairing, simple roots and simple reflections. No project declaration states the item. Related modules under lean/Sheaf/ concern Lie-algebra input, not this statement; they are not attachments.

## WANTED

None. Read the local Milne Algebraic Groups PDF, Appendix C.1, C.3, C.12--C.22 (printed pp.607--612), and the local pinned Mathlib sources. No SGA source was used. Extracted source text is retained only in this sandbox as milne-source.txt.

## Findings and changes

The item was unsplit, with no Lean attachment or repair order. There was no earlier sandbox split or report to overwrite. Its imported searches were preserved. They had correctly identified nonempty_base and induction_reflect but also the missing passage from unbundled reflection data to a bundled root pairing. I supplied that passage and ran new logged searches for each new leaf, as well as additional searches for the whole item. LeanFinder and LeanSearch returned mk'' and isRootSystem_mk'' for the constructor; the exact Loogle and grep results and the declarations' full local types confirm the matches. The constructor grep was also run on the RootSystem directory to obtain file names and verified lines. The unsuccessful combined Loogle query for the whole item is recorded as zero hits; it is not used to reject the separately located theorems.

The proof retains the rational field throughout: restriction makes the generated reflection group finite, a rational coordinate dot product is averaged over that group, and its reflection formula proves injectivity of the prescribed coroots. This gives precisely the missing input to mk''. Base existence and the existing reflection-induction leaf then finish the argument. The averaging and injectivity calculations are proof steps, not unnecessary new nodes. Every non-elementary fact used is supplied by a cited node. Each step is under 900 characters; none is a long step that could conceal a lemma.

Read the chapter and unit records, SETUP's three levels, and the current latest blueprint's sk-thm-sf-ctf-stability section and direct-image proof (3). This is a supporting root-system calculation below the unit, on the inherited alteration/moduli route; it changes no unit or chapter. Whole-blueprint searches for root pairing, roots, coroot, crystallographic and simple roots locate no equivalent imported blueprint statement. blueprint_refs.py ancestor reports None for this chain. I retained the item's inherited null ancestor and extended its exact from.place and via chain on each new leaf rather than inventing a blueprint ancestor. same_as is [] throughout.

There is no STATEMENT-DISPUTED: the rational hypotheses match Milne C.14 and reducedness C.18, and the conclusions match C.21--C.22. C.19 supplies the finite averaging formula, and C.20 its reflection formula. No hypothesis or conclusion was changed. Nothing mathematical remains unfinished in the item's split; the two supporting nodes are already Mathlib leaves.

## Not duplicates

lem-sfb-spanning-reflections-root-pairing vs lem-sfb-finite-spanning-reflection-uniqueness: uniqueness of one functional does not construct simultaneous root/coroot permutations or show that coroots span. The new leaf starts with injective paired families and only root stability and gives exactly those missing conclusions.

lem-sfb-spanning-reflections-root-pairing vs lem-sfb-killing-cartan-reduced-root-pairing: the existing leaf starts from a Killing Lie algebra and a triangularizable Cartan subalgebra; the new leaf is pure linear algebra, with no Lie algebra.

lem-sfb-spanning-reflections-root-pairing vs lem-sfb-rational-reflection-simple-base-orbits: the new leaf assumes the coroot injection and a perfect pairing and produces the paired reflection axioms and coroot spanning, not a base or orbit statement. The item's steps 1--3 supply the injection, and steps 5--6 prove its actual conclusions.

lem-sfb-reduced-rational-root-pairing-base vs lem-sfb-crystallographic-positive-base: the existing leaf proves independence of a prescribed indecomposable positive support in a perfect integral pairing, assuming a nonvanishing integer functional. It does not state existence of a rational RootPairing.Base with simultaneous root and coroot axioms. Converting the rational evaluation pairing to a perfect integral pairing and choosing the functional would require extra arguments.

lem-sfb-reduced-rational-root-pairing-base vs lem-sfb-root-base-rational-integral-spans: the existing leaf assumes a linearly independent support with root sign decompositions and proves basis/span and coroot properties. The new leaf asserts existence of a support; no support is an input.

lem-sfb-reduced-rational-root-pairing-base vs lem-sfb-root-base-reflection-induction: induction assumes an existing base; the new leaf supplies one. The item's step 6 cites the existing induction leaf rather than duplicating it.

lem-sfb-reduced-rational-root-pairing-base vs lem-sfb-root-chamber-simple-transitivity: the existing real chamber theorem assumes an orthogonal realization and describes chambers and the action. The new leaf is the exact rational bundled nonempty_base theorem, with no scalar extension, topology or chamber assertion.

lem-sfb-reduced-rational-root-pairing-base vs lem-sfb-simple-root-reflection-generation: generation assumes a real sign-coherent root basis. It does not construct a rational bundled base.

lem-sfb-reduced-rational-root-pairing-base vs lem-sfb-rational-reflection-simple-base-orbits: this is an exact Mathlib leaf for already bundled spanning root/coroot data, not a new unsplit restatement of the item's clause. The missing coroot injection and pairing construction remain explicit in the item's earlier steps, and the orbit assertion uses a separate existing leaf.

lem-sfb-spanning-reflections-root-pairing vs lem-sfb-root-datum-realization: the existing statement constructs split reductive algebraic groups from root data; the new leaf only verifies the linear root-pairing axioms. No group scheme is involved.

The source places here are Milne Appendix C and the Mathlib declarations, not Stacks tags; there is no shared-Stacks-tag pair to resolve. Neither new node is elementary: one packages the reflection compatibility and coroot spanning theorem, the other base existence. Both are actual searched Mathlib results. Neither new node depends on the item or on its rank-two parent.

## Review by Q42

I checked delivery-errors B--E with the written files and primary sources open. For the item I read Milne's finite reflection action C.15, the explicit averaging formula C.19, the reflection/coroot formula C.20, and the base and orbit assertions C.21--C.22. For the constructor leaf I read Basic.lean:247--275 including all section hypotheses, and Defs.lean:98--112 for the structure's two simultaneous permutation identities. This confirms that coroot stability is a conclusion, not an unproved input hidden in step 4. For the base leaf I read BaseExists.lean:113--115, the IsReduced assumption at line 197, and lines 311--328, and Base.lean:70--78 to check what a Base actually contains. The source gives the exact rational specializations claimed in the two mathlib_match records.

Step 1 writes the involution calculation and the faithful restriction to the finite permutation group. It uses only normalization, linearity and spanning. Step 2 gives the actual finite-sum formula, positivity from the identity term, the reindexing bijection, and the equation deriving c_r. Nothing assumes a real completion or equal root lengths. Step 3 proves coroot injectivity: nondegeneracy here is checked by evaluating B(u,u), and applying the common functional to the resulting scaled-vector equality proves equality of the two squared lengths and then of the roots. These are explicit elementary calculations and create no node.

Step 4 cites lem-sfb-spanning-reflections-root-pairing. Its statement gives exactly the prescribed root and coroot families, simultaneous permutations and both spanning properties. I verified finiteness of I=S, injectivity from subset inclusion and step 3, evaluation perfection by the written dual-basis inverse, normalization, all integral cross pairings and root stability. The claimed reflection equals the original s_r by its displayed formula. Reducedness follows from the supplied root-line hypothesis and is not smuggled into the constructor.

Step 5 cites lem-sfb-reduced-rational-root-pairing-base. Its statement gives independent root and coroot families and the nonnegative integer sums, under precisely the finite, reduced, spanning and integral assumptions established in step 4. Since all roots lie in the simple span and all roots span V, the simple roots span V. Independence plus spanning is the definition of basis; uniqueness of basis coordinates makes the sums the requested coordinates. This last inference uses no theorem about real scalar extension.

Step 6 cites the preexisting lem-sfb-root-base-reflection-induction. I opened its statement and Base.lean:665--674 and matched its three hypotheses separately: empty words for support indices, prepend a simple reflection for closure, and append s_d on the right of a word w(d) to get its negative w(s_d(d)). This proves closure under negation without erroneously requiring that the reflection in an arbitrary root is already a simple word. The root pairing's reflectionPerm formula identifies every step with the specified original s_r. citations.json copies the actual statements of exactly these three cited nodes.

For small cases I checked V=0 and empty indices (the argument exits before choosing a nonzero root), rank one S={a,-a} with one simple root, the orthogonal rank-two system A1 x A1 (the union of two simple-root orbits, not one orbit), and unequal root lengths in B2 and G2 (injectivity does not assume equal lengths, and an orbit may preserve root length). The root line condition excludes nonreduced systems such as {a,2a,-a,-2a}, exactly where the reduced base theorem would otherwise be misapplied. All new statements introduce their objects, retain all hypotheses, have no proof or proof sketch in the statement, and cite their foundational notions inline. No Lean or compiler command was run, no repository file was written, and no agent was started.
