# Stage-1 report: lem-pur-coordinate-boundary-geometric-pullback

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-coordinate-boundary-geometric-pullback.json: statement, split into four proof steps; no Mathlib match.
- citations.json: one verbatim statement quotation for each of the five node citations across the four steps.
- searches.jsonl: search-command records, retained as generated.
- report.md: this report.

New nodes: 0. Mathlib leaves: 0. The sandbox contained no earlier node, report or search log when this attempt began.

## Attachments

None. Searched the live WeilConjectures source by the exact blueprint tag, coordinate-boundary terminology, kummerBoundary and restrictSupportedClass. Read TateTwist/KummerClass.lean (especially leftDerivedUpperStar_map_kummerClassOf, line 247) and Purity/Smooth/Orientation.lean (supportedClassMap_restrictSupportedClass_affineLineOrientation, line 232, and restrictAffineLineZeroLocusHom_affineLineOrientation, line 282). These provide ordinary-etale class/orientation naturality, but do not themselves state all clauses of this item, including its specified exponent m and its canonical etale/pro-etale supported-constant and supported-Hom comparisons. No attachment is claimed on the strength of partial coverage or unseen transitive axiom dependencies.

## WANTED

None. The blueprint, Milne lectures and Stacks sources required for this assembly are present and were read locally.

## What was corrected or clarified

The imported statement is retained, with every hypothesis and all three simultaneous identities. There is no statement dispute. The missing argument is now a proof rather than an invocation of a newly renamed clause. Broad DAG searches and blueprint_refs.py searches for Kummer, coordinate boundary and supported-Hom found existing results sufficient for the whole assembly. In particular the new relative-Kummer coefficient-normalization and site-normalization nodes apply to every k-scheme; the older curve-only coefficient-base-change node would not justify their use on U over an arbitrary Y.

No new nodes were needed. Existing node statements, not their proofs, provide the non-elementary inputs. The elementary first step checks the square by polynomial, Laurent-polynomial and quotient rings. No smooth base-change theorem, arbitrary invertibility of exceptional exchange, or cohomology-with-support base-change isomorphism is used. Only canonical pullback maps and their functoriality are needed.

Mathlib searches were made only through msearch.py: LeanFinder with two different phrasings, Loogle for "Kummer", grep for kummerBoundary|restrictSupportedClass|supportCohomology, and LeanSearch for the pullback connecting-map question. All services answered. Hits concerned general scheme naturality, sheaf free-object or global-section naturality, and arithmetic Kummer extensions; none states the required three identities on both sites. The inherited search entries are retained and the actual current queries/results appended.

## What could not be finished

Nothing mathematical remains in this one-level split. Delivery validation is recorded below when complete.

## Not duplicates

No new nodes, hence no new/existing pairs. Reused lem-pur-relative-kummer-coefficient-normalization, lem-pur-relative-kummer-site-normalization, thm-pur-with-support-exactness and lem-pur-supported-hom-pullback. The item is not equivalent to the blueprint's broader orientation isomorphism/base-change results: it asserts the three class/representative equalities with the specified coefficient construction, without assuming or proving that the purity orientation is invertible.

## Review by Q100

I read the item's source proof in the current main-20261015 blueprint, specifically the sentence asserting that the geometric fibre is the coordinate boundary. I also read Milne, Lectures on Etale Cohomology, printed pages 66-67, including Example 9.5 and the Ext proof of Theorem 9.4: the support sequence comes from the exact sequence of open and closed constants. The arbitrary-pullback and site refinements are recorded honestly as the existing DAG statements rather than attributed to Milne alone. For the Kummer coefficient step I read Stacks Tag 03PL, etale-cohomology.tex, lemma-kummer-sequence, including its explicit root-cover construction, and for comparison I read proetale.tex, lemma-compare-cohomology (099W) and lemma-morphism-comparison (09A6). The latter's qcqs hypothesis is not used to restrict the arbitrary map g: this proof uses cohomology/class comparison and the cited arbitrary-pullback normalization statements, not a direct-image base-change isomorphism for g.

For step 1 I opened def-pur-affine-line-datum and checked that its statement really gives R[t], the quotient t=0 and R[t,t^-1]. Tensoring these presentations with Omega gives the Cartesian pair and the identical coordinate. This is an elementary verification and does not assume that a factorization through an open follows merely from a set-theoretic image condition.

For step 2 I opened both lem-pur-relative-kummer-coefficient-normalization and lem-pur-relative-kummer-site-normalization. The former explicitly gives finite freeness under e|n, root and tensor trivializations compatible with every k-morphism, and u^*kappa(v)=kappa(u^*v). The latter explicitly identifies the actual scalar Kummer class on the two sites and asserts the arbitrary-pullback formula, including geometric points whose residue extension is not of finite type. Thus this step does not derive naturality from a node stating only exactness of Kummer. The calculation zeta^a -> a*1_A in the unchanged root coordinates shows exactly which coefficient morphism is retained. No tensor product of G_m over Z/m is formed.

For step 3 I opened thm-pur-with-support-exactness. Its statement says that the sequence is functorial in the pair and in F and includes pro-etale finite-torsion coefficients. This supplies precisely the commuting square of connecting maps used here. F is a finite torsion sheaf in degree zero; no constructibility or finite-type hypothesis on X' is required by that statement. Substitution of the step-2 class equality gives the support equality with the same sign convention, rather than identifying two generators up to a unit.

For step 4 I opened lem-pur-supported-hom-pullback. Its statement supplies the exact formula with c inverse, allows arbitrary scheme maps and bounded-below F, and explicitly compares the etale and pro-etale supported-Hom identifications, shifts and supported-constant maps. The direction is correct: c inverse maps s'_*A to h^*s_*A, followed by h^*M to F'[2]. I checked that none of the four cited theorem nodes reaches this item through statement or proof dependencies, so no cycle is introduced.

I checked B-E of delivery-errors against the written files. There are no statement-only new nodes needing missing definitions, searches, tags or duplicate comparisons. Each non-elementary input is in a cited node's statement and every citation has a verbatim quote in citations.json. The four proof steps have lengths 544, 799, 510 and 700 characters; none hides a lemma in a step longer than 2000 characters. Edge cases checked: the identity geometric base change preserves all formulas; algebraically closed extensions of positive transcendence degree use exactly the same coordinate-ring and arbitrary-map statements; nonreduced Y is permitted because tensoring a quotient by (t) is valid without flatness; the case n=e gives N=1 and the unchanged pure-tensor map; an empty Y has no geometric point, so the universally quantified assertion is vacuous. The proof preserves the lecture-notes/Kummer route and uses no SGA source.
