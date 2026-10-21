# Stage-1 report: lem-sfb-lattice-supported-hom-finite-comparison

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-lattice-supported-hom-finite-comparison.json`: statement item, now split into seven steps; no Mathlib match for the complete statement.
- No new DAG nodes and no Mathlib leaves.
- `citations.json`: one entry for every step/node citation, quoting the cited statement verbatim in full so that all used clauses remain visible.
- `searches.jsonl`: actual Mathlib searches run by msearch.py. The parent's five pre-existing search records in the item are retained; six searches performed in this sandbox are appended with the original query text and actual outcome.
- `build_split.py`: sandbox-only preparation script, not a library or launcher edit.

## Attachments

None. I searched the actual project `lean/WeilConjectures/` for the exact blueprint tag and for supported lattice Hom, finite coefficient Hom and the comparison terminology. No declaration gives all the stated clauses. Ordinary finite-coefficient internal-Hom files and their import references do not give the integral-to-finite supported-lattice comparison, so no attachment is asserted.

## WANTED

No new document requested. Existing arithmetic nodes already record the absent Serre Local Fields reference. This split invokes their explicit stated results, without purporting to supply or split their proofs.

## Audit of the imported item

The item was an unsplit node with a complete statement and no proof; the sandbox contained only dispatcher brief markers. I copied the live item and retained its statement, statement dependencies, source, blueprint provenance and prior searches. There is no statement dispute and no source correction. The proof follows the unit's Lattices / Torsion targets / Integral targets route: scalar reduction of the lattice, finite-coefficient support-Hom, and the scalar adjunction. It does not change the chapter or the unit.

The implicit comparison needed more care than merely applying the integral projection formula. An isomorphism between underlying integral complexes does not, by itself, specify the isomorphism in the finite coefficient category. Steps 4 and 5 now distinguish these assertions. Step 5 constructs the finite-coefficient arrow as the derived scalar adjunct of the actual quotient map and proves its underlying quotient augmentation is a quasi-isomorphism. The source is a lattice; the target remains arbitrary in the ordinary unbounded derived category. Flatness is used only for the locally free source and its dual, never for R_X -> A_{n,X}.

## Searches and reuse

Whole-DAG searches covered scalar adjunctions, quotient resolutions, reduction of duals, locally closed extension, finite quotient rings and local finite-free derived scalar extension. Blueprint searches included `coefficient`, `closed-support`, `stratum`, `scalar adjunction`, `locally free derived`, `lattice supported` and `finite coefficient comparison`; the last two had no match. The ancestor command returned det-uniform-constructible-ext-integral. Its Integral targets sentence and the unit's Torsion targets supported complex are the recorded blueprint places. The whole item has no blueprint equivalent, so same_as remains empty. Existing support and projection nodes are reused, rather than duplicated as new clauses.

All Mathlib searches were run through the prescribed msearch.py. Both semantic phrasings returned ordinary module extension/restriction adjunctions, general Ext/cohomology identifications, or unrelated complex-extension lemmas. Loogle returned no hit. The CategoryTheory greps returned either no hit or unrelated injective/projective complex-extension lines. I read the relevant returned candidate `ModuleCat.extendRestrictScalarsAdj` in ChangeOfRings.lean (line 885), and `SheafOfModules.PullbackConstruction.adjunction` in Sheaf/PullbackContinuous.lean (lines 76 onward), as well as the surrounding ordinary sheaf pullback adjunction (line 60). They concern ordinary scalar adjunctions or underived sheaf pullback; they do not state the unbounded supported-Hom coefficient comparison and all its reduction/dual clauses. No search service was unavailable in this run.

## Not duplicates

No new nodes. The local dual reduction is an explicit basis computation in step 3. Source reduction is proved in steps 4–5 from the existing projection formula, quotient resolution and scalar adjunction. Neither clause was moved into a new node. The finite-quotient, locally-free derived-scalar and support-Hom facts all cite existing statements.

## Review by Q68

I read the chapter and unit records, the current main-20261015 uniform-Ext proof (especially Lattices, Torsion targets and Integral targets), the derived-extension-of-scalars definition, the closed-support statement and stratum proof, the complete locally closed tensor-projection proof, and the derived-Nakayama quotient-resolution proof. For external cross-checks I read Stacks Tag 07A6, sites-cohomology.tex, label lemma-adjoint; Tag 0GN1, sites-modules.tex, label lemma-flatness-sheafification-refined; Tag 093M, sites-modules.tex, label lemma-completion-flat; and Tag 09BM, proetale.tex, label lemma-closed-immersion-complement-retrocompact-exact. These support the existing nodes rather than replacing citations of their statements. No SGA source is used. There are no new nodes requiring separate literature verification.

Step 1 uses exactly the coefficient datum's DVR/finite-residue clauses and the finite quotient lemma's finiteness conclusion. The DVR lemma applies to the nonarchimedean absolute value on E and its uniformizer, all supplied by the coefficient datum. The l-adic absolute-value definition gives |ell|=ell^{-1}; hence ell lies in the maximal ideal (pi), and ell^n annihilates the quotient. This avoids an unjustified assertion that ell itself is a uniformizer in a ramified extension. Finiteness and ell-primary torsion are both established before the finite-coefficient support theorem is applied.

Step 2 uses the exact sequence explicitly in det-pe-derived-nakayama-resolution, not merely a definition of coefficient reduction. Thus the condensed quotient coefficient is the actual sheaf cokernel on every scheme. On a trivializing slice the reduced lattice is A_n^r; the generic locally-free-derived-scalars lemma therefore applies on the chosen small site with arbitrary quotient ring map. Its statement explicitly supplies flatness, K-flatness and the comparison in D(Mod(A_n)), without requiring flatness of the quotient. This covers locally varying rank and rank zero.

Step 3 is an elementary step, with no hidden external dual-base-change lemma. I wrote the well-defined evaluation formula and checked it on coordinate functionals. The formula commutes with restriction and changes of basis, so the local inverses glue, and it directly proves evaluation compatibility. Both integral and reduced duals are locally finite free by the same coordinate calculation.

Step 4 invokes exactly the relative derived projection formula stated by det-lem-int-tensor-projection for an open immersion into a closed immersion, with the source L_0 and the integral module underlying A_n. Its schemes and immersions satisfy the standing finite-type hypotheses. Its statement also supplies exact termwise i_* and u_!. Cartesian coefficients explicitly identify a^*A_{n,X} with A_{n,S}. I checked the nu statement of lem-sfb-slice-scalar-hom-chain-adjunction: it supplies underlying R-linear tensor = restriction of ordinary scalar extension, and applying it on K-flat representatives gives the same identification for derived extension. It is not being cited for an unsupported assertion about support or finite coefficient Hom. The equality of the restricted actions follows from the prescribed open-extension and closed-pushforward definitions in the item's statement dependencies.

Step 5 supplies the finite coefficient refinement. The normalized derived coefficient adjunction really states x tensor a |-> a g(x), so applying it to the quotient Q -> Res(a_!L_{0,n}) gives an A_n-linear derived arrow. The quotient resolution states underlying reduction is the cone of pi^n. Local freeness makes pi^n injective on L_0, and exactness of the composite extension preserves the short exact quotient sequence. Thus its two-term quotient augmentation is a quasi-isomorphism. On a K-flat representative the adjunction's formula gives that same augmentation, so the actual coefficient arrow is invertible after restriction. Restriction leaves the sheaf complex and cohomology kernels/cokernels unchanged, hence detects this invertibility. This is the place where I checked that an integral isomorphism was not silently promoted to a finite-coefficient isomorphism. The step is 1,382 characters and is one quotient-augmentation argument; it does not hide a general new comparison theorem.

Step 6 applies the stated derived Hom adjunction on the same small site to Q and Kbar[q]. Its hypotheses permit every unbounded target and every quotient ring map. The formula shows additivity; target naturality is in the cited statement. Termwise restriction commutes with every integer shift. Precomposing with the inverse of the fixed source reduction gives the second comparison, naturally in Kbar.

Step 7 uses the Hom/cohomology assertion of det-lem-formal-closed-support-stratum, not merely full faithfulness of a pushforward or a definition. A_n is admissible by step 1, the finite locally free source is finite locally projective by step 2, and the closed/open factorization and support kernel are precisely the ones in the statement. The sk-lem-formal-closed-support statement has the same i^*kernel definition and ordinary unbounded right derivation. Substitution of the evaluated dual from step 3 gives the desired complex. The reduced dual's K-flatness, supplied by locally-free-derived-scalars, justifies termwise tensor for every complex; there is no boundedness assumption to discharge.

I checked B1–B10: self-contained item objects and definition dependencies are retained, TeX is singly escaped in the mathematical strings, no new statement-only or Mathlib node is misclassified, all searches are actual and logged, and there is no unsupported attachment. I checked C1–C8 against the complete statement of each cited node, wrote all quotes in citations.json, and declared the generic off-unit tools in split_report.tool_uses; the support nodes are on the unit's existing route. I checked D1–D5: the item carries its seven-step proof and creates no restatement nodes; no dependency is on the item, and no argument is deferred as 'standard'. I checked E1–E6 by retaining the actual coefficient rings, integral restriction versus finite derived category, exact quotient map, and all finite-type and local-freeness assumptions.

Small cases checked: n=1, ramified E (ell is only a multiple of pi), L_0=0, locally varying ranks, S empty, Z empty, Z=X, u the identity, Kbar=0 and negative q. For a point with i=u=id and a rank-r lattice, the source is R^r, scalar reduction is A_n^r, and the comparison gives H^q(Kbar)^r. A quotient A_n need not be flat over R; resolving it by [R --pi^n--> R] explains why the stated derived reduction is nevertheless concentrated in degree zero for this source.

## Unfinished work

None at stage 1. No Lean was written and no compiler, Lake or build tool was run. Required server dry run and delivery follow this report.
