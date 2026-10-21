

## def-pur-smooth-pullback-exchange (2026-10-15 23:45 UTC, branch head 8ff99438fe)

E1/C4: added k-morphism hypotheses exclude the semilinear Frobenius square explicitly used by def-pur-tate-datum. Removing that restriction alone leaves an incorrect Tate comparison: for q=2, ell=3, n=1, root transport acts by 2, not the coordinate identity. Requiring all schemes separated also excludes cases of the existing coherence citer. Full step, source, dependency, and edge-case checks are recorded in review.md; no fixes applied.

## cor-pur-general-admissibility-datum (2026-10-16 02:23 UTC, branch head 5ace13cda4)

L: independent stage-2 immutable head 5ace13cda480: H13: exceptional-inverse-image dependency omits the source-required integral, rationalized, and common-stage functors. Supply those constructions and correct the report. Finite-stage clauses match; all four files passed scompile.py server confirmation. Full findings are in review.md.

## def-weil-pbc-bounded-constructible-complete (2026-10-16 02:47 UTC, branch head 4badcc6e82)

L: the delivery could not be prepared for review: NOT MERGED def-weil-pbc-bounded-constructible-complete: the report lacks the heading '## Review by NX' (the group's own review) Repair what this says (the report needs the sections the brief lists) and push again.


## lem-pur-etale-iso-descent (2026-10-16 04:53 UTC, branch head cfc5c40c13)

L (re-issued by the launcher; the entry had been lost): very.py return N3 thm-cbc-finite-level-proetale E1 and 7b: the delivery adds a supplied compactification and quasi-compact open hypothesis, weakening the exact master theorem. The exact blueprint source is present but the report incorrectly says it is absent. The conditional proof checks out, but the target-level source defect must be resolved without silently weakening the target. Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## lem-sfb-condensed-product-bar-comparison (2026-10-21 16:42 UTC, branch head 54bc9417c69)

L: independent stage-2 immutable head 54bc9417c69b: H13: the delivered lem-sfb-condensed-product-action-inflation record replaces ND's landed record (module CondensedProductActionInflation, declaration product_action_inflation, the theorem stating the node) with module CondensedActionAbelian, declaration instance productBarActionAbelian : Abelian (ActionModule R P), plus 8 proof-valued instances; product_action_inflation is dropped from declarations. The old record was usable (the new module imports it and extracts every field from it). Correction: leave the dependency node unchanged, move the canonical Abelian instance (toPreadditive := actionPreadditive) and the Grothendieck/additive/exactness instances into Sheaf.CategoryTheory.CondensedProductBarComparison as same-node helpers listed in lean.declarations, and drop CondensedActionAbelian.lean. The item itself was checked clause by clause and is correct: ring, groups and Invariants/ProductInvariants packages canonical; h is asserted by the dependency; ProductBar sections M(S×G^a×H^b) with scalar/restriction/map/faces/degeneracies pinned, applied termwise to the injective resolution; diagonal and H-first iterated totals with differential d_G+(-1)^a d_H+(-1)^(a+b) d_res; derived isos pinned by unit normalizations; comparison determined by the augmentation square and equated with conjugateIsoEquiv(derivedCompositionLeftIso) as derived arrows; naturality for all f, resolutions and lifts; trivial group, N=0 and a=b=0 covered; no hollow definitions; only one sorry; no file changed, so no compile. Advisories: CondensedInternalBarResolution now has a live record (proof dependency only); the second reading is the author's own.
