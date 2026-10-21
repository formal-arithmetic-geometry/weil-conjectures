

## def-pur-smooth-pullback-exchange (2026-10-15 23:45 UTC, branch head 8ff99438fe)

E1/C4: added k-morphism hypotheses exclude the semilinear Frobenius square explicitly used by def-pur-tate-datum. Removing that restriction alone leaves an incorrect Tate comparison: for q=2, ell=3, n=1, root transport acts by 2, not the coordinate identity. Requiring all schemes separated also excludes cases of the existing coherence citer. Full step, source, dependency, and edge-case checks are recorded in review.md; no fixes applied.

## cor-pur-general-admissibility-datum (2026-10-16 02:23 UTC, branch head 5ace13cda4)

L: independent stage-2 immutable head 5ace13cda480: H13: exceptional-inverse-image dependency omits the source-required integral, rationalized, and common-stage functors. Supply those constructions and correct the report. Finite-stage clauses match; all four files passed scompile.py server confirmation. Full findings are in review.md.

## def-weil-pbc-bounded-constructible-complete (2026-10-16 02:47 UTC, branch head 4badcc6e82)

L: the delivery could not be prepared for review: NOT MERGED def-weil-pbc-bounded-constructible-complete: the report lacks the heading '## Review by NX' (the group's own review) Repair what this says (the report needs the sections the brief lists) and push again.


## lem-pur-etale-iso-descent (2026-10-16 04:53 UTC, branch head cfc5c40c13)

L (re-issued by the launcher; the entry had been lost): very.py return N3 thm-cbc-finite-level-proetale E1 and 7b: the delivery adds a supplied compactification and quasi-compact open hypothesis, weakening the exact master theorem. The exact blueprint source is present but the report incorrectly says it is absent. The conditional proof checks out, but the target-level source defect must be resolved without silently weakening the target. Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## lem-sfb-lisse-lattice-potential-kummer-tameness (2026-10-21 15:37 UTC, branch head af5315f6bba)

Route-pivot drop rule F plus C1. The item is live: it is absent from side-live route-pivot-dropped.txt and its citer lem-sfb-tame-pair-proper-generators is live. However, Step 8 cites lem-per-snc-root-punctured-torsor-splitting, which was dropped on 2026-10-19 (line 1918). That node is the multi-divisor Abhyankar splitting (ILO IX 2.1) and carries the whole tameness content of the item. I searched the snapshot DAG: every live Abhyankar or root-splitting node is one-divisor only (lem-sbc-regular-divisor-galois-root-splitting and lem-sbc-regular-divisor-strict-hensel-root-section use one f; the trait and DVR nodes cover traits and DVRs only), and every r>=2 node is dropped. The one-divisor nodes cannot be iterated, since inverting t_1 destroys locality, so no re-cite and no FIX is possible. Step 6 also cites the dropped lem-per-regular-boundary-divisorial-chart (line 1860), only for regular parameters defining D; that citation alone would be re-citable. Batch-5 finding: that chart's closure reaches def-trf-strict-normal-crossings-boundary, a general definition already in stmt_deps and outside both assumptions, so it is not a fault by itself. Steps 1-5, 7, 9 and 10 were read in full and are correct: HRS Ex. 3.1 transport, the BS 6.8.4(1) reduction tower, 0DV5 residual trivialization, the congruence kernel K_n=1+M_d(varpi A_n) with ell-power order, the 03RV frame torsor, recursive compatible frames, and full faithfulness on T; the cases r=0 and d=0 are fine. No SGA. This is the third RETURN of this item for the same citation (NL, N5 68c9bff0, now NX). The maintainer must either un-drop the generic SNC Abhyankar node or withdraw the item, otherwise re-dispatch loops.
