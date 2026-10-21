

## def-pur-smooth-pullback-exchange (2026-10-15 23:45 UTC, branch head 8ff99438fe)

E1/C4: added k-morphism hypotheses exclude the semilinear Frobenius square explicitly used by def-pur-tate-datum. Removing that restriction alone leaves an incorrect Tate comparison: for q=2, ell=3, n=1, root transport acts by 2, not the coordinate identity. Requiring all schemes separated also excludes cases of the existing coherence citer. Full step, source, dependency, and edge-case checks are recorded in review.md; no fixes applied.

## cor-pur-general-admissibility-datum (2026-10-16 02:23 UTC, branch head 5ace13cda4)

L: independent stage-2 immutable head 5ace13cda480: H13: exceptional-inverse-image dependency omits the source-required integral, rationalized, and common-stage functors. Supply those constructions and correct the report. Finite-stage clauses match; all four files passed scompile.py server confirmation. Full findings are in review.md.

## def-weil-pbc-bounded-constructible-complete (2026-10-16 02:47 UTC, branch head 4badcc6e82)

L: the delivery could not be prepared for review: NOT MERGED def-weil-pbc-bounded-constructible-complete: the report lacks the heading '## Review by NX' (the group's own review) Repair what this says (the report needs the sections the brief lists) and push again.


## lem-pur-etale-iso-descent (2026-10-16 04:53 UTC, branch head cfc5c40c13)

L (re-issued by the launcher; the entry had been lost): very.py return N3 thm-cbc-finite-level-proetale E1 and 7b: the delivery adds a supplied compactification and quasi-compact open hypothesis, weakening the exact master theorem. The exact blueprint source is present but the report incorrectly says it is absent. The conditional proof checks out, but the target-level source defect must be resolved without silently weakening the target. Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## lem-pe-comparison-injective-left-modules-acyclic (2026-10-21 03:05 UTC, branch head 203385b43b)

A6/D, repair order unfulfilled. coord/repair-notes/lem-pe-comparison-injective-left-modules-acyclic.json records a decision of the human (2026-10-21): the 4757-character proof is too coarse; every non-elementary argument must become its own cited node until each proof is well under 3000 characters, with the statement kept. The note names steps 2 (1369), 4 (804) and 5 (1270). This delivery re-pushes the landed Q41 split unchanged. Compared field by field with the live node: statement, stmt_deps, all five proof steps (byte-identical, still 667+1369+647+804+1270 = 4757 characters), proof_deps, tool_uses, reviewed and lean are all identical. Only six 2026-10-21 Mathlib searches were added and split_report was rewritten. The report says outright that no second decomposition was needed, and it creates no node. The mathematics is correct; I read all of it. Statement checked for associative Λ on X empty, Λ=0, F_p (I_ab not injective) and M_2(F_p). Step 2: the slice-restriction adjunction is correct, using the étale inverse-image/restriction lemma, the slice identification and comparison-pullback with u = W→X. Steps 3–4: 03FD (sites-cohomology l.1862) gives H^q(W,I_ab) = R^qΓ_Mod(W,I) = 0; then 03F3 with X_et/W = W_et, 099W (proetale l.3986, no hypotheses) on W, and 03F3/03FD on X_proet. Step 5: sectionwise exactness gives a zero cohomology sheaf. No cycle (490-node closure). The commutative, finite-ring and abelian variants are special cases, not duplicates. No SGA. A re-delivery should keep the statement and move into new statement-only nodes: (1) for étale W→X, the identification (ν_X^{-1}F)|_W ≅ ν_W^{-1}(F|_W), including slice restriction = pro-étale inverse image; (2) the 03FD+03F3 bridge from module evaluation at W to slice cohomology, for any ring sheaf; (3) R^qν_*M = 0 when R^qΓ_Mod(W,−)(M) = 0 for all étale W. det-pe-injective-acyclicity-reduction covers only commutative Λ. No fixes were written.
