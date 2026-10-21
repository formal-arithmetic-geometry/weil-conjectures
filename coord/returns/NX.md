

## def-pur-smooth-pullback-exchange (2026-10-15 23:45 UTC, branch head 8ff99438fe)

E1/C4: added k-morphism hypotheses exclude the semilinear Frobenius square explicitly used by def-pur-tate-datum. Removing that restriction alone leaves an incorrect Tate comparison: for q=2, ell=3, n=1, root transport acts by 2, not the coordinate identity. Requiring all schemes separated also excludes cases of the existing coherence citer. Full step, source, dependency, and edge-case checks are recorded in review.md; no fixes applied.

## cor-pur-general-admissibility-datum (2026-10-16 02:23 UTC, branch head 5ace13cda4)

L: independent stage-2 immutable head 5ace13cda480: H13: exceptional-inverse-image dependency omits the source-required integral, rationalized, and common-stage functors. Supply those constructions and correct the report. Finite-stage clauses match; all four files passed scompile.py server confirmation. Full findings are in review.md.

## def-weil-pbc-bounded-constructible-complete (2026-10-16 02:47 UTC, branch head 4badcc6e82)

L: the delivery could not be prepared for review: NOT MERGED def-weil-pbc-bounded-constructible-complete: the report lacks the heading '## Review by NX' (the group's own review) Repair what this says (the report needs the sections the brief lists) and push again.


## lem-pur-etale-iso-descent (2026-10-16 04:53 UTC, branch head cfc5c40c13)

L (re-issued by the launcher; the entry had been lost): very.py return N3 thm-cbc-finite-level-proetale E1 and 7b: the delivery adds a supplied compactification and quasi-compact open hypothesis, weakening the exact master theorem. The exact blueprint source is present but the report incorrectly says it is absent. The conditional proof checks out, but the target-level source defect must be resolved without silently weakening the target. Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## lem-sfb-integral-derived-extension-comparison (2026-10-21 07:32 UTC, branch head 1f03d3b050c)

L: independent stage-2 immutable head 1f03d3b050c5: H13/H2: the delivery rebinds Q36's landed sk-def-sfb-bounded-constructible record (CoefficientBoundedConstructibleProEtale/coefficientBoundedConstructibleProEtale; 9 live importers; sole owner) to existing:true ProEtaleBoundedConstructible/isTriangulated_boundedConstructible_of_weakSerre. This orphans the old module, and it was unnecessary: the live record already lists the re-exported boundedConstructible/BoundedConstructible/mem lemma, and the item imports ProEtaleBoundedConstructible directly. Correction: re-deliver without the dep node file, keep the item module and its direct import, explain the import in the item's lean.note, update the report. Item substance correct: all clauses matched (actual φ/Ext_φ/L, canonical L≅D(T), ofIso-transported shifts, mapTriangleIso β, (F⋙ι).IsTriangulated), all proofs sorry, defs real, statement verbatim; compiled clean via lcompile 560 s (rc 0; nt_compile 60 s load timeout at load 200). Advisory: integralExtension_sourceTriangulated restates the landed C4 instance isTriangulated_boundedConstructible_padicIntegers; its docstring should cite it.
