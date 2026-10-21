

## def-pur-smooth-pullback-exchange (2026-10-15 23:45 UTC, branch head 8ff99438fe)

E1/C4: added k-morphism hypotheses exclude the semilinear Frobenius square explicitly used by def-pur-tate-datum. Removing that restriction alone leaves an incorrect Tate comparison: for q=2, ell=3, n=1, root transport acts by 2, not the coordinate identity. Requiring all schemes separated also excludes cases of the existing coherence citer. Full step, source, dependency, and edge-case checks are recorded in review.md; no fixes applied.

## cor-pur-general-admissibility-datum (2026-10-16 02:23 UTC, branch head 5ace13cda4)

L: independent stage-2 immutable head 5ace13cda480: H13: exceptional-inverse-image dependency omits the source-required integral, rationalized, and common-stage functors. Supply those constructions and correct the report. Finite-stage clauses match; all four files passed scompile.py server confirmation. Full findings are in review.md.

## def-weil-pbc-bounded-constructible-complete (2026-10-16 02:47 UTC, branch head 4badcc6e82)

L: the delivery could not be prepared for review: NOT MERGED def-weil-pbc-bounded-constructible-complete: the report lacks the heading '## Review by NX' (the group's own review) Repair what this says (the report needs the sections the brief lists) and push again.


## lem-pur-etale-iso-descent (2026-10-16 04:53 UTC, branch head cfc5c40c13)

L (re-issued by the launcher; the entry had been lost): very.py return N3 thm-cbc-finite-level-proetale E1 and 7b: the delivery adds a supplied compactification and quasi-compact open hypothesis, weakening the exact master theorem. The exact blueprint source is present but the report incorrectly says it is absent. The conditional proof checks out, but the target-level source defect must be resolved without silently weakening the target. Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## lem-sfb-finite-closed-cover-resolution (2026-10-21 17:35 UTC, branch head 23a13b10a3d)

L: independent stage-2 immutable head 23a13b10a3d7: F1 (H3/hollow): FiniteClosedPullbackCompatible only quantifies a comparison c for Z and asserts ∃! derived e with Q(g^*aug_D)≫e = Q(c)≫Q(aug_D'); this is the conjugate e = Q(g^*aug)^{-1}≫Q(c)≫Q(aug'), which always exists since aug is a quasi-iso and g^* is exact; hc is unused. The node's naturality in pullbacks with identified closed-restriction comparisons is missing. Fix: quantify unit-compatible c_s for every intersection Z_J, assert a row comparison σ whose components are Π c_s under terms, compatible with augment, and require Q of its totalization (via g^*Tot≅Tot g^*) to be the augmentation-normalized derived comparison. F2 (theorem stmt_deps, mechanical finding confirmed): lem-pur-proetale-inverse-image-tensor-comparison is used only for the abbrevs Rings/Modules/inverseRing/inverse (unfold to ringedSiteModules, proEtaleSheafInverseImage, proEtaleModuleInverseImage of def nodes): replace them and drop that dep. lem-weil-pbc-proetale-closed-underived-projection is used only for ProEtaleClosedProjection.adjunction (Classical.choose of the helper adjunction_exists in the theorem module, not the theorem's conclusion; no def node owns a public version): move it into a definition node owning a module with the unit-normalized adjunction and cite that node. Checked OK: all hypotheses incl. quasi-compact complementary open immersions; Over-X product intersections; unit-pinned restrictions (units epi); signed Čech differential; augment_unit; total sign d_h+(-1)^p d_v; quasiIso on CochainComplex.plus; derivedIso pinned; refinement clause with sorting signs is genuine; edge cases m=1, repeats, empty intersections, Z empty; universes u/u+1; docstrings and 8-step proof; Worker report and Second reading sections present. No compile (no file changed).
