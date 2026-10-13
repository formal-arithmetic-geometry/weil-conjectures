## What changed

The original module now proves `AlgebraicGeometry.Scheme.complete_punctured_principal_formal_sections` by combining completeness for ideals contained in the maximal ideal, depth-two Hartogs restriction on the punctured spectrum, and a formal-completion comparison for compatible principal thickenings. Its signature, existing docstring and public imports are unchanged. The completion-to-section calculation uses GammaSpecIso naturality and the pullback condition; uniqueness uses both comparison uniqueness and injectivity of the completion map.

The delivery adds three modules and their nodes. `Sheaf.RingTheory.CompleteLocalSubideal` proves completeness for every subideal of the maximal ideal directly from Mathlib: a maximal-ideal-adic limit retains each I-adic congruence because Krull intersection in R/I^n kills its residual class. `Sheaf.AlgebraicGeometry.Morphisms.DepthTwoPunctureGlobalSections` exposes a depth-two Hartogs consequence with a complete proof from the existing Hartogs interface. This proof was already private in `DepthTwoPuncturedPrincipalSliceConnected`; its helpers are reused, with no modification of that other module. `Sheaf.AlgebraicGeometry.Morphisms.PuncturedPrincipalCompletionComparison` isolates the remaining formal-sheaf comparison.

All four modules compile in import order with lcompile.py. No existing statement or definition changes, and no other holder's module is adapted.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.Scheme.complete_punctured_principal_formal_sections`, node `lem-sbc-complete-punctured-principal-formal-sections`.

Added one hole: `AlgebraicGeometry.Scheme.punctured_principal_completion_comparison`, node `lem-sbc-punctured-principal-completion-comparison`, in the new module `Sheaf.AlgebraicGeometry.Morphisms.PuncturedPrincipalCompletionComparison`. Its proof is exactly `by sorry`; its docstring records the source and the full argument. Unlike the original theorem, it assumes no completeness of R and yields a point in the adic completion, not a section on W. The nontrivial step remaining is Stacks 0BLD's comparison of ordinary completion with the inverse limit of sheaf quotients, including their pullback interpretation. This delivery is a decomposition: one upper hole closed, one lower hole added, net zero holes.

The other two new declarations are proved, with no new holes: `IsAdicComplete.of_le_maximalIdeal`, node `lem-sbc-complete-local-subideal`, and `AlgebraicGeometry.Scheme.depth_two_puncture_globalSections_bijective`, node `lem-sbc-depth-two-puncture-global-sections`. The latter uses the existing `isIso_restrictAdjunction_unit_of_depth_two`; dependencies below that interface remain separate items.

## No longer needed

No original import is removed. The original finite-étale section-transfer module is still necessary for the definitions of the thickenings and transitions; its finite-cover theorem is not used in this scalar argument. No planned node or module is pruned globally by this delivery. All three added proof imports are used. When extracting the private puncture calculation, imports of `Sheaf.RingTheory.DepthLeSupportDimension` and `Mathlib.RingTheory.Spectrum.Prime.LTSeries` were omitted from the new module: they serve the original module's connectedness and dimension arguments, not the puncture-section bijection. That original module is unchanged and still needs them.

## Where the brief, the DAG or earlier work was wrong

The original proof plan cites definitions where actual theorem inputs are required. In particular, maximal-ideal completeness does not by itself synthesize the smaller-ideal completeness instance; this is now proved using Krull intersection in the quotient module. The finite-étale section-transfer theorem does not supply the scalar formal comparison; its interfaces only specify the relevant pullbacks. Stacks 0EII's proof invokes 0BLD, which has now been isolated as the remaining source input.

The sources were read at Stacks Tags 0EII, 0BLD, 0AVY, 0BK0, 00IP and 0317. The new formal comparison is deliberately independent of completeness, which is handled separately in Lean. Edge cases: g=0 gives a constant system; nilpotent g gives an eventually constant system. Neither comparison nor the convergence argument cancels g or assumes R reduced. The subideal theorem also includes I=0. The puncture theorem only requires depth two and no completeness. Empty opens are permitted by the interfaces, although a nonzero local ring of depth at least three cannot have an empty puncture. The unit `sk-prop-input-spreading` is unchanged; the new nodes remain below the same scalar local input, and its realized fields impose no additional node-level path here.

Mathlib searches: LeanSearch was attempted for each new result and returned Internal Server Error (recorded as unavailable, with no mathematical verdict). LeanFinder returned eight hits for each query, none establishing the needed result. The completion-query hits included `IsAdic.isAdicComplete_iff` and `IsHausdorff.of_isLocalRing`; the puncture-query hits concerned localization and basic opens; the formal-query hits concerned affine-transition limits and `AdicCompletion.mk_ofAlgEquiv_symm`. Mathlib grep found no corresponding exact theorem. Project grep located the private depth-two puncture bijection reused here and the power-series-specific formal comparisons, which do not apply to an arbitrary principal element of R.

## New nodes

`lem-sbc-complete-local-subideal`, module `Sheaf.RingTheory.CompleteLocalSubideal`: a proved completeness transfer to every subideal of the maximal ideal. It separates the topological convergence part from formal geometry and uses only Mathlib in its proof.

`lem-sbc-depth-two-puncture-global-sections`, module `Sheaf.AlgebraicGeometry.Morphisms.DepthTwoPunctureGlobalSections`: a proved structure-sheaf specialization of the existing depth-two Hartogs theorem. No new sorry is introduced by exposing this previously private calculation.

`lem-sbc-punctured-principal-completion-comparison`, module `Sheaf.AlgebraicGeometry.Morphisms.PuncturedPrincipalCompletionComparison`: the remaining formal-sections comparison of Stacks 0BLD, applied at p=0 after depth-three vanishing. It removes the completeness-to-section part of the original theorem and is the only split-off hole.

No change record is needed: no existing public signature, definition or public command changes.

## Second reading by N3

1. **Comparison with the repository.** I diffed the delivered item against the repository version. The target theorem signature, existing declarations, and definitions are unchanged; the only item change is replacement of its proof and three proof-only imports. The three added modules and node files are new delivery files.

2. **Compilation and proof checks.** I compiled all four modules in import order with `lcompile.py --all`; compilation succeeds without warnings. The original target has no `sorry`; the only remaining `sorry` is the named theorem `punctured_principal_completion_comparison`, exactly as listed above. No `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definition occurs. The proved declarations use only the permitted library axioms (the split theorem necessarily reports `sorryAx`).

3. **Statement and node review.** I checked each added declaration against its node. `of_le_maximalIdeal` states completeness for every subideal of the maximal ideal, the depth-two theorem states bijectivity of canonical punctured restriction, and the completion comparison states the formal family representation in the adic completion without assuming completeness. Each is strictly below the target, has a source, proof description, searches, and matching Lean record. The split comparison is the sole unresolved source input and is not a restatement of the target.

4. **Route and pruning.** The target proof follows the planned unit route: subideal completeness, depth-two puncture restriction, the finite-etale thickening interfaces, and the isolated formal-completion comparison. No existing import or required node was removed; all new proof imports are used. The unit's realized route remains unchanged.

5. **Edge cases and truth.** The arguments do not cancel the principal element or assume reducedness, and cover zero and nilpotent elements and the zero ideal. The punctured hypotheses permit the stated open interfaces. I found no weakened or strengthened existing statement and no shorter applicable Mathlib or upstream theorem.

**Changes made in this second reading:** appended this review section only; no Lean proof or declaration required repair after compilation and diff review.
