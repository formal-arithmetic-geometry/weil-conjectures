## What changed

Proved all four coefficient clauses in `Sheaf.Paper.CompactFiberStalk`, preserving every existing signature, definition, public import and visibility. Added the proved private helper `compactFiber_integral_membership` to share the detailed-integral category characterization. Added proof imports `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin` and `Sheaf.Paper.WeilTensorProduct`; retained only the five proof imports actually used. Updated the node proof and proof dependencies to follow the Lean argument.

Finite coefficients use the existing bounded etale-origin essential-image criterion, undo intrinsic realization through its equivalence unit, and apply the published finite compact-support exchange theorem. Integral coefficients use the detailed integral characterization, completeness for every generator tuple, and completed compact-support exchange. Rational coefficients apply localization to that invertible arrow. Qbar specializes the existing normalized common-stage theorem after proving its geometric hypotheses.

Validation: the complete pruned module compiled without errors or warnings through lcompile.py in 48.3 seconds. The delivery dry run additionally checks the declaration axiom/sorry probe. Both added proof imports pass import_direction.py. No target statement, coefficient presentation, or canonical exchange definition changed.

## Proved and sorry left

Closed 4 original holes, all belonging to `lem-pur-cfiber-stalk`:

- `WeilConjectures.PurityFiniteSetting.compactFiber_finite`
- `WeilConjectures.PurityFiniteSetting.compactFiber_integral`
- `WeilConjectures.PurityFiniteSetting.compactFiber_rational`
- `WeilConjectures.PurityFiniteSetting.compactFiber_qbar`

Sorries left in the item: zero. Holes added: zero. Split off: zero. These are proofs from existing declared results, some of which still have their own recorded proof obligations; this is not a claim that the entire transitive axiom closure is already sorry-free.

## No longer needed

Removed the following 27 direct proof imports. Some remain visible transitively through unchanged public imports; this report claims direct dependency pruning, not that all these modules leave the targets' global closure.

- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`
- `Sheaf.AlgebraicGeometry.GeometricFiberFinite`
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`
- `Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport`
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`
- `Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange`
- `Sheaf.Paper.CompletedDirectImageLimits`
- `Sheaf.Paper.CompletedOpenExchangeTransport`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Paper.DerivedPullbackTensorHom`
- `Sheaf.Paper.FiniteExtensionCompactSupportBaseChange`
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`
- `Sheaf.Paper.GlobalFiniteLevelCompactSupportBaseChange`
- `Sheaf.Paper.IntegralUniformCoefficient`
- `Sheaf.Paper.IntrinsicQbarCategory`
- `Sheaf.Paper.PbcDescentFunctors`
- `Sheaf.Paper.PbcQbarCategory`
- `Sheaf.Paper.PbcQbarCompletedPullback`
- `Sheaf.Paper.PbcRationalCategory`
- `Sheaf.Paper.PbcRationalTransport`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.Paper.QcqsCompactSupportRealization`
- `Sheaf.Paper.SfCbcExtensionZeroCompletion`
- `Sheaf.Paper.SfDerivedComplete`
- `Sheaf.Paper.SfIntegralConstructible`
- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`
- `WeilConjectures.Compactification.BaseChange`

The following former direct node dependencies are no longer used by this proof:

- `cor-weil-pbc-geometric-fiber-finite`
- `def-compact-support-direct-image-detailed`
- `def-pur-completed-coefficient-presentation-transport`
- `def-weil-algebraically-closed-coefficients`
- `def-weil-derived-complete-integral-detailed`
- `def-weil-derived-pullback-tensor-hom`
- `def-weil-integral-rational-qbar-compact-support`
- `def-weil-pbc-bounded-constructible-complete`
- `def-weil-pbc-completed-pullback`
- `def-weil-pbc-etale-origin-witness`
- `def-weil-pbc-geometric-stalks`
- `def-weil-pbc-qbar-category`
- `def-weil-pbc-rational-category`
- `lem-cbc-completed-extension-zero-comparison`
- `lem-sf-cbc-extension-zero-completion`
- `lem-sf-proetale-constructible-origin`
- `lem-weil-pbc-constant-completion-equivalence`
- `lem-weil-pbc-inverse-image-stalk-germ`
- `prop-weil-pbc-descent-functors`
- `prop-weil-pbc-direct-image-limits`
- `prop-weil-pbc-rational-transport`
- `thm-cbc-finite-extension`

The unchanged statements already have the stalk/fibre endpoints and canonical arrows, so the proof need not rederive stalk comparisons or compact-support realization. The published finite exchange packages its proper/open proof. The completed exchange packages its tower and extension-by-zero argument. The rational arrow is literally localization, so preservation of isomorphisms suffices. The Qbar theorem packages coefficient transport and descent. Retained all public imports to preserve the external interface. The unit record has no separately realized statement or proof-step nodes being bypassed.

## Where the brief, the DAG or earlier work was wrong

The plan named coefficient-presentation and stalk bridges that the final Lean signatures have already incorporated; repeating them would prove more than the displayed claims require. The finite essential-image theorem directly matches intrinsic constructible cohomology after extracting its bounds, avoiding the older continuous-function coefficient presentation.

Tool use for independent review: `wfConstructible_complete` is an existing generic theorem of `Sheaf.Paper.WeilTensorProduct` (node `def-wf-tensor-product`, another unit). Its statement quantifies over arbitrary schemes and adic data and supplies exactly the intrinsic-completeness predicate required here, with no Weil structure or Frobenius hypothesis. It proves independence of generator tuple and representative, which the existential completeness membership alone does not immediately provide. No top-level tool approval was added; the reviewer should assess this auxiliary use. `lem-weil-pbc-finite-ring-constructible-derived-origin` is an existing proved theorem used for the finite etale antecedent. No new nodes or statements were needed.

The scoped 10000-heartbeat option bounds elaboration of the large common-stage formula; it does not raise the project limit. The clean 48.3-second compile includes it. All chapter hypotheses remain explicitly present via the existing include commands; the unused-section-variable lint is scoped to the four proofs because the general exchange theorems require fewer hypotheses.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
