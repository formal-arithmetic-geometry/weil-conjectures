## What changed

Replaced the sole `sorry` of `WeilConjectures.openQuotientKoszulCompleteness` by a complete Lean assembly. The arithmetic, coefficient and open-operation constructions are proved inline in private helpers:

- `openDvrUniformizer_ne_zero` and `openDvrResolution_properties`: use the existing DVR arithmetic and a short exact module sequence; the mapping cone has finite free, projective terms and a quasi-isomorphism to the positive quotient.
- `dvrFiniteComparison`, `dvrFiniteComparison_constants`, `dvrConstants_hom_ext`, `dvrFiniteComparison_naturality` and `dvrCoefficientModel_exists`: construct finite constant/function sheaf comparisons, prove constants and transition equations, take the limit comparison and construct its actual scalar restriction equivalence.
- `dvrConstantOpenIso`, its constants/naturality lemmas and `dvrOpenModel_exists`: construct the finite open comparisons from constant-sheaf pullback, their completed projection equations and actual ordinary open extension.
- `dvrCompletionModel_exists` and `dvrActualUnit_isIso`: combine the normalized tower comparison with the specified Koszul/intrinsic equations and reflect unit invertibility through the coefficient equivalence.

Moved the existing DVR interface declarations verbatim into `Sheaf.SixFunctors.OpenQuotientKoszulModels`, publicly reexported by the original module. This permits three separate transport lemmas without an import cycle. All original signatures, definition bodies, instance priorities and visibility are preserved. The main theorem signature and declaration docstring are byte-identical. No source-library file or target statement changes.

The three retained holes separate strict augmentation transport, the intrinsic unit criterion and intrinsic open preservation. Each excludes the other two arguments, the arithmetic existence and the open/finite coefficient construction; none restates the entire original theorem. Their docstrings and nodes specify the actual units, not arbitrary isomorphisms of completion objects.

Verification: all seven delivered modules compile together. The two downstream modules `Sheaf.Paper.CompletedOpenTensorSystemRealization` and `Sheaf.Paper.QcqsCompletionUnitLocality` compile unchanged against the packet; their temporary copies are excluded from delivery. This is a single-file/sandbox compile check, not a global library build.

## Proved and sorry left

Original holes: one, `WeilConjectures.openQuotientKoszulCompleteness` (node `lem-sf-open-quotient-koszul-completeness`). Its Lean body is now complete and has no local holes.

Added holes, exactly three, all public theorems with `:= by sorry`:

- `WeilConjectures.openDvrAugmentedReductionComparison`, node `lem-sf-open-dvr-augmented-reduction-comparison`.
- `WeilConjectures.openDvrIntrinsicCriterion`, node `lem-sf-open-dvr-intrinsic-criterion`.
- `WeilConjectures.openDvrIntrinsicOpenTransport`, node `lem-sf-open-dvr-intrinsic-open-transport`.

This is a decomposition: one upper hole closed and three strictly partial comparison holes added, local net minus two. It is not a sorry-free proof or a claim of positive net closure progress. The new interface module has zero holes; there are no holes in definitions or private helpers. The arithmetic, finite/completed coefficient transport and ordinary open model require no new admitted result. The total-limit transport and augmented-comparison assembly are also proved. The remaining three transports preserve their canonical normalization and are not mere arbitrary-witness existence constructions.

## No longer needed

Removed direct private proof imports:

- `Sheaf.Paper.CompletedQuotientUnitNormalization`.
- `Sheaf.Paper.CompletedOpenExchangeTransport`.
- `Sheaf.Paper.WeilCompletedTensorReflector`.
- `Sheaf.Paper.DerivedCompleteKoszulReconstruction`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Mathlib.RingTheory.Noetherian.Defs`.
- `Sheaf.CategoryTheory.SequenceProjectionDerivedAdjunction`.
- `Sheaf.CategoryTheory.SequencePushforwardLimitProjections`.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`.
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`.
- `Mathlib.Topology.Algebra.Valued.LocallyCompact`.

No public import was removed. No module was withdrawn. Direct-import removal does not claim global unreachability: the retained interfaces and intermediate nodes still reach several of these generic results. In particular sequenceTensorAugmentationUnit, regular_roos_koszul_unit and completed open preservation remain required below the new comparison nodes.

The original parent no longer needs explicit proof edges to `def-weil-pbc-noetherian-ring`, `lem-weil-valued-dvr-finite-quotients` or `def-pc-perfect-ring-complex`: `PrincipalKoszulStrictReplacement.coefficient_datum` already gives the datum, and the displayed resolution is proved directly. The original K-flat existence, adic reduction/quotient-unit, sequence-unit, regular-Roos and completed-open edges are recorded within the corresponding comparison node or its statement interfaces. These are dependencies moved below a transport lemma, not removed mathematics. The retained Koszul reconstruction route stays intact.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan is retained. The existing general sequence-unit, regular-Roos and completed-open results use different presentations from the recorded DVR interfaces. Applying them requires coherent scalar transport of strict towers, universal derived-limit localization factors, signed singleton Koszul fibers, the universe lift of the datum and the actual open left adjoint. Those equations were not direct Lean applications. They are the precise outstanding comparisons, separately stated with no boundedness, constructibility or scheme finiteness hypothesis. The zero complex and empty scheme cause no exceptional case; regularity of the DVR uniformizer is used only by the criterion, not by augmentation transport.

The interface extraction is a dependency-order repair only. It changes no mathematical object. The stated two-term resolution and the final finite-projection equation are both proved rather than moved to new statements.

## New nodes

`def-sf-open-quotient-koszul-models` attaches the unchanged coefficient, completion and open interfaces to their new module; no proof hole.

`lem-sf-open-dvr-augmented-tower-comparison` records simultaneous quotient tensor and limit transport and the actual augmentation unit. Its assembly is proved.

`lem-sf-open-dvr-limit-comparison` is fully proved: exact equivalence transports the universal right-derived limit comparison; the ordinary comparison is fixed by its projections. `dvrRlimComparison_exists` and `dvrRlimModel_exists` prove the precise localization and projection equations.

`lem-sf-open-dvr-augmented-reduction-comparison` retains only the quotient reduction, strict representative and unit clauses relative to the independently proved normalized limit comparison. This hole contains no remaining limit-equivalence existence obligation.

`lem-sf-open-dvr-intrinsic-criterion` records the equivalence of quotient Roos completeness and invertibility of the transported specified singleton intrinsic unit. It assumes the canonical coefficient model and proves no coefficient existence or open theorem.

`lem-sf-open-dvr-intrinsic-open-transport` records only preservation of the specified intrinsic unit under quasi-compact open extension. It does not assert the quotient criterion or the actual calculus unit conclusion.

All new nodes carry source passages, complete proofs in words, recorded Mathlib searches, a blueprint ancestor and Lean signatures. Change record: `coord/changes/M3-open-dvr-comparison-interface.md`.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
