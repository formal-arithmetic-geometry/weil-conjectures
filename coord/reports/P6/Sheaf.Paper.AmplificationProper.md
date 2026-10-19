## What changed

Reduced `AlgebraicGeometry.ProEtale.amplification_of_isProper` to its strict completed-tower
preservation subargument. The original theorem signature and all existing definitions
are unchanged. Extracted the proved finite amplification part into
`Sheaf.Paper.FiniteAmplificationProper`, which checks quotient-order invertibility,
Cartesian geometric-fibre identification, both proper FIN applications, and both
pullback interval clauses in Lean.

Proved both family witness-compatibility subarguments. The pullback proof uses actual
etale inverse-image origins and the canonical scalar/pullback comparison. The proper
image proof uses the published finite-coefficient realization/direct-image comparison
and derives its coordinate comparison by total right derivation. On Noetherian schemes, it transports the existing proper finite-coefficient
extension isomorphism through a functorial bounded-below etale-origin lift. The reduction
of that lift is bounded below by exact faithful comparison. This uses neither perfectness
of one intermediate quotient over another nor boundedness of the scalar extension of
the direct image.

Extracted the shared functor construction into
`Sheaf.Paper.FamilyWitnessCompatibilityFromOrigins`. It lifts etale normalizations and
maps uniquely through bounded-below full faithfulness, checks all three morphism squares,
and proves identity and composition laws. Both family modules use this proved assembly.
The origin lift is an actual essential-image construction through a fully faithful
functor, determined up to unique comparison-compatible isomorphism. No object is chosen
from an unproved mere-existence assertion.

The existing `Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension` is used as a generic
coefficient-change tool, and this use is recorded in the proper-family node's split report.
All new imports in the item itself are proof imports.

Validation: all six delivered modules compile against the current server build in
dependency order (2026-10-19 resume, exit 0). Explicit functor
associators keep scalar-extension functors abstract during kernel checking; the proper
family module compiles within the single-file limit. The target signature is unchanged,
Lean lines are at most 100 characters, and each node's proof dependencies are exactly the
union of its proof-step uses.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.amplification_of_isProper`
(`thm-weil-pbc-amplification-proper`), by decomposition. Its module has zero holes.

The following new public theorems are proved:

- `AlgebraicGeometry.ProEtale.finiteLevelAmplification_of_isProper`
  (`lem-weil-pbc-finite-amplification-proper`).

- `AlgebraicGeometry.ProEtale.pbcFamilyWitnessCompatibility_of_origins`
  (`lem-weil-pbc-family-witness-compatibility-from-origins`).
- `AlgebraicGeometry.ProEtale.pbcFamilyWitnessCompatibility_pullback`
  (`lem-weil-pbc-pullback-family-witness-compatibility`).
- `AlgebraicGeometry.ProEtale.pbcFamilyWitnessCompatibility_directImage_of_isProper`
  (`lem-weil-pbc-proper-family-witness-compatibility`).

Added one hole, exactly the entire proof of its named public theorem:
`AlgebraicGeometry.ProEtale.towerPreservation_of_amplification_witnesses`
(`lem-weil-pbc-tower-preservation-from-amplification`). It still needs quotient-linear
output adic towers over the actual strict functor values, amplitude comparisons across
the coefficient presentations, and common local models in every AMP interval. Existing
normalized local effectivity concludes uniform constructibility but does not explicitly
retain the prescribed local-model interval. That stronger interval conclusion must be
extracted from its construction or proved separately. The module docstring and node give
the full construction and identify its published inputs.

This is one original hole closed and one added: a decomposition, not a sorry-free proof
of the full amplification theorem. The retained attempt had two added holes; the proper
family hole is now closed as well as the already completed pullback family argument.
No definition contains a hole and no existing statement or definition was changed.

## No longer needed

No original public import was removed. The explicit unit-route proof import
`Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel` is retained; the witness
assembly uses its exact faithful comparison through its dependencies. The redundant direct import of
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp` was removed
from the new proper-family module; its needed API is reexported by the required
`RightDerivedFunctor.MapDerivedCategory` module. A trial direct import of
`Mathlib.GroupTheory.OrderOfElement` is unnecessary because existing interfaces provide
the arithmetic lemmas.

The item no longer uses `lem-sc-fibre-dimension-after-base-change`
(`Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange`) or
`lem-weil-pbc-dimension-supremum-local-dimensions`
(`WeilConjectures.Topology.DimensionSupremumLocalDimensions`). Direct pullback pasting over
the same algebraically closed field proves the required geometric-fibre dimension equality,
including empty fibres. Both dependencies and their imports are absent. The obsolete
fibre-dimension tool approval was removed from the item's top-level tool list.

The proper-family proof reuses
`Sheaf.AlgebraicGeometry.FiniteCoefficientRealizationDirectImage`; the former private
constant-section forgetful construction is no longer copied here.

The proper-family proof does not directly use the old intermediate-quotient perfectness
argument, `lem-kun-0f0g`, the exchange/tensor coherence node, or the equality between the
two independently specified scalar mates. It instead uses the already declared proper
finite-coefficient extension theorem. The proper projection theorem remains needed below
that existing tool; it is not pruned transitively. The scalar-mate module is imported for
its canonical bounded-below direct-image site comparison, not its scalar-mate theorem.

The pullback-family module no longer contains a private copy of the full witnessed-tower
assembly. Both family proofs use the new generic module. The pullback-family proof needs
no bounded-constructible output preservation theorem: WIT requires bounded-below etale
origins, which exact inverse image supplies.

The following former direct dependencies were removed from the item node. The two
fibre-dimension nodes listed above are pruned; the others now belong under its
witness/tower subarguments and are not claimed to be pruned transitively:
`def-weil-pbc-bounded-constructible-tower`,
`def-weil-pbc-completed-pullback`,
`def-weil-pbc-etale-origin-witness`,
`def-weil-pbc-proetale-modules`,
`def-weil-pbc-scheme-conventions`,
`def-weil-pbc-tower-preservation`,
`def-weil-proetale-constructible-sheaf`,
`lem-kun-0f0g`,
`lem-sc-fibre-dimension-after-base-change`,
`lem-weil-pbc-comparison-direct-image-canonical-mate`,
`lem-weil-pbc-comparison-pullback`,
`lem-weil-pbc-constant-completion-equivalence`,
`lem-weil-pbc-dimension-supremum-local-dimensions`,
`lem-weil-pbc-normalized-constructible-local-effectivity`,
`lem-weil-pbc-ringed-exchange-tensor-coherence`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lem-weil-pbc-uniform-perfect-quotient-bound`,
`prop-weil-pbc-amplification-consequences`,
`prop-weil-pbc-comparison-direct-image`,
`prop-weil-pbc-direct-image-limits`,
`prop-weil-pbc-site-comparison-finite-level`,
`thm-weil-pbc-site-comparison`.
The old item-level proper-projection tool approval was removed because that tool now
belongs below the proper-family coefficient-extension theorem. No unit statement or
route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The blueprint still calls the intermediate quotient perfect over the preceding quotient.
This is generally false, for example F_2 over Z/4. The proper finite-coefficient extension
theorem supplies the nonperfect quotient case and is the argument now used in Lean.

The previous attempt left proper-family compatibility open and stated it without
Noetherian hypotheses. The new, unlanded helper now explicitly assumes Noetherian source
and target, as required by the existing coefficient-extension theorem and already supplied
by the original amplification theorem. No existing signature was changed.

The original local-dimension detour is unnecessary for the actual hypothesis quantifying
over every algebraically closed field and geometric point.

The early required dry run refused delivery before the 72-minute split threshold. Some
compilation requests received no server answer after retries; these were checked before
retrying. Kernel checking of an expanded functor composition exceeded the file limit;
its origin-lift and normalization data were refactored behind explicit definition APIs.
No launcher or repository tool was edited or bypassed.

Resume checks on 2026-10-19 found no pending delivery push. The required initial dry
run again refused the retained one-hole reduction before the split threshold; the
reference clock had restarted although the sandbox retained the previous attempts.
Earlier transport retries recorded in the scratchpad returned no compiler answer.
Those failures are superseded by successful current-server compilations of all six
modules. The finite-level part was independently extracted and checked during this
resume. No launcher metadata or scripts were changed.

## New nodes

`lem-weil-pbc-finite-amplification-proper` is the proved finite-level part (a),
including the arithmetic and Cartesian fibre identification. It states only the AMP
conclusion and is used by the original three-part assembly.

`lem-weil-pbc-family-witness-compatibility-from-origins` is the proved shared assembly
of a witnessed-tower functor from natural quotient comparisons and supplied etale origins.

`lem-weil-pbc-proper-family-witness-compatibility` is the proved direct-image portion
of step (b), for a single proper map of Noetherian schemes; it is applied to both
vertical maps.

`lem-weil-pbc-pullback-family-witness-compatibility` is the proved inverse-image portion
of step (b), for an arbitrary scheme map; it is applied to both horizontal maps.

`lem-weil-pbc-tower-preservation-from-amplification` isolates step (c), with AMP and WIT
already provided as inputs. It asserts one of the original three conclusions, without
reasserting either finite amplification or witness compatibility. Its one remaining hole
and the work needed are listed above.

No statement/definition change records or consumer adaptations are needed.

## Second reading by P6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
