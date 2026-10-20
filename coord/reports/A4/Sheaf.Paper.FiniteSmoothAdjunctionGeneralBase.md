## What changed

Repair of returned head 54da2eda9: removed the redundant file-local
`set_option warn.sorry false` command from the parent module. The landing ledger
matched the option-name component `sorry` at line 33 as an unattributed hole.
There was no proof hole at that location. Removing the option preserves every
declaration, proof term, definition and public import. The actual remaining
holes are the three named theorems listed below.

The command-inventory change is recorded in
coord/changes/A4-finite-smooth-warning-option.md, including all ten transitive
consumers. No consumer needs adaptation. All six delivery modules compiled in
dependency order in the repair dry run. The source ledger now finds no
unattributed holes and exactly the three named holes reported below.

Preserved every existing signature and definition in
Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase. Replaced its sole sorry with the
Noetherian/Nagata setup, characteristic-to-unit argument, construction of the actual
normalized diagonal/deformation/bundle orientation, and assembly of the finite levels,
reductions, root realizations and quotient cocycles. Cancellation proves the complete
OrientationNormalized equation. Witness selections occur only in the existential proof.

Added five modules for separate parts of the source argument. FiniteSmoothLevelOfOrientation
and FiniteSmoothSiteRealizations are proved. The level proof establishes naturality,
actual-origin constructibility and counit invertibility, independence of every ordinary
origin, trace transport, exceptional/source finiteness, coefficient-unit finiteness and
unit-degree concentration. Adjoint uniqueness deduces the dimension-zero trace from
its purity-map equation. Abstract categorical helpers avoid costly unfolding of the
concrete derived tensor definitions. The root proof constructs the actual scalar and
sheafification comparison, proves its Kan-extension normalization, and checks every
root generator and every pro-etale restriction. Intrinsic compact-support realization
is proved separately in the parent from sfIntrinsicCompactSupportComparison.

## Proved and sorry left

Closed the original textual hole in
AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteSmoothAdjunctionGeneralBase.
The item module now has zero sorry. This delivery is a decomposition: one original
hole closed and three new holes added. It is not a completed proof of all finite purity.
finiteSmoothLevelOfOrientation and finiteSmoothSiteRealizations have no sorry.
The three remaining holes, each a public named theorem in its own module, are:

- finiteSmoothIntrinsicLevelProperties
  (lem-pur-finite-smooth-intrinsic-level-properties): only dimension-zero purity-map
  normalization for a supplied normalized geometric orientation and supplied
  graph-normalized sum comparison. All categorical transport and its trace consequence
  are proved in the level assembly.
- finiteSmoothTwoLevelReduction (lem-pur-finite-smooth-two-level-reduction): the source's
  two-level coefficient argument. Construct normalized root comparisons, prove
  compatibility of the actual diagonal/deformation/bundle orientation with reduction,
  then transport tensor mates, counits and constructible origins to the pro-etale site.
  This proves ReductionData for any two supplied levels; it does not construct a level
  and does not supply the parent's simultaneous system or root-site realizations.
- finiteSmoothQuotientCoherence (lem-pur-finite-smooth-quotient-coherence): the ordinary
  compact-support coefficient cocycle and eight other specified quotient equations.
  The ordinary exceptional cocycle is extracted from the existing exceptional
  coefficient comparison theorem in the parent.

Each remaining statement has its source, proof in words and matching node. None
repeats the parent theorem, and no definition contains sorry or chooses an arbitrary
object from unproved existence. Positive levels and equal quotient levels are retained;
zero objects, dimension zero and empty schemes satisfy the same formulas. The rank-zero
statement retains the entire OrientationNormalized equation. Generator normalization
fixes the root-line comparisons, so quotient coherence applies to arbitrary witnesses
satisfying those normalizations.

## No longer needed

No whole-library module is claimed pruned. Removed these direct proof imports from the
item, relative to the current shared source:

- WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
- Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
- Sheaf.Paper.FiniteReductionConstructibility
- WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
- WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
- WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
- Sheaf.Paper.EtaleUnboundedRestrictionComparison
- Sheaf.AlgebraicGeometry.ProperProjectionFormula
- Sheaf.Paper.ExceptionalCoefficientComparison
- Sheaf.Targets.VectorBundlePurity
- Sheaf.AlgebraicGeometry.VectorBundleIntegration
- Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
- Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
- Sheaf.AlgebraicGeometry.AffineSpaceTopTrace
- Mathlib.AlgebraicGeometry.Morphisms.Etale
- Sheaf.AlgebraicGeometry.DiagonalRegularPureCodimension
- Sheaf.Paper.NoetherianEtaleSectionSpecialization
- Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange
- Sheaf.Paper.PurityDiagonalOrientationCompatibility
- Sheaf.AlgebraicGeometry.SmoothTensorDuality
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
- Sheaf.Paper.FiniteRingSectionDeformation
- Sheaf.Paper.FiniteSmoothGammaNormalization
- Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
- Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
- Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
- Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
- Sheaf.Paper.FiniteRingConstructibleDerivedOrigin

The geometric orientation construction retains exactly its needed dependencies. Parts
needed for the remaining reduction, coherence and realization proofs are recorded in
their own modules and nodes; others are already public prerequisites of the canonical
data interface. The original node's direct proof dependencies were updated to this
assembly, with the corresponding source dependencies recorded below the new nodes.
No unit statement or realized unit step is bypassed.

The three unproved statement modules require only their public
FiniteSmoothAdjunctionData import. Their remaining proof-only imports were unused
by the present statements and proof terms and were removed while diagnosing the
all-files parent compilation timeout. The source proof plans and
corresponding dependencies remain in the DAG for their future proofs. Removed:

- FiniteSmoothIntrinsicLevelProperties: Sheaf.Paper.FiniteSmoothGammaNormalization.
- FiniteSmoothTwoLevelReduction: Sheaf.Paper.ExceptionalCoefficientComparison, Sheaf.Paper.FiniteSmoothQuotientCoherence, Sheaf.Paper.FiniteReductionConstructibility, Sheaf.SecSmoothPurity.ScalarExtensionFunctor, Sheaf.Paper.PurityDiagonalOrientationCompatibility, Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction, Sheaf.AlgebraicGeometry.AffineSpaceTopTrace, Sheaf.AlgebraicGeometry.VectorBundleIntegration, Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback, Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence, Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses, Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate, Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison.
- FiniteSmoothQuotientCoherence: Sheaf.Paper.ExceptionalCoefficientComparison, Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence, Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses, Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback, Sheaf.AlgebraicGeometry.ProperProjectionFormula, WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison, WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs.

The rejected NoetherianPrimePowerSmoothDuality route has been removed completely.
It occurs in the human's route-pivot dropped list and must not be reintroduced. The
proposed finiteSmoothReductionTransport split and its node were never delivered;
their drafts are retained only in scratchpad, outside the packet. Their categorical
content is consolidated with the geometric two-level source result. The node and
report no longer claim the geometric unit equation is proved from the forbidden family.

The site realization module now uses only CartierReductionSiteComparison and the
categorical comparison construction. It drops EtaleFiniteTwistPullback,
ExceptionalCoefficientComparison, ProperProjectionFormula, the ordinary open-immersion
FiniteComparison and Defs modules, SupportComparisonPullbackCoherence,
ProEtaleExtensionZeroComparison and FixedComparisonDirectImageMate as direct proof
imports. The open/proper dependencies needed for the remaining ordinary compact-support
cocycle now belong to FiniteSmoothQuotientCoherence. This is a consolidation of one
unproved coherence conclusion, not a claim that the compact-support cocycle was proved.
Intrinsic compact-support realization is proved separately in the parent from
sfIntrinsicCompactSupportComparison.

The intrinsic remainder no longer imports constructible-origin, tensor-duality,
exceptional-finiteness or site-transport proof modules: these steps are now proved in
FiniteSmoothLevelOfOrientation. The level assembly also drops its former direct imports
of FiniteRingConstructibleDerivedOrigin, CompactSupportComparisonUnit,
FiniteSmoothGammaNormalization, RingedTopoiCanonicalTensorPullbackOfUniverses,
SupportComparisonPullbackCoherence, ProEtaleExtensionZeroComparison and
FixedComparisonDirectImageMate. The actual remaining interface prerequisites still
enter through public imports; no transitive pruning is claimed for these removals.

The parent no longer names these nodes as direct proof dependencies; their needed
content is retained in the interface or the new source results, rather than pruned
from the target closure:

- thm-amb-etale-exceptional-adjoint
- lem-amb-etale-compact-comparisons
- lem-pur-finite-reduction-constructibility
- lem-weil-pbc-extension-by-zero-stalks
- lem-weil-pbc-extension-by-zero-exact
- prop-weil-pbc-inverse-image-modules-exact
- lem-sbc-canonical-restrict-scalars-functor-comparisons
- lem-amb-proper-coproducts-projection
- lem-weil-pbc-mate-pasting
- thm-amb-vector-bundle-purity
- def-amb-vector-integration
- lem-asd-etale-finite-twist-pullback
- lem-asd-ordinary-finite-p1-adjunction
- lem-amb-affine-space-top-trace
- lem-weil-pbc-derived-single-fully-faithful
- lem-sbc-smooth-relative-dimension-permanence
- lem-pur-diagonal-regular-immersion
- lem-pur-noetherian-etale-section-specialization
- lem-pur-diagonal-orientation-compatibility
- thm-asd-smooth-tensor
- lem-weil-pbc-ringed-topoi-derived-tensor-pullback
- lem-pur-finite-smooth-gamma-normalization
- lem-weil-pbc-comparison-pullback
- lem-cbc-proetale-extension-zero-comparison
- lem-weil-pbc-comparison-direct-image-canonical-mate
- thm-weil-pbc-site-comparison
- lem-weil-pbc-finite-ring-constructible-derived-origin

## Where the brief, the DAG or earlier work was wrong

The returned delivery's unattributed-hole diagnostic was caused by the lexical
ledger scan of the `warn.sorry` option name, rather than an anonymous Lean proof.
The unnecessary command is removed; no tool or launcher file was changed.

The source sync moved the smooth exceptional base-change theorem into
WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange.
The parent imports that proved theorem directly. Its quasi-separated-base hypothesis
holds because the bases are Noetherian. The normal-cone projection and
purityNormalProjection are not definitionally equal: the construction uses
purityNormalProjection_eq. Relative-dimension base-change permanence also requires
its explicit theorem. No existing signature, definition or target statement changed,
and no module held by another group was adapted.

The first full preflight rejected the attempted Noetherian smooth-duality shortcut:
NoetherianPrimePowerSmoothDuality is in coord/route-pivot-dropped-modules.txt, under
the human's 2026-10-19 route decision. This is not stale sandbox metadata. The shortcut
was removed, and the retained two-level theorem follows the original source route.
The unpublished transport node also lacked a LeanSearch record; that draft is no
longer delivered. No launcher or route-policy file was changed.

finite_smooth_gamma_normalization and diagonalOrientationCompatibility use a single
universe lift of ZMod; this item uses a double lift. They do not apply directly.
The two remaining geometric arguments explicitly include transport along the canonical
ring equivalences while preserving root generators, tensor products and adjunction units.

The reduction_ctf field quantifies over every scheme T without an invertibility
hypothesis. finiteReduction_constructibility therefore cannot be applied directly
there. The two-level node now uses the existing intrinsic
scalarExtensionFunctor_preserves_constructible_tor theorem, which has no such
hypothesis. Identifying its constant-ring presentation with proScalar is part of the
retained transport argument. The ordinary-origin theorem still applies on X and Y.
No weakening of reduction_ctf was made.

After consolidating the two-level result, one all-files compile timed out on the parent.
Profiling the same parent completed in 13.3 seconds: elaboration 3.37 seconds, kernel
checking 1.73 seconds, and linting 5.44 seconds. No definition unfolding dominated.
The diagnostic profiling option was removed. The first preflight's repeated axiom
probe of the level module timed out. A separate probe containing only the public
theorem's print-axioms command also exceeded 60 seconds, while the module itself
compiles in a few seconds. No temporary probe commands remain in delivered code.
The axiom-probe limitation is reported for independent review; no axioms were added.

Additional direct-route checks found normalizedOriginComparisonCoherence, whose public
statement uses an adic quotient datum; its general helper is private. The coefficient
chain theorem for finiteCoefficientDirectImageMap uses a different specified map,
requiring identification with scalarMate and pasting with the open comparison. These
do not directly close the retained canonical quotient equations.

The reference metadata reset across provider-error resumptions: the retained
continuation recorded start 1792426374.1015034, while .budget records
1792429583.8738375. Earlier scratch logs precede both. This worker did not edit budget
metadata. No delivery had been pushed when the continuation began.

## New nodes

- lem-pur-finite-smooth-level-of-orientation: proved finite-level assembly from a supplied
  normalized orientation and the separate rank-zero normalization. Includes naturality,
  origin independence, trace transport and smooth Tor bounds; no new hole on this node.
- lem-pur-finite-smooth-intrinsic-level-properties: the geometric rank-zero map equation,
  including canonical coefficient-presentation transport; its trace consequence is proved.
- lem-pur-finite-smooth-two-level-reduction: the source's root-normalized coefficient
  comparison, geometric orientation compatibility, and ordinary/pro-etale counit transport.
- lem-pur-finite-smooth-quotient-coherence: the actual triple-level scalar/tensor/pullback,
  compact-support and exceptional quotient equations and their pro-etale transports.
- lem-pur-finite-smooth-site-realizations: proved prescribed finite-root realization,
  including scalar action, the comparison unit and every pro-etale restriction.

All six delivery modules compiled successfully together in import order after
pruning the unused imports. The final parent compile took 18.2 seconds. The unchanged immediate
consumer Sheaf.SmoothPurity.NormalizedWitness compiled unchanged in the sandbox's
actual Lean overlay, with no diagnostics. Its temporary unchanged mirror was removed
from the packet; no adaptation is needed. All inherited public
signatures and definitions are preserved. The repair's warning-option command
record is coord/changes/A4-finite-smooth-warning-option.md.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
