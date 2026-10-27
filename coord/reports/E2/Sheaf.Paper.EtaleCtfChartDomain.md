## What changed

Restored Sheaf.Paper.EtaleCtfChartDomain at its original module path and completed both
theorem bodies. Proved private helpers handle boundedness, isomorphism transport, comparison
preservation/reflection, the restricted comparison equivalence, and finite scalar preservation.
Every existing public signature, definition body and docstring is unchanged.

The ordinary chart proof applies the declared compact-support and pullback/twist Tor-window
lemmas to the declared flat constructible models. Derived braiding reconciles the twist
lemma's right-line convention with this module's left-line convention. Scalar preservation
uses exists_etaleScalarFlatModel. Pro-etale preservation reflects the Tor bound of an
etale-origin witness and transports along the specified canonical chart/scalar comparisons.

The proved native exact-monoidal Tor comparison replaces the coefficient-sized site-model
route. Bounded-below comparison supplies full faithfulness, and the etale-origin definition
plus Tor reflection supplies essential surjectivity. Updated the node's proof and direct
proof dependencies to match. Removed obsolete tool approvals without adding approvals.

Removed redundant imports and narrowed FiniteEtaleTwistLine to FiniteEtaleTateTwist, the
module defining the Tate object used here. This avoids the quarantined import chain while
preserving all mathematical definitions. Change records:
coord/changes/etale-ctf-chart-domain-imports.md and the retained, reconciled earlier record
coord/changes/E2-etale-ctf-chart-proof-imports.md.

Validation: the final item compiles without warnings (27.5-second cached result). The
seven-file consumer check also succeeds for the current source copies of the item and all
six downstream modules: AffineCounitScalar, ChartCounitScalarTransport,
OrderedCompactificationScalarSquare, EtaleAffineIntegrationCoefficientEquation,
RawChartScalarCounitPasting and SecSmoothPurity.OpenScalarInverseTransposeFactorization.
No consumer edits are needed, so these copies remain outside the delivered Lean tree.
The compile service supplied IntrinsicCtfRefinementComparison from its recorded source commit
in its private overlay; that dependency is not added to the packet. A fresh axiom probe compiled in 14.4 seconds and shows exactly propext, Classical.choice
and Quot.sound for both named theorems. deliver3.py repeats the required packet checks before pushing.

The resumed required deliver3.py invocation exhausted its 50-minute priority-slot wait
and exited 75: `DELIVERY BUSY: 6 deliveries are running on this machine; retry in a few
minutes`. It pushed nothing. This is the same capacity failure as the preceding attempts;
the complete packet is retained for retry. All proof and consumer verification above passed.

## Proved and sorry left

Closed 2 of 2 original holes:

- AlgebraicGeometry.ProEtale.AdjunctionTransfer.etaleCtfChartDomain
  (lem-sp-etale-ctf-chart-domain).
- AlgebraicGeometry.ProEtale.AdjunctionTransfer.etaleCtfChartScalarDomain
  (lem-sp-etale-ctf-chart-domain).

There are zero textual sorrys left in the item, zero added holes, and zero split-off lemmas.
A scratch copy of the final module compiled in 27.2 seconds with #print axioms for both
named theorems. Each uses exactly propext, Classical.choice and Quot.sound; neither reaches
sorryAx. The whole imported modules may still contain unrelated holes.

Edge cases: an unordered witness interval is widened using min; n=0 is covered by using
ell^(n+1) for the positive-exponent compact-support premise; zero twist, all integer shifts,
empty schemes and the zero coefficient ring are retained. Scalar extension assumes no
flatness or finite projective dimension of the target ring.

## No longer needed

Removed these private imports from the item:

- Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
- WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
- WeilConjectures.ConstructibleSheaf.OpenClosed
- Sheaf.CategoryTheory.RingedSliceExtensionTensor
- WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
- WeilConjectures.ConstructibleSheaf.KernelCokernel
- Sheaf.AlgebraicGeometry.ProperGeometricFibreCohomologicalBound
- Sheaf.AlgebraicGeometry.ProperFiniteTorAmplitude
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
- WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
- WeilConjectures.ConstructibleSheaf.Pullback
- Sheaf.AlgebraicGeometry.FlatConstructibleTensor
- Sheaf.Paper.ComparisonPullbackExact
- Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
- Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackExact
- Sheaf.AlgebraicGeometry.FiniteRootSiteComparison

The assembly no longer invokes det-pe-finite-tor-comparison-noetherian: its coefficient-model
transport is replaced by the native proved exact-monoidal Tor theorem, the ordinary comparison
full-faithfulness theorem and the actual etale-origin definition. Its redundant public import
is removed. Also removed the redundant public imports of DerivedChangeOfRingsCochainModel
and ModuleObject.Derived.BoundedConstructible, and narrowed FiniteEtaleTwistLine to
FiniteEtaleTateTwist. The flat-model, scalar-model, compact-support and pullback/twist dependencies are proof-only
imports. The public-import
change is documented in coord/changes/etale-ctf-chart-domain-imports.md; consumers are checked.

lem-sp-etale-chart-comparison-isos is not needed as an additional proof dependency: the
unchanged chartOperationComparison and chartScalarComparison already construct the specified
canonical comparisons from existing native comparison APIs. No claim is made that either
module is globally unused. The removed low-level private imports are handled inside the
stated Tor-window lemmas; their underlying mathematical results may remain transitively needed.

The node's obsolete direct tool_uses entries are removed:

- lem-pc-bounded-above-flat-kflat-site
- lem-weil-pbc-extension-by-zero-exact
- lem-fin-extension-by-zero
- lem-weil-pbc-ringed-slice-extension-tensor
- prop-weil-pbc-inverse-image-modules-exact
- thm-constructible-serre
- lem-sfb-finite-proper-geometric-cd-bound
- det-ctf-finite-proper-tor
- lem-weil-pbc-ringed-topoi-derived-tensor-pullback
- prop-constructible-pullback
- lem-asd-finite-etale-twist-line
- lem-fd-flat-constructible-tensor
- det-pe-finite-tor-comparison-noetherian
- lem-sf-comparison-pullback-exact
- lem-weil-pbc-comparison-pullback
- lem-pur-coefficient-pullback-exact
- lem-amb-finite-root-site-comparison

The finite-type-over-Noetherian approval is retained; no new approval is added.
No source-library declaration or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The DAG's suggested coefficient-model transport is unnecessary for this ordinary-module
interface: the source library already proves the stronger Tor comparison for every unbounded
object. The node lem-exc-comparison-tor-interval records another presentation of this result;
its own current proof uses that same native source comparison. The source bounded-below
full-faithfulness theorem likewise supplies exactly the restriction argument needed here.

The pullback/twist lemma's tensor factors are ordered oppositely to etaleChartOperation;
this is reconciled by a proved derived braiding, with no statement change. The quarantine/rework
row was checked before copying; the quarantined source is preserved and its complete interface
and all six declarations are restored at the original Lean module path. There is no module withdrawal or definition repair.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
