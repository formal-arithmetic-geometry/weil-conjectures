## What changed

Replaced the `general_admissibility` hole by a complete assembly from bounds on one selected
chart. The exact public theorem signature and all public imports are unchanged. Private lemmas
prove interval conversion, the two maximum inequalities, Tor interval enlargement, zero detection
on an open cover, and descent of every intrinsic K-flat tensor test. The target proof first glues
cohomological intervals, then establishes the requested Tor interval, and obtains bounded
constructibility by applying the cohomological result to any interval containing the input support.

Added `Sheaf.Paper.PurityChartLocalBounds` for the still unfinished calculation on one chart.
Added `Sheaf.Paper.PurityOpenTensorTestVanishing`, proved from the existing intrinsic coefficient
realization, intrinsic Tor transport and resolution tensor comparison, the unit-normalized pullback
model, and the proved source exact monoidal pullback/tensor comparison.

Validation: all three sandbox modules compiled in import order with lcompile.py --all, exit 0,
with no diagnostics (41.5 s, 56.1 s, 46.7 s). No axiom or definition hole was introduced. The
new statements were checked on the empty source, zero input, d=0, c=0, and arbitrary non-etale-origin
test modules. The chart statement needs no descent and no uniform maximum. The tensor-test
statement needs no exceptional inverse image or constructibility. Searches found no matching
Mathlib shortcut. Read the current blueprint Step 1--4 and the corresponding unit route; the
smooth-then-closed chart calculation followed by finite open descent is retained.

## Proved and sorry left

Closed the original hole in `WeilConjectures.PurityFiniteSetting.general_admissibility` (node
`thm-pur-general-admissibility`) by a compiling proof from the named chart-local statement.
Proved `WeilConjectures.purityOpenTensorTestVanishing` (node
`lem-pur-open-tensor-test-vanishing`) and every private helper in the delivery.

One new hole remains: `WeilConjectures.PurityFiniteSetting.chart_local_bounds` in
`Sheaf.Paper.PurityChartLocalBounds` (node `lem-pur-chart-local-bounds`). Its entire proof is
`:= by sorry`, and its docstring and node give the source and full argument. This is a
one-for-one decomposition, not a net hole closure: 1 original hole closed, 1 new hole added,
0 holes in the item module, 1 hole in the packet. The remaining work is the witnessed
chart comparison, smooth projection and closed-support assembly in intrinsic coordinates.
The existing chart identification and closed transport declarations have been read; their
witness-retaining interfaces do not directly yield this instantiated intrinsic conclusion.
No arbitrary data is selected from an unproved mere existence statement in a definition.

## No longer needed

The following old private imports are removed from the item module:

- `Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint`
- `Sheaf.AlgebraicGeometry.EtaleClosedSupportAmplitude`
- `WeilConjectures.Compactification.NagataCompactification`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.Paper.EtaleOriginDerivedCategory`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.AlgebraicGeometry.EtaleClosedSupportTorAmplitude`
- `Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals`
- `Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction`
- `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.Paper.ComparisonTorAmplitude`
- `Sheaf.Paper.DerivedPullbackTensorIso`
- `Sheaf.Paper.ExplicitExceptionalPreservation`
- `Sheaf.Paper.FiniteTorAmplitudeSites`
- `Sheaf.Paper.SmoothExceptionalPreservation`

Their mathematical uses in the local chart calculation are retained in the new chart node's
proof dependencies, rather than duplicated in the global assembly. No source-library declaration
or module is withdrawn. No entire module is claimed to be globally unreachable.

The parent no longer directly uses `lem-pur-affine-chart-exceptional-identification`,
`prop-exc-open-adjoint`, `thm-exc-explicit-preservation`, `sbc-lem-affine-space-smooth`,
`cor-pur-smooth-admissibility`, or `lem-pur-closed-etale-transport-bounds`: the new chart-local
node retains all six. The original parent dependency `lem-sfb-tor-interval-local-detection`
is unnecessary for this proof. Its signature uses inverse-image ring sheaves and the
independent-coefficient derived tensor, whereas the target uses the constant-ring
K-flat resolution predicate. The proved single-test comparison and cover-zero detection
supply exactly the required descent without assuming their predicates definitionally equal.
`Sheaf.AlgebraicGeometry.ProEtaleTorIntervalLocalDetection` is not imported. The larger
all-coefficient theorem `derivedPullbackTensorIso` is not imported either: its finite
exact fixed-scalar source comparison suffices here. None of these are deletion requests.

## Where the brief, the DAG or earlier work was wrong

The existing theorem docstring still refers to a nine-step proof, while the current node
had four steps. The new node proof records the actual Lean assembly, following the current
blueprint Steps 1--4 without changing the theorem statement or the unit route. The existing
Tor-local-detection declaration cannot be applied directly to the target's tensor presentation;
the new proved tensor-test lemma supplies this comparison explicitly, for arbitrary sheaves.

The interrupted draft had omitted the private monoidal pullback import. The first set compile
reported missing `F.Monoidal`; adding the existing source monoidal instance module repaired it.
A single-file compile of the parent before the new siblings were compiled reported their absent
object file; the complete import-ordered set compile succeeded. There is no tool failure.

Tool use: the new proved tensor-test node specializes the existing finite exact pullback/tensor
computation and intrinsic Tor transport; the parent uses the proved source open-cover zero test.
These are generic tools, with no change to the unit's smooth-then-closed proof route. Existing
maintainer tool-use approvals are preserved; no new approvals are manufactured.

## New nodes

`lem-pur-chart-local-bounds` records the single selected chart calculation, with its two
independent input clauses and the local interval [a-2d,b-2d+c+1]. It has no maxima or descent
conclusion. It retains the existing open, smooth, closed and witnessed chart dependencies.
Its Lean module compiles with exactly one named theorem hole.

`lem-pur-open-tensor-test-vanishing` records a proved comparison for one global resolution,
one arbitrary module sheaf and one outside degree after a single open restriction. Its
Lean proof transports to fixed scalars, applies the local Tor bound, and conjugates the
existing derived tensor and homology comparisons. It contains no hole.

The parent node now records the actual maximum arithmetic, cohomological descent,
single-test Tor descent and bounded-support argument. No signatures or definitions changed,
so there is no change record and no forced adaptation.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
