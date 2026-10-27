## What changed

Reduced `WeilConjectures.SfStrictDirectImageScalar.strictDirectImageScalarComparison`
without changing its signature. The proof assembles a family of strict integral models,
normalized integral comparisons, and the explicitly constructed raw rational functors.

Moved the existing 16 interface declarations, byte-for-byte with their docstrings,
into `Sheaf.Paper.SfStrictDirectImageScalarData` and publicly re-exported them from the
original module. Existing public imports remain unchanged. Added integral associator
and coherence predicates in `SfStrictDirectImageScalarCoherence`; these express the
original Steps 4--7 and are extra hypotheses only of the lower rational descent lemma.

`rationalImage` is a real construction: `ScalarLocalization.transport` of the integral
linear image. Its object map, additive structure, and every pure-tensor map are fixed
without an existence choice. `strictDirectImageRationalComparisons` states the remaining rational descent step
with equality to this fixed functor, including the literal object and tensor formulas. `strictDirectImageScalarComparison`
combines the three stages using existential elimination. The local Classical.choice
is inside a theorem proof, not an exposed definition of unspecified data.

Change record: `coord/changes/sf-strict-scalar-shared-interface.md`.
The interface and all three lower statements were checked by single-file Lean compiles;
the final seven-module packet compiled across the complete-set and final changed-module checks. The original assembly and three
direct consumers compiled. The unchanged SfPackageFieldOperationRealization consumer
reached the fixed compile limit; no consumer interface adaptation was needed in the
three successful consumer checks.

## Proved and sorry left

This is a decomposition, not a net completed proof. Closed the one original textual hole
in `WeilConjectures.SfStrictDirectImageScalar.strictDirectImageScalarComparison` by a
complete assembly proof. Added three strictly smaller public obligations:

- `WeilConjectures.SfStrictDirectImageScalar.strictDirectImageIntegralModel`
  (`lem-sf-strict-direct-image-integral-models`): one coefficient field only; constructs
  the strict realization, normalized reconstruction, scalar linearity and shift.
- `WeilConjectures.SfStrictDirectImageScalar.strictDirectImageIntegralComparisons`
  (`lem-sf-strict-direct-image-integral-comparisons`): supplied strict models; constructs
  only the ambient/integral scalar comparisons and proves their integral laws.
- `WeilConjectures.SfStrictDirectImageScalar.strictDirectImageRationalComparisons`
  (`lem-sf-strict-direct-image-rational-comparisons`): supplied coherent integral data;
  constructs rational comparison isomorphisms and proves the object, tensor, shift,
  unit and cocycle equations on the fixed tensor-Hom rational functor.

Those are every sorry left in this packet. Each is exactly the whole proof of a named
public theorem in its own module, with source, proof in words, and matching DAG node.
`rationalImage` and `rationalImageAdditive` contain no holes. The original module contains
zero holes; the packet has three, replacing one (net -2 holes closed).

## No longer needed

Removed these original proof-only imports from the assembly module:

- `Mathlib.RingTheory.FiniteType`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`
- `Sheaf.Paper.SbcCompletedOperations`
- `Sheaf.Paper.ScalarCompletionAssociator`
- `Sheaf.Paper.CompletedLineTensorCoherence`
- `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison`
- `Sheaf.Paper.CompletionUnitStrictQuotientModel`
- `Sheaf.Algebra.Homology.RoosCommShift`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
- `Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence`
- `Sheaf.Paper.CompletedScalarChainShift`
- `Mathlib.CategoryTheory.Shift.CommShift`
- `Sheaf.CategoryTheory.SemilinearScalarLocalization`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`

They were prospective imports for the old monolithic proof. The three unproved
construction/coherence statements import only what their signatures need. The
normalized data module retains the original public imports, so all original consumers
see the same declarations. No existing module is withdrawn, and no existing dependency
is claimed globally pruned: the old proof dependencies are redistributed to the three
lower proof plans. The original node's 16 direct tool approvals are removed from its
`tool_uses` because its direct proof now uses the new model/comparison/descent route;
the original tools remain cited where actually required in the lower plans.

## Where the brief, the DAG or earlier work was wrong

The published Lean interfaces for individual geometric/completion comparisons do not
already provide the functorial strict models or the fully normalized comparison family
required by this item's existential. In particular the integral shift/cocycle equations
must be retained before applying rational scalar descent; HasIntegralLaws alone records
only normalization and unit, so the lower descent statement also assumes the explicitly
spelled-out HasIntegralCoherence. The target itself is unchanged.

The current `literature/blueprint/latest/` version of the cited all-stages proof contains
the underlying full-faithfulness/unit argument only, without the older rational and
algebraically closed paragraphs named by the inherited node. The new nodes identify
these as agent expansions of the inherited eight-step argument instead of pretending
the current source contains those paragraphs. No unit or chapter route changes.

Checked the new statements on repeated fields (unit transports are retained), on a
triple of identity inclusions (integral associator still includes the actual equality
transport), on zero objects/maps and empty schemes (no nonempty or dimension hypothesis
is added), and with independent scheme/closure universes. The rational descent statement
has no geometry assumptions because all needed integral data and laws are supplied.
No arbitrary object is selected by a public definition.

## New nodes

- `def-sf-strict-direct-image-scalar-data`: the moved existing scalar-comparison interfaces.
- `def-sf-strict-direct-image-integral-coherence`: integral associator and shift/cocycle law.
- `lem-sf-strict-direct-image-integral-models`: original Steps 1, 2 and 6 at a single field.
- `lem-sf-strict-direct-image-integral-comparisons`: original Steps 3--5 and 7 for supplied models.
- `def-sf-strict-direct-image-rational-data`: explicitly constructed rational functor.
- `lem-sf-strict-direct-image-rational-comparisons`: original Step 8, with equality to
  the fixed rational functor, used by the original theorem.

All nodes are in `dag/nodes/sec-smooth-purity/`. Searches were actually run using
msearch (LeanSearch, LeanFinder/Loogle and grep); generic shift and tensor tools were
found, but none constructs these normalized strict models or their entire scalar
coherence. Existing related nodes and the full current blueprint were also searched.

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
