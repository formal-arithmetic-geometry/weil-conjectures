## What changed

`Sheaf.Algebra.Homology.OpenTensorScalarUnitAugmentation.augmentation_exists`
now assembles two independent constructions and proves their augmentation square
in Lean. The proof transports equality across the normalized base isomorphism,
uses the extension/restriction adjunction, tests every homogeneous total-sum
inclusion, and applies tensor induction after the sheafification adjunction.
Naturality of the extension adjunction unit computes functorial extension on an
extension-section generator. The square follows from the two unit formulas and
the comparison formula with coefficients `1,1`. The common value and localized
square are proved explicitly.

The unchanged concrete definitions are in the new publicly reexported
`OpenTensorScalarUnitData` module. A byte comparison of the complete declaration
block confirms that only the blueprint tags changed. This avoids an import cycle
between the main theorem and its two construction lemmas. The change record is
`coord/changes/W9-open-tensor-scalar-unit-data.md`.

`OpenTensorScalarUnitPairing` states only the strict coefficient transitions and
the two unit maps. `OpenTensorNormalizedComparison` states the normalized base
and coefficient isomorphisms, for any prescribed strict totals. Neither asserts
or assumes the augmentation square. Both are separate construction steps of the
original source proof, with their complete arguments recorded in their docstrings
and nodes. The main module imports them privately.

## Proved and sorry left

Closed the original hole:
`SheafOfModules.OpenTensorAugmentation.augmentation_exists`
(node `lem-sf-open-tensor-scalar-unit-augmentation`). The original module contained
one hole; it now contains zero.

Added two holes, both named public theorems in separate modules:

- `SheafOfModules.OpenTensorAugmentation.scalarUnits_exists`, node
  `lem-sf-open-tensor-scalar-unit-pairing`.
- `SheafOfModules.OpenTensorAugmentation.normalizedComparison_exists`, node
  `lem-sf-open-tensor-normalized-comparison`.

This is a decomposition: one upper hole closed, two lower holes added, a net increase
of one hole. It is not reported as a net proof. No definition contains a hole;
the relocated data module has zero holes. The private extensionality and extension
naturality helpers are proved completely.

The new statements were checked on the empty site, zero input complexes, the
identity coefficient algebra, and identity transitions: the formulas reduce to
the zero maps or the ordinary identity-coefficient construction. Their proofs use
universal properties rather than surjectivity of tensor-sheaf sections; unbounded
complexes use degreewise direct sums and the same sign in each bidegree. There is
no added flatness, boundedness or completeness hypothesis.

## No longer needed

No modules are withdrawn or globally pruned. Obsolete direct `tool_uses` entries
for `lem-pc-sites-sheaf-tensor-bilinear-universal`,
`lem-pc-sites-module-sheafification-bilinear-extension`,
`lem-weil-pbc-left-adjoint-preserves-colimits`,
`lem-sfb-localized-site-tensor-restriction`,
`lem-sf-cbc-slice-tensor-generator-coherence`, and
`lem-sf-ringed-slice-tensor-generators` are removed from the parent's approvals:
their mathematical construction work remains recorded on the new lower nodes. No original public dependency import
is removed: all are retained in the publicly reexported data module. The parent
proof now depends directly on the two construction nodes, the unchanged data node,
the localized adjunction, and tensor/total extensionality. Its former detailed
construction dependencies remain needed below the new construction nodes; this
packet makes no claim to prune them from the targets' closure.

The unit `sk-prop-sf-pf-coherence` realizes the original proposition and its open
base-change and compactification-pasting steps. None is bypassed. Unfinished DAG
parents of the assigned node remain unchanged even though there are no current
external Lean importers of this module.

## Where the brief, the DAG or earlier work was wrong

No disputed statement or source-library repair was needed. The original six-step
plan grouped two substantial constructions with the augmentation calculation.
This packet records those constructions independently and proves their combination.
The existing normalized module-level slice tensor isomorphisms do not directly
supply natural isomorphisms of the unbounded total towers, so importing that module
alone does not close either construction obligation.

## New nodes

`def-sf-open-tensor-scalar-unit-data` attaches the verbatim relocated concrete
presentation, including `StrictTotals` and `Augmentation`. It introduces no new
mathematical definition or hole. Its change record is
`coord/changes/W9-open-tensor-scalar-unit-data.md`.

`lem-sf-open-tensor-scalar-unit-pairing` records the source proof's bilinear unit
pairings, coefficient transitions, signed totalization, and compatibility with
unital transitions. It asserts no open projection formula or augmentation square.

`lem-sf-open-tensor-normalized-comparison` records normalized ordinary and
coefficient-linear slice comparisons, their totalization and strict transition
naturality. It asserts no unit maps or augmentation square. The assigned node's
proof route and proof dependencies now describe the actual Lean assembly.

## Second reading by W9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
