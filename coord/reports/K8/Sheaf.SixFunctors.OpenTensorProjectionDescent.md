## What changed

Constructed the inverse projection as the adjoint transpose of tensor(unit,identity)
followed by inverse restriction. Its naturality is proved directly, for arbitrary
bifunctors and an adjunction. There is no arbitrary choice of a derived map.

The item now detects invertibility on flat-term K-flat representatives, transports
it to all derived objects via resolutions, constructs gamma by inversion, and
extends the representative square to an arbitrary first complex. The extension
proves naturality of both explicit comparison isomorphisms and cancels the
localized first-variable resolution map using the ambient comparison square.

The only imported unresolved step is the chain calculation on pairs where BOTH
complexes are flat-term K-flat, in the new module
Sheaf.SixFunctors.OpenTensorProjectionMateResolving. It asserts neither existence
of gamma, nor invertibility, nor the arbitrary-first-complex formula. The item
supplies the canonical natural transformation to this lemma and proves those
remaining conclusions. Thus this is a decomposition, not a renamed existence
statement. No existing public signature, public import, definition or target changes.

## Proved and sorry left

Closed the original body of
WeilConjectures.CoefSupportOpenTensor.openTensorProjection_descent
(node lem-sf-open-tensor-projection-descent), by a complete proof from the
resolving-pair calculation. All private helpers are proved without sorry.

Added one hole:
WeilConjectures.CoefSupportOpenTensor.openTensorProjection_mate_resolving
(node lem-sf-open-tensor-projection-mate-resolving).
It is the localized chain adjunct calculation on resolving pairs. Its docstring
specifies preservation of the resolving class, the summand calculation, and
localization through the specified adjunction. Zero holes remain in the item;
one hole is added elsewhere. Net hole change: zero; this delivery is a decomposition.

Validation: lcompile.py compiled the two-module import chain in order. The item
compiled in 38.4 seconds; the sole blank-line linter warning was removed. The
original theorem signature was compared verbatim with the library source and is
unchanged. deliver3.py performs the final clean compile and axiom/sorry probe.

## No longer needed

No original imports are removed; the two public imports supply the theorem's
signature. The main proof does not use lem-sf-cochain-tensor-model-rigidity
(Sheaf.Algebra.Homology.CochainTensorModelRigidity) or
lem-sfb-ringed-tensor-comparison-extension
(Sheaf.Algebra.Homology.RingedTensorComparisonExtension). The supplied one-flat
comparisons already suffice, and constructing the canonical inverse mate avoids
two-variable descent of a separately constructed isomorphism.

The original first-step preservation arguments for F, and the exact derived
adjunction normalization, remain needed inside the resolving-pair calculation;
they are not pruned. The K-flat and flat-sheaf definitions remain needed there.
The new proof explicitly uses the K-flat resolution theorem and the proved
siteSheafTensorRightIso bridge from
lem-weil-pbc-independent-sheaf-tensor-colimits. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The unit's realized statement and step lists are
empty, and no unit route is bypassed. The old proof plan descended a separately
constructed comparison and then identified its inverse; it is enough to construct
the inverse by adjunction first and detect its invertibility on resolving pairs.

Mathlib searches: leanfinder for projection formula/exact adjunction/localization;
loogle for Adjunction.homEquiv_counit; msearch grep and local rg for projection
comparison APIs. The source-library projection theorem is specialized to
condensed-ring module categories, not the arbitrary ringed sites and supplied
models of this item. The source read is Stacks sites-cohomology.tex,
lemma-j-shriek-and-tensor (0GL1), and sites-modules.tex with the same label (0E8I).

The new statement was checked on zero complexes and the identity adjunction:
it reduces to the ordinary comparison square with the prescribed models. The
flat-term K-flat assumptions on BOTH inputs are essential to its proof, because
they permit applying restrictionModel.derived to F(C) and P. The main proof
supplies the missing extension to arbitrary C; no equality after finite
coefficient evaluations is used.

## New nodes

lem-sf-open-tensor-projection-mate-resolving states only the chain adjunct square
on flat-term K-flat pairs. Its module is
lean/Sheaf/SixFunctors/OpenTensorProjectionMateResolving.lean. The existing
item node now records the canonical-mate construction, invertibility detection,
and first-variable resolution transport actually implemented in Lean.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
