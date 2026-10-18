## What changed

Proved `AlgebraicGeometry.ProjectiveSpace.isConnectedCurve_smooth_proper_genus_zero`
in `Sheaf.AlgebraicGeometry.ProjectiveLineGenusZero`, with its exact existing signature,
universes, hypotheses and visibility unchanged. All existing public imports are preserved.
The proof-only imports now name the existing projective-line cohomology, line smoothness,
and module/source-cohomology comparison APIs.

The standard-chart work already exists for this exact base-change ProjectiveLine model in
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth`. Use its smooth-relative-
dimension-one and connectedness instances, the stated fixed-dimension theorem, and the
existing properness instance. Build IsConnectedCurve using the dimension equality and its
upper bound. This avoids constructing another chart comparison or using a separate curve
bound theorem.

Compute the recorded differential-form genus directly: relativeDifferentials is O(-2),
whose H0 vanishes by the existing monomial theorem. Separately, H1(O(0)) vanishes; transport
along unitIsoTwistZero and the existing additive module/source comparison. The latter
comparison is the existing closed node `lem-sc-module-cohomology-source-comparison`; it is
a generic cohomology-model comparison, with no replacement supplied by this item's unit.
Updated the item's DAG proof, proof_deps, and proof_origin accordingly, and removed its
obsolete affine-spectra tool approval. The unit record has no realized statement or steps
attached to this node; the geometric and monomial route is preserved.

Server single-file compilation passed in 3.2 seconds after import cleanup. An additional
single-file #print axioms check reports exactly `propext`, `Classical.choice`, and
`Quot.sound`, with no sorryAx dependency. The temporary print command is removed
from the delivered module. No definitions, signatures, or consumers
were changed, and no change record is needed.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.ProjectiveSpace.isConnectedCurve_smooth_proper_genus_zero`
(node `lem-asd-projective-line-genus-zero`).

Original holes: 1. Remaining holes in the item: 0. Holes added: 0. Split-offs: 0.
No declaration in this delivery retains sorry. This is a proof, not a decomposition.

## No longer needed

Removed proof-only imports:

- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits`: no direct TwistData
  or transition-unit argument is needed; the canonical unit/twist and differential/twist
  isomorphisms are already available through projective-line cohomology.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`: the dimension theorem and
  smooth API are supplied by the explicitly used LineSmooth import.
- `Mathlib.AlgebraicGeometry.Pullbacks`: no direct affine-spectrum pullback calculation.

Removed direct planned node dependencies `def-nagata-affine-proj`,
`lem-weil-pbc-fibre-product-affine-spectra`, and `def-sc-p1-standard`. The exact base-change
model already has the required standard-chart geometry and canonical twist isomorphisms;
this proof needs neither a new polynomial-Proj comparison nor TwistData.
Removed `lem-weil-pbc-fibre-product-affine-spectra` from the item's top-level tool_uses.
No whole module is claimed globally unreachable: the removed imports can still occur
transitively in the library's constructed chart and cohomology APIs.

The attempted new import `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Curve` was
also unnecessary and is absent: its dimension upper bound follows from the dimension
one equality already needed for IsConnectedCurve. No new node or theorem was introduced.

## Where the brief, the DAG or earlier work was wrong

The old plan requests explicit base-change/Proj chart identifications already implemented
upstream for ProjectiveLine. Reuse those constructions. The recorded genus is the global-
differential-form genus; H1 vanishing alone would require a duality comparison. The existing
monomial theorem's O(-2) canonical-sheaf clause computes that genus directly instead.
The final module-cohomology clause additionally needs the ordinary/module-cohomology
comparison, which the old proof_deps omitted; the existing closed bridge now appears there.

Read the local source labels varieties.tex lemma-projective-space-smooth and curves.tex
proposition-projective-line (the forward implications are omitted there). Existing chart
proofs and the existing monomial computations supply those omitted arguments. No source
statement or project target was changed. LeanFinder returned unrelated Weierstrass-curve
results; Loogle and the server grep search returned no match. Local library searches found
the exact APIs used above.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
