## What changed

Filled `AlgebraicGeometry.Scheme.completedContinuousHomHypotheses` without changing any
existing public signature or definition. Added proved private helpers for scalar projections,
constant-section normalization, faithful restriction, and preservation/reflection of bounds.
The actual restriction functor and canonical shift comparison are retained.
The supplementary nodes `lem-pbc-scalar-coefficient-equivalence` and
`lem-weil-pbc-uniform-complete-triangulated` are used as general coefficient and
subcategory tools, respectively; they do not replace a unit proof step.

The proof uses the scalar-coefficient equivalence directly. Integral membership follows
from the specified round-trip isomorphism and invariance of the full completion predicate.
The Hom-sums theorem in completed coefficients is transported through the explicitly
normalized linear Hom equivalences and their generator square.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.completedContinuousHomHypotheses`
(node `lem-per-completed-continuous-hom-hypotheses`). No holes added; no `sorry` remains
in the delivery. Remote compilation and delivery validation are pending.

## No longer needed

Removed private import `Sheaf.Algebra.Homology.NormalizedRingIsoDerivedTransport` and
proof dependency `lem-pur-ring-iso-derived-transport`: exact restriction and its inverse
suffice; the monoidal and braided transport comparisons are unused. Removed the obsolete
tool approval from this node. No module or declaration is withdrawn.

The Hom-sums theorem is needed only in completed coefficients. No extra continuous
compactness or local-model transport is required. The existing characterization and
Hom-sums dependencies remain used. No unit statement or route changes.

## Where the brief, the DAG or earlier work was wrong

The original plan invokes a stronger monoidal transport theorem than needed and reapplies
Hom continuity in continuous coefficients, although the existing Hom-sums theorem already
gives the completed comparison. The shorter proof transports that comparison. Integral
membership is stated in round-trip coordinates, where invariance under the round-trip
isomorphism directly preserves all etale-origin witnesses. The old quarantine row was
checked; the currently present item source and its Lean attachment are preserved.

LeanFinder for exact derived equivalences, bounds, and shifted Hom coproducts returned
generic derived shift/support declarations. Loogle for `Functor.mapLinearEquiv` returned
no match. Repository searches found `derivedRestrictIso_isEquivalence`, exact-functor
cohomology, `Linear.homCongr`, and `DirectSum.lmap`; the proof combines these APIs.

Source read: Bhatt--Scholze, Section 6.8, especially Lemma 6.8.2(1),
Proposition 6.8.11(3), and Lemma 6.8.12. Edge cases checked: empty X, zero K,
empty/singleton index sets, torsion cohomology, and positive/negative integer shifts.

## Second reading by T9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
