## What changed

Replaced the hole in `WeilConjectures.sfPackageCommonStageTransport` with an assembly
of the actual StageSystem constructions and the PBC descent theorem. The transported
family is the composite of an exact inverse coefficient family, the given family F,
and the target coefficient comparison. Whiskering the scalar-compatible inverse unit
gives the required mixed transformation. Descending its invertible components gives
the natural comparison of pair functors. Mathlib's `CommShift.ofComp` and
`Functor.isTriangulated_iff_comp_right` then reflect exactness through JS. The existing
representative, transformation, identity and composition lemmas prove all remaining
clauses of DescentSpec. Idempotent completeness is transferred along the actual
coefficient equivalence, while the prescribed triangulation and inclusions already
exist in GeneralAlgebraicallyClosedCoefficients.

Added `Sheaf.Paper.SfCoefficientCoherentInverse` for the inverse-family calculation
of step 2, including the finite-stage forward exactness normalization needed
to compose the target comparison. Its statement concerns just one scheme and its coefficient comparison;
it has no F, S, descended functor, DescentSpec or completeness conclusion. Its
source and full mate/coherence argument are recorded in its docstring and node.
No existing statement or definition changes. The finite exactness adapter is
included in this bridge because comparing the two large coefficient presentations
directly exhausted Lean's heartbeat budget; the bridge records the precise
finite_functor and finite_shift_normalization argument.

## Proved and sorry left

Closed the original hole in `WeilConjectures.sfPackageCommonStageTransport` by a
reduction to existing declarations and the single inverse-family sublemma.
Added one hole: `WeilConjectures.sfCoefficientCoherentInverse`
(node `lem-sf-coefficient-coherent-inverse`). Thus this is a decomposition:
one upper hole closed, one strictly smaller hole added, net zero holes closed.
The item module has zero remaining holes; the delivery has one hole in total.
Both modules compile without errors or warnings using lcompile.py --all.
The original theorem signature is verbatim unchanged; the new import passes
the import-direction check.

## No longer needed

Removed the proof import `WeilConjectures.CategoryTheory.TriangulatedEquivalenceTransfer`
and dependency `lem-pc-triangulated-equivalence-transfer`. No transported replacement
triangulation is needed: `GeneralAlgebraicallyClosedCoefficients.isTriangulated` and
`inclusion_exact` already give the literal prescribed structures. Removed that
obsolete entry from the parent node's top-level tool_uses list.

The triangle-transfer construction and explicit lifting of idempotent splittings in
the old step 1 are replaced by existing canonical instances and Mathlib's
`Idempotents.Equivalence.isIdempotentComplete`. The old representative-conjugation
construction in steps 5--6 is unnecessary: the existing `Morphism.functorCompIso`
and `descNatTrans` supply the natural isomorphism, and the existing representative
and transformation lemmas give every required formula and equation directly.
No other module or node is withdrawn. The unit's PBC descent and
idempotent-complete-triangulation results are both still used.

## Where the brief, the DAG or earlier work was wrong

The DAG's step 1 unnecessarily rebuilt the prescribed common-stage triangulation;
its definition module already exports it and exact inclusions. The required
inverse scalar family of step 2 had no separately usable declaration. It is now
isolated as an item with the full scalar-compatible inverse-unit square, including
repeated coefficient fields. The supplied equivalences, rather than scalar
extensions, are the only functors whose faithfulness is used.

Edge cases for the new statement: identity field inclusions are covered by the
same mate/tower calculation; the inverse unit is invertible on zero objects as
on all objects; no strict identity transition or faithful scalar-extension
hypothesis is imposed. Coefficient and scheme universes remain independent.

## New nodes

`lem-sf-coefficient-coherent-inverse` in
`dag/nodes/sec-six-functors/lem-sf-coefficient-coherent-inverse.json` realizes the
inverse-comparison step of the parent's source argument. LeanSearch, LeanFinder,
Loogle and source searches found generic equivalence and exactness tools but no
coherent exact inverse StageSystem family. The parent DAG proof and dependencies
now follow the Lean assembly. No change record is needed because no existing
signature or definition is changed.

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
