## What changed

Proved `AlgebraicGeometry.coordinate_generic_fiber_dimension_lt` with its signature and
public imports unchanged. Added the proof-only import
`WeilConjectures.AlgebraicGeometry.GenericFiber.CoordinateDimension`, whose stronger
`AlgebraicGeometry.topologicalKrullDim_fiber_genericPoint_add_one_le` is already proved.
Constructed the isomorphism from the affine line indexed by `ULift (Fin 1)` to the
one indexed by `PUnit`, identified the generic fibres using their canonical
homeomorphisms, and converted the source theorem's additive inequality into the required
strict bound. Updated the docstring and the node's proof route and dependencies.

The existing source theorem proves the same blueprint lemma using closed specializations
in a Jacobson generic fibre. This is a shorter existing proof below the unit level;
`dag/units/sk-prop-sf-cbc.json` has no realized steps bypassed by the specialization.
No statement or definition repair and no consumer adaptation was needed.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.coordinate_generic_fiber_dimension_lt`
(node `lem-fin-coordinate-generic-dimension`). Added zero holes and zero split-offs.
There are no remaining sorries in the delivered Lean module.

Remote single-file compilation passed after pruning the imports (5.2 seconds).
`#print axioms AlgebraicGeometry.coordinate_generic_fiber_dimension_lt` reported exactly
`propext`, `Classical.choice`, and `Quot.sound`; in particular the reused source proof
introduces no sorry axiom. The statement still covers empty schemes, nonreduced schemes,
non-Noetherian integral bases, and `n = 0`; `m = 0` has no possible coordinate `r`.

## No longer needed

Removed these proof-only imports:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`
- `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`
- `Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis`
- `Sheaf.AlgebraicGeometry.Morphisms.FiniteAffineTensorBaseChange`
- `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso`
- `Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg`

The localization/transcendence-degree route is unnecessary for this proof, because the
existing source theorem supplies the dimension drop directly. The following former proof
dependencies are pruned from this node's proof route (statement dependencies remain as
originally recorded):

- `def-sc-function-field`
- `def-pc-fibre-product`
- `lem-sc-integral-function-field-affine-fraction`
- `lem-weil-pbc-lft-affine-pairs`
- `lem-sbc-finite-affine-tensor-base-change`
- `lem-weil-pbc-fibre-ring-localization-quotient`
- `def-weil-pbc-finite-type-algebra`
- `lem-weil-pbc-open-fibre-product`
- `lem-weil-pbc-localization-prime-residue-field-iso`
- `lem-sc-closed-irreducible-dimension-trdeg`
- `def-weil-affine-spectrum`
- `lem-sbc-transcendence-degree-tower`
- `def-kun-transcendence-degree`

In particular this item no longer needs the proof modules
`Sheaf.AlgebraicGeometry.Morphisms.FiniteAffineTensorBaseChange`,
`Sheaf.RingTheory.LocalizationPrimeResidueFieldIso`, and
`Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg`.
Removed the two obsolete tool approvals for the tensor base-change and localization
residue-field nodes. These modules may still have other consumers; this delivery claims
only that this proof does not require them.

## Where the brief, the DAG or earlier work was wrong

The planned six-step localization argument missed a fully proved stronger theorem already
in `WeilConjectures.AlgebraicGeometry.GenericFiber.CoordinateDimension`. Its docstring
explicitly names the same blueprint lemma, and its hypothesis is only local finite type
over the integral base. The required singleton reindexing and strict-inequality conversion
are sufficient to reuse it. No mathematical error in the assigned statement was found.

Searches actually run: leanfinder for generic-fibre dimension decrease, loogle for
`WithBot, _ + 1 ≤ _, _ < _`, the msearch grep for
`topologicalKrullDim_fiber_genericPoint_add_one_le`, and direct ripgrep searches of both
library roots. Loogle's returned module path belonged to a newer Mathlib layout; the
pinned declaration is in `Mathlib.Data.ENat.Basic` and was already available. The direct
source search found the stronger theorem. The import-direction check returned yes.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
