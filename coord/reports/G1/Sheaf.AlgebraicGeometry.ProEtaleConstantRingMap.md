## What changed

Proved all five existing theorems in
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`, preserving every existing statement,
definition, visibility and docstring. Naturality is proved from the fibre-product projection
identity and sheafification naturality. The constant-sheaf comparison follows from the
already stated locally bijective scalar map. Three proved private helpers record the
comparison unit, its inverse-image square for arbitrary rings, and invertibility of the
canonical constant-ring inverse-image map. The last helper specializes uniqueness of left
adjoints to the constant-sheaf and inverse-image adjunctions, adapting the existing private
calculation in `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage` from commutative
rings to rings. The empty-source assertion follows from terminal sections on empty objects.

Added proof-only imports of `Mathlib.CategoryTheory.Sites.LocallyBijective`,
`WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale`. Updated the existing node's
proof, proof dependencies and proof origin to describe this route. No new public interface,
definition repair, adapted consumer, or new node is needed.

## Proved and sorry left

Closed five original holes, all attached to
`prop-weil-pbc-proetale-constant-ring-map`:

- `AlgebraicGeometry.ProEtale.finiteCoefficientDirectImageApp_naturality`.
- `AlgebraicGeometry.ProEtale.finiteCoefficientConstantComparison_isIso`.
- `AlgebraicGeometry.ProEtale.finiteCoefficientInverseImageMap_isIso`.
- `AlgebraicGeometry.ProEtale.finiteCoefficientInverseImageMap_constant`.
- `AlgebraicGeometry.ProEtale.finiteCoefficientInverseImageMap_empty`.

Zero holes remain in the delivered module; zero holes added; zero split-offs. The constant
comparison and the main isomorphism use the existing statement
`AlgebraicGeometry.ProEtale.finiteCoefficientScalarMap_locallyBijective` from
`def-weil-pbc-proetale-modules`, whose proof remains an upstream obligation. Thus this is a
proof from the declared dependencies, not a claim that the transitive axiom closure is
already free of `sorryAx`. Single-file remote compilation passed without warnings (12.1 seconds).
`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for
naturality, the constant-map square specialization, and the empty-source theorem.
The comparison-isomorphism and main isomorphism also report `sorryAx`, from the existing
upstream local-bijectivity obligation just identified. Temporary axiom-print commands
were removed before delivery.

## No longer needed

Removed the proof-only import
`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization` and removed
`lem-weil-proetale-weakly-etale-localization` from this node's direct proof dependencies.
Its open-fibre work is already encapsulated by
`finiteCoefficientScalarMap_locallyBijective`; repeating localization here is unnecessary.
No other declared proof dependency was pruned, and no unit statement or realized unit step
was bypassed. This removes the direct import edge only; it does not assert the localization
module is globally unreachable from all targets. All existing public imports are retained
as the statement/definition interface.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original proof plan repeated the open-fibre gluing
argument despite an applicable local-bijectivity theorem already being declared in the
coefficient module. The supplied dependency API is sufficient: no new intermediate
obligation or definition change is needed. The proof includes empty schemes, the zero
ring and finite noncommutative rings with the original hypotheses unchanged.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
