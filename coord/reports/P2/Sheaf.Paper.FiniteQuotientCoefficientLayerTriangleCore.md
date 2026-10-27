## What changed

Filled `AlgebraicGeometry.Scheme.finiteQuotient_coefficient_layer_core` in
`Sheaf.Paper.FiniteQuotientCoefficientLayerTriangleCore`, preserving its statement.
Resolve the completed-coefficient object once, extend that flat-term K-flat complex to
the successor quotient, and tensor the actual kernel-unit-quotient sequence.

Proved locally that the quotient map is epi: quotient rings admit set-theoretic
sections, these give continuous lifts of discrete-valued coefficient functions,
and sheafification preserves local surjectivity. Degreewise flatness then gives
the required short exact sequence of complexes. The K-flat/single tensor comparison,
the tensor unitor, and normalized change-of-rings balancing identify its three
endpoints. The third comparison retains all localization factor isomorphisms and
uses exact scalar restriction to transport the canonical representative.

Localization comparisons abstract local functor and model values before composing.
Scalar restriction exactness is proved directly by forgetting to abelian sheaves
and reflecting finite limits and colimits. This avoids extracting instances from
the large ordinary adjunction witness, which caused a kernel-checking timeout.

Added only private proved helpers and proof imports. Updated this item's DAG proof,
proof dependencies, and proof origin to record the actual route. No shared definition,
public signature, target, or other existing module changes.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.finiteQuotient_coefficient_layer_core`
(node `lem-weil-pbc-finite-quotient-coefficient-layer-triangle-core`).
No new holes or split-off statements. No `sorry` remains in the delivered module.
The complete proof compiled in 27 seconds; its axiom check reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## No longer needed

Removed the original proof import
`Mathlib.Algebra.Homology.DerivedCategory.ShortExact`: this item constructs the
short exact sequence; its parent constructs the distinguished triangle.

The original direct proof dependency
`def-sfb-site-derived-constant-module-functor`, implemented by
`Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor`, is unnecessary:
the coefficient layer is already defined using the actual successor coefficient
sheaf, and no derived constant-module construction enters the proof.

The other original mathematical dependencies remain used. No module is withdrawn.
No claim is made that a dependency used transitively elsewhere is globally unused.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The original plan did not specify how
to compare the previous reduction with the last tensor endpoint. Resolving over
the completed coefficients first makes the existing normalized balancing map
supply that comparison. Existing proved tensor and change-of-rings APIs suffice;
no further decomposition of this obligation is needed.

The construction also covers n = 0 and zero quotient rings: surjectivity uses the
actual quotient homomorphism without a nonzero-ring hypothesis, and exactness and
the endpoint comparisons use categorical kernel, tensor, and restriction APIs.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteQuotientCoefficientLayerTriangleCore": "9890dd294b3cace476e74bf3d67b5343ef56bcb0"}, "results": {"Sheaf.Paper.FiniteQuotientCoefficientLayerTriangle": {"hash": "4e692e97fefba22a6dee62cf67c9d17815ecd73a", "status": "OK"}}, "seconds": 35, "time": "2026-10-28T04:59:05+0800", "transitive": 0, "version": 1}
```

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
