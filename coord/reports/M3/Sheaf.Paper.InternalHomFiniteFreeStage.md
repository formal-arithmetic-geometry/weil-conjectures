## What changed

Completed `Sheaf.Paper.InternalHomFiniteFreeStage`, with the existing public
statement and representative definitions unchanged. All supporting declarations
are private and proved in the same module.

The denominator uses the natural identification of finite-free tensoring with a
finite power of the identity, hence exactness, followed by quasi-isomorphism
invariance of the chosen derived-Hom representative. The numerator first checks
the normalization at the unit using the section formula for the tensor-unit
isomorphism. Additivity gives the required finite-product cones; K-injectivity
and the natural augmentation transport these cones to the resolved Hom functor
after taking homology. Naturality then proves the finite-free comparison.
Empty finite products include rank zero. Complexes remain unbounded.

Proof-only imports supply the independent-coefficient tensor API, Hom
quasi-isomorphism invariance, single-complex tensor comparison, additivity,
finite products of functors, and products of K-injectives. The node's proof and
proof origin describe the implemented argument. No other module is adapted.

Change record: `coord/changes/m3-internal-hom-finite-free-proof-context.md` documents
the local proof context commands and all three downstream consumers, as requested
by server preflight class (d). The public interface remains unchanged.

Validation: the final module compiled without warnings through `lcompile.py`
in 43.1 seconds. Its public theorem signature matches the original verbatim.
No new axiom or hole inside a definition is introduced.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.SfbHomFilteredColimit.internalHom_finiteFree_stage`
(node `lem-sfb-internal-hom-finite-free-stage`).

Holes closed: 1. Holes added: 0. Holes left in the delivered module: 0.
Split-off statements: 0. Imported stated dependencies are retained, including
`comparison_existsUnique`; their proofs are outside this assignment.

## No longer needed

Removed the redundant trial import
`Mathlib.CategoryTheory.Preadditive.Biproducts`; it is already supplied by the
monoidal preadditive API. No declared dependency, node, or module is pruned. The argument uses every
recorded proof dependency and keeps the blueprint unit's route. The original
public data import is retained.

## Where the brief, the DAG or earlier work was wrong

No statement or definition repair was necessary. The proof does not assume the
chosen functorial K-injective replacement is additive. Instead its augmentation
transports finite-product cones after homology, where its relevant components
are isomorphisms. This makes the finite-sum argument in the plan precise.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
