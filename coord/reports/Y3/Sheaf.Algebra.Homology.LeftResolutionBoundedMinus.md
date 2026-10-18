## What changed

Proved `CochainComplex.exists_functorial_boundedAbove_left_resolution` in
`Sheaf.Algebra.Homology.LeftResolutionBoundedMinus`, with its signature unchanged.
Package the given datum as `LeftResolution`, use the existing source
`minusResolutionFunctor` and whiskered `minusResolutionNatTrans`, and use the existing
quasi-isomorphism instance. The essential-image witnesses are actual terms of the
C-valued resolution with identity isomorphisms. The upper-bound clause uses the source
support instance for the total and preservation of support under termwise mapping.
Updated the proof docstring and the existing DAG node's proof, proof dependencies,
and proof origin to describe this direct reuse. The unit route is unchanged; its
`realized` lists do not attach this auxiliary node to a unit step.

Validation: the assigned module compiled remotely in 2.1 seconds with no warnings.
The source construction acts on all maps of the bounded-above full subcategory and
uses upper bounds only to establish support and existence of totals. In particular,
the proof applies to the zero complex, to complexes concentrated in one degree, and
to every upper bound of a complex, without assuming a preferred bound.

## Proved and sorry left

Closed 1 of 1 original holes:
`CochainComplex.exists_functorial_boundedAbove_left_resolution`
(node `lem-sfb-left-resolution-bounded-minus`).
Added 0 holes. There are no remaining `sorry`s in the delivered Lean module and
no new modules or split-off obligations.

## No longer needed

Removed the proof import
`WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns`: the quasi-isomorphism
instance is already available through the existing resolution API, so the proof
does not invoke the comparison theorem directly. Its source implementation still
uses the comparison theorem, and its node remains a proof dependency.

The following statement-only wrappers are not needed by this proof and are removed
from this node's proof dependencies:

- `lem-sfb-left-resolution-bicomplex-total-exists`, module
  `Sheaf.Algebra.Homology.LeftResolutionBicomplexTotalExists`: the source construction
  already has the required HasTotal and support instances.
- `lem-sfb-left-resolution-totalized-augmentation`, module
  `Sheaf.Algebra.Homology.LeftResolutionTotalizedAugmentation`: the source
  `minusResolutionNatTrans` already has naturality and the component QuasiIso instance.
- `lem-sfb-left-resolution-additive-total-transport`, module
  `Sheaf.Paper.AdditiveTotalTransport`: the source `totalπ` and its quasi-isomorphism
  instance already incorporate `mapTotalIso` and its naturality.

These three wrapper modules were not explicitly imported in the original item;
none is added. This pruning is local to this proof and makes no claim that other
parents no longer need them. The objectwise-cochain, single-row-total, and
bounded-above comparison nodes remain dependencies of the source implementation.

## Where the brief, the DAG or earlier work was wrong

No statement defect. The original eight-step plan repeated constructions and
proofs already implemented in the source module imported by the item. Direct reuse
closes the hole without introducing dependencies on the three statement-only
wrappers listed above. No definitions, target signatures, or consumer interfaces
were changed.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
