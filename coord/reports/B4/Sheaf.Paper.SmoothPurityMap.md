## What changed

Filled the three theorem proofs in `Sheaf.Paper.SmoothPurityMap`. Added proved private
helpers for ordinary tensor-mate naturality, generic bifunctor and isomorphism comparison calculations,
derived comparison tensor naturality,
and compatibility of the pullback, tensor-source and theta comparisons with a map of
etale presentations. The final existence/uniqueness proof uses a bounded etale
representative and the existing comparison Hom bijection. Added private proof imports
of `WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence` and
`Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`. Existing public signatures,
definition bodies, public imports and canonical maps are unchanged. Updated the node
proof to record this route. The final single-file server compile completed cleanly
in 44.9 seconds. The constructible-derived-origin theorem is used as a
tool from the comparison unit: the purity unit supplies the explicit composite but
no etale-origin witness for an arbitrary intrinsic bounded constructible object.
The existing fixed-module Hom-bijection node records the second comparison tool.

## Proved and sorry left

Closed all three original holes, all attached to `def-pur-smooth-purity-map`:

- `WeilConjectures.PurityFiniteSetting.smoothPurityTensorPresentation`.
- `WeilConjectures.PurityFiniteSetting.existsUnique_smoothPurityTensorShift`.
- `WeilConjectures.PurityFiniteSetting.existsUnique_smoothPurityTensorMap`.

Holes added: zero. Holes left in the item: zero. Imported declarations retain their
existing proofs and any transitive holes; none is changed by this delivery.

## No longer needed

No public import, module or declaration is withdrawn. The node previously had no
proof dependencies or proof steps, so none is removed. The larger compactification
and witness-independence theorem `tensorMap_presentation_independent`
(`lem-pur-tensor-map-presentation-independent`, module
`Sheaf.Paper.TensorMapPresentationIndependent`) is not needed for this proof:
ordinary naturality plus the existing bounded-below comparison Hom bijection
already identifies every presentation. No global pruning of that independently
used module is claimed. The cohomological-smoothness isomorphism theorem is not
needed to construct this map; the existing tensor-mate definition is retained.

## Where the brief, the DAG or earlier work was wrong

The assigned definition node had no proof steps despite its three theorem holes.
Its proof now records the actual argument. The shift identity is reflexive, as its
existing docstring claims. The final theorem can use any fixed bounded etale
representative: existence of the representative and equality for every presentation
make the resulting morphism unique, without choosing any arbitrary map data.
The unit route and the specified diagonal orientation, tensor mate and shift
comparison are preserved.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
