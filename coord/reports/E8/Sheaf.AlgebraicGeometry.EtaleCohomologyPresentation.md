## What changed

Replaced the two original `sorry` proofs in `Sheaf.AlgebraicGeometry.EtaleCohomologyPresentation`.
`sheafHToDerived_add` follows from the additive Ext representation, derived functors,
composition, and evaluation. `sheafHToDerived_bijective` factors the specified map through
the derived constant-sheaf/global-sections adjunction, the projective-single Hom equivalence
for `ULift ℤ`, evaluation at `1`, and the canonical shift and single-object isomorphisms.
Two proved private lemmas identify the derived adjunction unit on singles and its zeroth
homology. They use the existing `rightDerivedSingleUnit_zero` normalization, so the explicit
evaluation definition and its canonical comparisons are unchanged. A third proved private
helper carries out the bijection for an abstract exact adjunction, so Lean does not repeatedly
unfold the concrete sheaf-category instances when checking the composition.

Added five private proof imports for these existing constructions and instances. Updated
`def-weil-pbc-etale-cohomology-presentation` to record this proof and its dependencies.
All existing public declarations, signatures, definitions, and public imports are unchanged.

## Proved and sorry left

Closed two original holes:

- `AlgebraicGeometry.Etale.sheafHToDerived_add`.
- `AlgebraicGeometry.Etale.sheafHToDerived_bijective`.

No holes added or split off. No `sorry` remains in the item module. The canonical additive
equivalence `AlgebraicGeometry.Etale.sheafHDerivedEquiv` consequently uses proved additivity
and bijectivity of its original explicit forward map.

## No longer needed

None. No existing import, node, or module was removed. All five new proof imports supply
constructions or instances used in the proof. The injective-resolution argument from the
original docstring is realized through the already proved derived adjunction and projective
single APIs rather than duplicating resolution-level cohomology computations. The unit's
fixed route and realized nodes are unchanged.

## Where the brief, the DAG or earlier work was wrong

The item node had empty `proof` and `proof_deps` despite carrying two proof obligations.
The delivery supplies the actual proof steps. Neither statement required correction.
The proof requires no nonempty-scheme assumption, no positive-degree restriction, and no
choice from a mere existence theorem. The empty scheme and degree zero are covered by the
same categorical equivalences.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
