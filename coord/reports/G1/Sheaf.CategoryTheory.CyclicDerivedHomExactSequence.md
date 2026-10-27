## What changed

Reduced `cyclicDerivedHom_exact_functorial` to two separate comparison calculations:
`cyclicDerivedHomTransport_exact_action` and
`cyclicDerivedOffDiagonalPresentation_mapExact`. Both are new modules imported privately
by the item. All four original public theorem signatures and public imports are unchanged.

The assembly proves additivity directly from the additive underlying derived functor and
bilinear composition. It proves the forgetting square from naturality of the specified
comparison and the coherent zero-shift equation. For the connecting square, take the
existing strict presentation of the raw off-diagonal boundary. Normalization and naturality
compute the source boundary on that presentation. The presentation-transport lemma supplies
a target presentation, and the same normalization calculation computes its boundary.
The action-transport lemma supplies the remaining clause of the functoriality predicate.

The new statements are strictly parts of the argument: one is only the conjugation
calculation, and the other concerns strict extension presentations, without referring to
a boundary family or its exactness. Neither asserts the parent's entire conclusion.
The two comparison calculations are documented with their precise endpoint and shift
factors. The DAG records the implemented assembly and keeps the plans for the two
unchanged companion holes.

## Proved and sorry left

Original item holes: 3. Closed/reduced in the item: 1,
`CategoryTheory.Endofunctor.IsoAlgebra.cyclicDerivedHom_exact_functorial`.
Added holes: 2. This is a decomposition, not a net proof gain: three original holes
become two original holes and two strictly smaller comparison obligations.

Every remaining hole in this delivery, in namespace
`CategoryTheory.Endofunctor.IsoAlgebra`:

- `cyclicDerivedHom_rightDerived_functorial`, unchanged, node
  `lem-sf-cyclic-derived-hom-exact-sequence`.
- `cyclicDerivedHom_finite_composite_functorial`, unchanged, same node.
- `cyclicDerivedHomTransport_exact_action`, new, node
  `lem-sf-cyclic-derived-exact-action`.
- `cyclicDerivedOffDiagonalPresentation_mapExact`, new, node
  `lem-sf-cyclic-derived-exact-presentation`.

The previously proved `exists_cyclicDerivedHomBoundary` is unchanged. Its dependencies'
existing holes are used as declared premises, as required by stage 3. There are no
new definitions, axioms, or private theorem holes. All three delivered Lean modules
compile cleanly together through `lcompile.py --all` (no errors or warnings).

## No longer needed

No existing import, node, or module is globally pruned. No module is withdrawn.
The exact case no longer needs bounded-below injective representatives, termwise
injectivity, the cone-kernel acyclicity calculation, or the right-derived shift theorem:
exactness maps every short exact presentation directly, and Mathlib already supplies
`DerivedCategory.map_triangleOfSESδ` with its canonical sign. These arguments remain
in the plans for the unchanged right-derived and finite-composite companions, so their
parent dependencies are retained.

The implementation uses the existing raw-presentation API rather than introducing another
boundary construction or choosing extension witnesses in a definition. Experimental
proof-only imports were removed before delivery; the retained proof imports all supply
named declarations used by the item.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The exact-functor plan is longer than necessary: strict
presentations are already available without cohomological bounds, and exact functors
preserve arbitrary short exact sequences. The shortened exact route therefore needs
no additional injective or boundedness hypotheses. The remaining difficulty is the
explicit comparison with the specified localization factors and shifts, separated into
the two new statements.

Edge checks: for the zero functor both transport statements give zero; for the identity
functor they give the original conjugation and presentation up to canonical localization
factors. For identity action on abelian groups the strict unipotent extension retains its
canonical nonzero cyclic extension class; nothing assumes that derived forgetting is
faithful. The new presentation statement is conditional on an actual presentation and
therefore does not assume existence outside the Grothendieck setting. Independent
localization universes are retained.

Searches used LeanFinder, Loogle, LeanSearch, Mathlib source grep, and searches of both
library roots and the blueprint. Mathlib's general Ext maps and canonical SES-boundary
map are relevant, but do not directly state either fixed-pair comparison. The blueprint
has no off-diagonal-presentation node; its exceptional-adjunction sentence is the anchor
for the parent's explicitly agent-written expansion. The blueprint ancestor tool reports
no resolved ancestor for this inherited chain; the new records preserve that chain and
identify the exact blueprint sentence.

## New nodes

`lem-sf-cyclic-derived-exact-action`, module
`Sheaf.CategoryTheory.CyclicDerivedExactAction`: exact transport commutes with the degree-r
conjugation action for every integer r. Its proof plan specifies the derived structure
square, the comparison beta, the shift equation, and the two endpoint cancellations.

`lem-sf-cyclic-derived-exact-presentation`, module
`Sheaf.CategoryTheory.CyclicDerivedExactPresentation`: exact transport preserves a strict
off-diagonal presentation with both its prescribed underlying class and native boundary.
Its plan maps the short exact sequence and splitting, applies naturality of e to the
matrix equation, specifies both endpoint isomorphisms, and uses Mathlib's signed
SES-boundary formula. No change record is needed: existing interfaces are unchanged.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
