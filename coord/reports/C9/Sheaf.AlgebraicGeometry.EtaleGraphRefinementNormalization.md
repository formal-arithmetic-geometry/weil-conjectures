## What changed

Proved `AlgebraicGeometry.Etale.etaleGraphFromOpen_refinement` with its original
signature and public import unchanged. Added three modules for the literal proper
refinement graph, its two Cartesian neighborhood squares and transports, the
intersection transport identity, and the two projection boundary identities.
The two theorem modules are private proof imports of the item.

The proof specializes the existing unbounded compact-support formalism. Vertical
exchange pasting proves the middle identity. Horizontal pasting and proper
compositor associativity prove the first side identity. Applying the same argument
to the identity refinement proves the second side identity, using the formalism's
proved identity law. Its existing normalization theorem identifies the first side
with the specified derived refinement map. Isomorphism cancellation then proves
the item. No auxiliary object is chosen from an existence theorem.

Validation: `lcompile.py --all` compiled all four modules without warnings,
with per-file times 43.6, 34.7, 35.6 and 39.0 seconds. The original theorem
signature and public import were also checked against the shared source.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.etaleGraphFromOpen_refinement`: 1 of 1 original holes.
Added no holes. The new theorems
`AlgebraicGeometry.Etale.etaleRefinementGraphMiddleTransport` and
`AlgebraicGeometry.Etale.etaleRefinementGraphSideTransport`, their private helpers,
and every geometry lemma and definition in `EtaleRefinementGraphTransport` have
complete proofs or explicit constructions. Zero `sorry` remains in this packet;
zero statements are split off with `sorry`.

## No longer needed

No existing public import or declaration was removed, and no module is withdrawn.
The original plan's separate ringed-derived-monoidal comparison and monoidality
of derived pullback composition (`lem-sfb-ringed-derived-monoidal-comparisons`
and `lem-kun-derived-pullback-composition-monoidal`) are not needed by this
argument: it uses ordinary functor composition and exchange coherence, without
tensor products. The other original requirements are supplied by the explicit
graph geometry, the existing unbounded-formalism comparison API, or the existing
graph definitions. The proper/open exchange cube module is used only for its
proved identity-adjunction normalization helper; its bundled cube theorem is not
applied. No global removal of that module or of its dependencies is claimed.

The direct dependency list of the item now records its geometry, middle and side
lemmas and the existing graph presentation. The lower nodes record the existing
unbounded normalization and mate-pasting API actually used. No parent or unit
route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface repair was found. The existing abstract
compact-support-formalism pasting and refinement identity laws, together with
the already proved concrete unbounded comparison helpers, give a shorter proof
than rebuilding the exchange normalization from resolutions. There is no
quasi-compactness or Noetherianity assumption in the helpers used here. Identity
refinements and empty supporting opens use the same equations.

## New nodes

`def-pur-etale-refinement-graph-transport` records the explicit graph, its product
and neighborhood maps, and the specified middle and two transport isomorphisms.
All data are constructed, with no holes.

`lem-pur-etale-refinement-graph-cartesian` separately records the proved
properness, projection equations, and two Cartesian neighborhood squares.
The definition node points to these properties without creating a dependency
cycle. Both nodes attach to `EtaleRefinementGraphTransport`.

`lem-pur-etale-refinement-graph-middle-transport` records vertical exchange pasting
on the common intersection, followed by the common exterior direct image.
Its Lean theorem is proved.

`lem-pur-etale-refinement-graph-side-transport` records the two horizontal
projection boundaries and their exact refinement and identity normalization.
Its Lean theorem is proved. No existing definition or statement changed, so no
change record or consumer adaptation is needed.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
