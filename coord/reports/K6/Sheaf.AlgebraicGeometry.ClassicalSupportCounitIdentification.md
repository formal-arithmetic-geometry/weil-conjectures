## What changed

Proved `AlgebraicGeometry.ProEtale.classicalSupportCounitIdentification` without changing
its signature, the support constructions, or the public imports. Added two private proved
helpers: full faithfulness of the termwise closed derived direct image, and distinguishedness
of the fixed support triangle transported from its injective model. The main proof uses
Mathlib's completion for the second triangle arrow, the supported-source adjunction
bijection, the two-isomorphisms theorem, reflection of isomorphisms, and adjunction naturality.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.classicalSupportCounitIdentification`
(node `lem-pur-classical-support-counit-identification`). No holes added or split off.
No textual `sorry` remains in the delivered module. The remote single-file compiler
accepted the module without errors or warnings in 17.6 seconds. A separate remote
`#print axioms` check compiled in 18.2 seconds and reported exactly `propext`,
`Classical.choice`, and `Quot.sound` for the theorem.

## No longer needed

None. The original imports and all five steps of the node's proof remain needed.
Mathlib's `complete_distinguished_triangle_morphism₁` implements the planned rotation,
completion and deshifting argument, including the signs. No module or DAG node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. Edge cases require no separate argument: the proof is
categorical and also covers the empty closed or open subscheme, zero objects, and the zero
coefficient ring. No constructibility or etale-origin hypothesis is added.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
