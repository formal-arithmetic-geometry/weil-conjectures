## What changed

Completed both theorems in `Sheaf.CategoryTheory.GeometricConstantLeftScalarExtension`.
All existing public definitions, signatures, and public imports are unchanged. The added
constructions and lemmas are private, and every one is proved.

For `geometric_constant_left_scalar_extension`, construct the sheaf scalar-extension
adjunction from the sectionwise arbitrary-ring adjunction and module sheafification.
Recover the underlying geometric hom bijection and counit from the lift's normalized
unit. Taking adjuncts of counit scalar-linearity identifies the direct-image scalar
endomorphisms. This produces a natural module isomorphism between the two scalar-restricted
direct images, using the identity comparison on their underlying set sheaves. Uniqueness
of left adjoints then constructs the geometric scalar-extension isomorphism. Its unit
identity proves the equation at `1` tensor a section; scalar compatibility and linearity
prove the required equation at every scalar. The section maps in the existential are
constructed from the scalar-adjunction unit, with their sectionwise formulas proved.

For `constant_left_scalar_extension`, first compare sheafification of presheaf scalar
extension with extension after sheafification by uniqueness of left adjoints. Whisker
with the constant-presheaf functor. The adjunction-unit equation gives the constant
pure-tensor formula at `1`, and linearity gives it for every scalar.

The proof follows all six steps of the existing node. Mathlib's `Adjunction.leftAdjointUniq`
implements the representing-isomorphism argument of its co-Yoneda steps. No unit route
is bypassed, and the existing node's mathematical proof and dependencies still apply.
Read the current blueprint unit and Stacks `sites-modules.tex`,
`lemma-adjointness-tensor-restrict` (03CZ), together with the normalized lift interface.
Searches via LeanFinder, Loogle, and grep found the needed adjunction APIs; the site-functor
pullback comparison does not directly cover an arbitrary given geometric morphism.

## Proved and sorry left

Closed both original holes:

- `CategoryTheory.geometric_constant_left_scalar_extension`.
- `CategoryTheory.constant_left_scalar_extension`.

Original holes: 2. Holes closed: 2. Holes added: 0. Holes remaining in the item: 0.
Split-off theorems: 0. Both declarations realize
`lem-sfb-geometric-constant-left-scalar-extension`.

The arguments use only universal properties and the given normalized lifts. They impose
no commutativity, flatness, finiteness, nontriviality, or terminal-object assumption;
in particular zero rings/modules, identity ring maps, nonflat quotients, and empty sites
require no separate exclusion or choice of a section.

## No longer needed

Removed the private proof import `Mathlib.CategoryTheory.Yoneda`; the proof uses the
adjunction uniqueness API directly. No mathematical node or project module is pruned:
all stated dependencies remain relevant to the existing proof route or statement.

## Where the brief, the DAG or earlier work was wrong

No statement or definition repair was needed. The sandbox contained earlier proof work;
its constant comparison and scalar-adjunction constructions were retained and completed,
and its unfinished geometric comparison was completed here. There is no current return
or rework entry for this item. No new nodes, changed public interfaces, or forced consumer
adaptations are included.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
