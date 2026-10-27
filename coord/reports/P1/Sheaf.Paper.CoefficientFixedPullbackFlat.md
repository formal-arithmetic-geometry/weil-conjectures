## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Scheme.coefficientFixedPullback_preservesFlat` by a proof from the
universe-polymorphic algebraic inverse-image flatness theorem and the normalized
constant-scalar equivalences. The proof first obtains the algebraic presentation of
the concrete fixed-scalar inverse image, sends the source object through the inverse
scalar equivalence, applies ordinary site flatness preservation, and recovers both
categorical tensor exactness conditions using the braiding. The final natural
isomorphism and equivalence counit transport flatness to the required object.

Added `Sheaf.CategoryTheory.ConstantScalarAlgebraicPullback`, containing the missing
algebraic identification as a single public theorem. This statement asks only for
an operation-compatible algebraic lift and a natural functor comparison. It has no
flatness hypothesis or flatness conclusion. It is the first step of the original
node's argument, independently usable for other properties of inverse image; it
does not rename or repackage the flatness obligation. Its full proof in words uses
unit-compatible forgetful inverse-image comparisons, normalization on constant
scalar sections, and extensionality on inverse-image units.

The three original public imports and all existing signatures are unchanged.
Added private proof imports of the comparison module, the algebraic inverse-image
flatness theorem, and `import all` of the coefficient finite-local-model pullback
module to use its proved finite-limit-preservation helper. No other existing Lean
module, definition, instance, or unit realization was changed.

Validation: `lcompile.py --all` compiled both modules in import order, respectively
1.8 seconds and 13.6 seconds. The new statement includes arbitrary small sites,
empty sites, the zero coefficient ring, and all modules in the chosen coefficient
universe. The argument uses no nonzero or nonempty assumption. No compilation or
consumer adaptation is needed for an existing interface change, because there is
no such change.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.coefficientFixedPullback_preservesFlat`
(node `lem-sfb-coefficient-fixed-pullback-flat`): 1 of 1 holes in the item module.
Its body now compiles without a `sorry`.

Added one hole in
`CategoryTheory.ConstantScalarRestriction.exists_constantScalarAlgebraicPullback`
(node `lem-sfb-constant-scalar-algebraic-pullback`), in its own new module. Its proof
is exactly `:= by sorry`. This is the algebraic-identification step, excluding the
flatness argument and the transport of tensor exactness implemented in the item.
There are no other holes in this delivery. This is a decomposition: one original
hole closed and one lower hole added, for net zero holes closed. The item is not
claimed to be axiom-free while this comparison is unfinished.

## No longer needed

No original import was removed, and no existing module was withdrawn or made
unreachable by this delivery. No modules are claimed pruned.

Removed `def-sfb-coefficient-fixed-derived-models` from this node's direct
`proof_deps` and proof-step uses: the ordinary flatness proof uses no derived
construction. That module remains transitively imported through the existing
public imports, and no claim of pruning it from the target closure is made.
The original constant-scalar restriction, coefficient exactness, and algebraic
inverse-image flatness dependencies are retained. The coefficient model's
finite-limit-preservation dependency and the new comparison are recorded explicitly.
The unit's statement and realized proof steps remain intact.

## Where the brief, the DAG or earlier work was wrong

The original plan's first step requires more than the statements of coefficient
exactness and constant-scalar tensor restriction: it needs the operation-compatible
identification of the particular fixed-scalar sheaf pullback with algebraic inverse
image over the constant coefficient rings. Neither of those declarations supplies
that comparison. Local searches also found a proved specialized pro-etale algebraic
lift, but its sites and coefficient universes do not match the arbitrary
coefficient-sized model of this item. The new node states precisely this missing
identification, while the rest of the plan is now Lean code.

No statement is disputed and no target or shared definition was changed. The
ordinary flatness theorem used by the proof is already proved; it was not copied
or replaced by another flatness assumption.

## New nodes

`lem-sfb-constant-scalar-algebraic-pullback`, in
`dag/nodes/sec-six-functors-basics/lem-sfb-constant-scalar-algebraic-pullback.json`,
realized by `Sheaf.CategoryTheory.ConstantScalarAlgebraicPullback` and
`CategoryTheory.ConstantScalarRestriction.exists_constantScalarAlgebraicPullback`.
It isolates the algebraic-identification step from the existing flatness proof.
The node includes its source, full proof plan, dependency union, three Mathlib
search records, and the original integral-models blueprint ancestry. There are no
change records, because no existing statement or definition was repaired.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
