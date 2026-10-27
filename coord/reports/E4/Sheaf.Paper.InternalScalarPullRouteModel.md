## What changed

The statement of `AlgebraicGeometry.ProEtale.QuotientChange.scalar_pull_route_model`
is unchanged. Its proof follows the node's three steps: normalize the X tensor
presentation and model target, commute the scalar and exact restriction counits,
and identify the remaining ordinary tensor square. The scalar/restriction
calculation is a proved private helper in the item module.

Three new supporting modules isolate the regular-coefficient counit calculation,
the X tensor/counit calculation, and the ordinary tensor square with the native
pullback monoidal structure. The ordinary square first proves equality of the
native and transported tensorators using the balanced tensor coequalizer.
The X calculation proves uniqueness of normalized tensor presentations on a
K-flat resolution, then applies the existing tensor-pull counit identity.
No hypothesis about flatness of the coefficient map or of P is added.

The item privately imports the two supporting calculations and the existing
restriction-mate and scalar-counit APIs. No source-library module, public
signature, definition, target, or unit route is changed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.QuotientChange.scalar_pull_route_model`.
The three new public theorems `scalar_regular_pull_counit`,
`scalar_pull_tensor_counit`, and `scalar_ordinary_tensor_pull_model` have complete
proofs, as do all private helpers. Holes closed: 1 of 1. Holes added: 0.
No `sorry` remains in any of the four delivered modules; no obligation is split
off with an unproved statement.

Validation: all four delivered modules compile together in import order without
errors or warnings using `lcompile.py --all`. The node Lean statements match
the declarations verbatim; proof dependency unions and the combined DAG were
checked, and the delivered Lean files contain no debug options or forbidden
constructs.

## No longer needed

None. No existing import, module or node is withdrawn. The original three proof
steps remain; the new nodes record their explicit normalization calculations.
The ordinary tensor square and derived tensor-model APIs remain dependencies,
including when accessed through the new supporting modules.

## Where the brief, the DAG or earlier work was wrong

The ordinary arbitrary-coefficient homotopy square uses the transported monoidal
structure. The model map uses the native composite monoidal pullback structure.
These are not interchangeable by a definitional equality: their tensorators must
be compared. The delivery supplies that comparison on the balanced coequalizer.
The original node anticipated this comparison, but the existing homotopy square
alone does not finish its third step.

The regular coefficient comparison also needs an explicit calculation with the
exact pullback counit. It involves only the degree-zero regular coefficient,
not the arbitrary-complex scalar route; it is not a renaming of the assigned
obligation. The unit's integral scalar-reduction route is preserved. The exact unit
calculation selects the native pullback monoidal instance and the relative
module tensor structures explicitly; it does not rely on conversion between
different monoidal functor structures.

## New nodes

`new-sfb-internal-scalar-ordinary-tensor-pull-model` records the ordinary
homotopy square with the native pullback tensorator. The native/transported
comparison is proved from balanced-coequalizer projection equations and
transport of a monoidal structure.

`new-sfb-internal-scalar-regular-pull-counit` records compatibility of the
restricted regular coefficient comparison with the exact pullback counit.

`new-sfb-internal-scalar-pull-tensor-counit` records the X tensor presentation
followed by the common-model target. It assumes no Y tensor normalization and
no scalar base-change comparison.

No change record is needed: no existing statement or definition is altered.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
