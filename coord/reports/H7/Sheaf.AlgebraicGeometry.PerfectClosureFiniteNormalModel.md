## What changed

Proved `AlgebraicGeometry.exists_perfectClosure_finite_normal_model` in
`Sheaf.AlgebraicGeometry.PerfectClosureFiniteNormalModel` without changing its statement.
Added three proved private helpers: stalk transport through an isomorphism, reflection
of density along a surjective morphism, and restriction of a Cartesian square. The last
is the elementary proved restriction lemma from the source GenericModelAux, copied privately
to avoid importing its unrelated generic-smoothness dependencies.

The proof constructs the componentwise normalization of the reduction over K. Its dense
normal open supplies the dense closed-immersion locus, including dense inverse image.
Finite-presentation descent and compact-open descent give a model and open at a common
finite intermediate field. Finiteness and the restricted closed immersion descend directly
along the faithfully flat field extension. Surjectivity and density follow from their
surjective continuous comparison maps; Cartesian pasting transports the normal stalks.

The proof reuses the source-library route in
`WeilConjectures.AlgebraicGeometry.Curve.GenericModelField` without importing that larger
curve theorem or GenericModelAux. The revised DAG records the actual argument and dependencies. Every existing
signature, definition, public import and target meaning is preserved.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.exists_perfectClosure_finite_normal_model`
(`lem-weil-pbc-perfect-closure-finite-normal-model`).

One of one original holes proved; zero holes added and zero split off. No `sorry` remains
in the delivered Lean module. No existing dependency proof was replaced by a hole.

Validation: the final file compiled through `lcompile.py` in 9.3 seconds, with exit code 0
and no errors or warnings. Its original theorem signature is byte-for-byte unchanged; all
Lean lines are at most 100 characters. The revised DAG dependencies have no path back to
the item.

The argument uses already proved normalization, inverse-limit, finite-presentation descent
and fpqc property-descent declarations. The empty scheme is covered by the same construction:
the normalization coproduct and opens may be empty, and the density and stalk statements
then have their usual vacuous meanings. No nonempty-space hypothesis is introduced.

## No longer needed

Removed proof imports:

- `WeilConjectures.AlgebraicGeometry.LimitAffineTransition`;
- `WeilConjectures.AlgebraicGeometry.DescendFinite`;
- `WeilConjectures.AlgebraicGeometry.DescendClosedImmersion`;
- `WeilConjectures.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange`;
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization` (its required API remains available
  through the public normalization imports of the used modules).

The original direct proof import of
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit` is replaced by
`WeilConjectures.AlgebraicGeometry.FieldExtensionLimit`, which publicly supplies its API.

The following planned dependencies are no longer direct steps of this proof:
`lem-weil-pbc-limit-affine-transition` (use the explicit algebraic-subextension cone),
`lem-weil-pbc-descend-finite` and `lem-weil-pbc-descend-closed-immersion` (use fpqc descent
at the chosen stage), and `lem-pc-homeo-pure-insep` (surjective continuous comparison maps
suffice for density). The standalone normalization and coproduct steps
`def-sc-normalization`, `lem-sc-normalization-exists`, and
`lem-weil-pbc-scheme-coproduct-family` are encapsulated by the existing proved componentwise
normalization API. `def-weil-pbc-scheme-reduction` and
`def-weil-finite-integral-morphism` are not separate proof steps; their APIs are used through
the reduction and normalization theorems. No declaration or module is withdrawn; other
consumers may still need all of these dependencies. No blueprint unit is bypassed. The temporary proof imports of
`WeilConjectures.AlgebraicGeometry.FieldExtensionDescent` and
`WeilConjectures.AlgebraicGeometry.Curve.GenericModelAux` were also eliminated: use the small
field-extension fpqc-cover theorem and prove the restriction-square helper privately.

## Where the brief, the DAG or earlier work was wrong

The original plan enlarged the intermediate field separately to descend finiteness and the
closed immersion. That is unnecessary here: every field extension is faithfully flat and
quasi-compact, and the source library already proves fpqc descent for both properties.
The finite-presentation and compact-open descent steps are still needed and are implemented.

The normality and density APIs in the current reduced normalization module already provide
the componentwise stalk and inverse-image facts. No further normalization theory had to be
split off. No statement is disputed and no interface repair was needed.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
