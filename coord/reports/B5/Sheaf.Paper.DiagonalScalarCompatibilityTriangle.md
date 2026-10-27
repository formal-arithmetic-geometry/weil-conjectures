## What changed

Replaced the body of `scalarCompatibility_triangle` by explicit constructions in both
directions. The original statement, its docstring, and its public import are unchanged.
The proof constructs/cancels the regular, line and supported endpoints, proves the
composition equation for each complete trace-domain arrow, cancels the three trace
squares, checks mate invertibility by two-out-of-three, and cancels the diagonal-class
square. It imports the new restriction-composition module for its proof; that module reexports
the endpoint-composition interface.

`DiagonalScalarEndpointComposition` constructs the exact restriction compositor and
its actual scalar-adjunction conjugate. Its `scalarHom_comp` proves composition of all
semilinear normalized arrows, including the shift by two. The unshifted part uses the
already proved `SheafExactDegreeZero.adjointInsertion_comp`; the shifted part is an
explicit calculation using the adjunction-induced shift structures.

`DiagonalScalarRestrictionComposition` isolates the remaining full-unit-normalized
restriction/direct-image construction and its mate composition on arbitrary derived
objects. It contains no diagonal diagram, line, trace, class, integration, endpoint
invertibility or mate invertibility hypothesis or conclusion.

No existing definition or statement was changed. No shared module needed adaptation.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.scalarCompatibility_triangle`.
Its proof is complete from the imported lower statements. The item's actual hole
count is zero.

Added one hole:
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.scalarRestriction_comp`, node
`lem-diagonal-scalar-restriction-composition`. Its proof is exactly `by sorry` in its
own module, with source and full proof in words. It isolates the restriction-square
step of the original plan, rather than repeating a scalar compatibility theorem.

`scalarHom_comp` and all private helpers are proved, without additional holes.
This is a decomposition: one original hole closed, one strictly smaller hole added;
the net hole reduction is zero. `lcompile.py --all` compiled all three files.
The only warnings in the final check were the temporary profiling options in the
item; those options have been removed before delivery. The compiler accepted every
file under its separate 60-second Lean execution limit.

## No longer needed

No original import was removed: `DiagonalCoefficientScalars` is required by the
unchanged statement. No existing module or declaration is withdrawn. The redundant direct import of
`DiagonalScalarEndpointComposition` and the unused proof import
`WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction` were removed during cleanup.

The original direct proof dependency `lem-sfb-internal-section-scalar-adjunction`
is replaced by the already proved exact degree-zero adjoint insertion API and the
actual `Mod.derivedExtendMapDerivedCategoryAdjunction`. No internal-section
presentation or its scalar generator calculation is used.

`def-sfb-comap-upper-star-iso` is not used by this proof or its new endpoint lemma.
The remaining restriction-square argument uses the scalar/geometric inverse-image
tensor comparison, rather than attempting to conjugate a restriction/inverse-image
square as though both functors were left adjoints.

`lem-diagonal-canonical-right-derived` is no longer a direct assembly dependency;
it remains in the plan of the remaining restriction lemma, where arbitrary full
universal derived models are compared. The ordinary lower-star comparison and
scalar-compatibility definitions likewise remain needed below and in the statement.
No claim is made that their source modules have become unreachable.

## Where the brief, the DAG or earlier work was wrong

No change to the mathematical statement or unit route was necessary. The proof plan
left the endpoint and trace cancellation as prose; this delivery supplies those
calculations. The upstream `derivedComapLowerStarIso` assumes flat coefficients and
cannot supply the nonflat restriction-square step. The remaining lemma explicitly
retains that missing generality and the full-unit equation. In particular, a
restriction/inverse-image isomorphism alone cannot be conjugated directly into the
required restriction/direct-image isomorphism; the scalar/inverse-image tensor
comparison and both relevant adjunctions are required.

## New nodes

`lem-diagonal-scalar-endpoint-composition` records the actual scalar associator and
the proved unshifted and shifted normalized semilinear composition equations. It is
a generic endpoint calculation with no direct images or diagonal compatibility.

`lem-diagonal-scalar-restriction-composition` records existence of normalized
restriction squares for arbitrary coefficient legs and composition of their scalar
mates. It is the remaining substep. Its edge cases include identity coefficient
maps, zero rings, empty schemes and nonflat coefficient maps; it asserts no
invertibility of scalar mates. The assigned node's proof dependencies now follow
the two lower steps and the explicit assembly. There are no change records because
no existing interface changed.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
