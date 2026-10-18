## What changed

Proved `AlgebraicGeometry.Etale.etale_compactSupport_baseChange_qcqs` with its exact
original signature and public imports. Use the literal pullback square and the two squares
of `c.baseChange g`. Finite coefficients are additively torsion, so the stated module form
of proper base change makes the proper exchange invertible. Whisker its `asIso` on the
left by exact derived extension by zero, then compose with
`extensionZeroBaseChangeDerivedPlusIso` whiskered on the right by proper derived direct
image. Three functor associators give the required natural isomorphism.

The proof uses only two of the original private imports:
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper` and
`Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange`.
Updated the item's node proof, direct dependencies and obsolete tool-use approvals to
match this explicit implementation. No new imports, declarations, statements, definitions,
consumer adaptations or change records are needed.

Validation: the final module compiles through `lcompile.py` without errors or warnings.
Read the source's first proof paragraph (Stacks Tag 0F7L), the actual signatures of the
stated dependencies, and the compactification construction. LeanFinder and Loogle searches
found no Mathlib match. Library search found existing composite APIs; one uses an additional
unfinished exchange lemma without a DAG attachment, so the final proof directly composes
the already declared proper and open isomorphisms instead.
The qcqs and finite-type hypotheses remain unchanged. The argument also covers the zero
coefficient ring and arbitrary base change: it requires neither flatness nor density.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.etale_compactSupport_baseChange_qcqs`
(node `lem-weil-pbc-etale-compact-support-base-change-qcqs`).
Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
The existing proper-base-change and extension-by-zero dependencies still carry their own
proof obligations; this delivery does not claim they are transitively sorry-free.

## No longer needed

Removed these nine direct proof imports:

- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.OpenImmersion`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.SixFunctors.BaseChange.Derived`

The following original node dependencies no longer need separate proof steps or direct
imports here. Geometry is supplied by the actual base-changed compactification;
exactness/boundedness is part of the existing functors; the module proper-base-change
theorem directly gives the required module exchange (some dependencies remain transitive):

- `def-weil-open-immersion`
- `lem-weil-pbc-proper-fp-permanence`
- `lem-weil-pbc-qcqs-morphism-permanence`
- `lem-pod-separated-finite-type-base-change`
- `lem-weil-pbc-extension-by-zero-exact`
- `lem-sp-exact-functor-preserves-homology`
- `prop-weil-pbc-inverse-image-modules-exact`
- `lem-weil-pbc-exchange-forget-coefficients`

Removed obsolete top-level tool-use approvals for
`lem-weil-pbc-proper-fp-permanence`, `lem-weil-pbc-qcqs-morphism-permanence`,
`lem-pod-separated-finite-type-base-change`, `lem-weil-pbc-extension-by-zero-exact` and
`prop-weil-pbc-inverse-image-modules-exact`; retained the open base-change tool approval.
The proper-base-change unit's statement and its three realized steps remain used through
the proper factor; none is bypassed.

The following modules leave this item's transitive import closure. Other target branches
may still import them:

- `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`

## Where the brief, the DAG or earlier work was wrong

The mathematical plan is correct. The existing module-valued proper-base-change theorem
already includes the coefficient comparison and torsion reduction, and the compactification
API already supplies both Cartesian squares. Thus their internal arguments need not be
repeated. The final proof is the two-arrow argument of the stated source paragraph.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
