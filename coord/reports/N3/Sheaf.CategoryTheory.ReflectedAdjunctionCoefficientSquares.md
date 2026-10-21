## What changed

Completed all proofs in `Sheaf.CategoryTheory.ReflectedAdjunctionCoefficientSquares`.
Added the private proof import `Mathlib.CategoryTheory.Adjunction.Restrict`.
All existing public signatures, definitions, instances and public imports are unchanged.
The additional proof elaboration options are documented in
`coord/changes/N3-reflected-coefficient-proof-options.md`; the downstream tool
reports zero current Lean consumers. Unfinished DAG parents remain attached.

The reflected adjunction is obtained by restricting the composite of the ambient
adjunction and the reflector adjunction. Its specified Hom equivalence gives the
unit and counit formulas. Reflection-unit injectivity proves normalization, and
the counit-transpose formula identifies the restricted mate. The composition
comparison is invertible because its precomposition maps into every local target
are bijective. Both pasting equations follow by naturality and Mathlib's mate
pasting lemmas. Identities and associativity are proved directly. Shift
compatibility uses explicit associators and unitors, the canonical full-inclusion
comparisons, and faithful transport of natural-transformation shift squares.
All auxiliary results are private and fully proved.

Validation: the remote single-file compile passed in 6.4 seconds with no errors
and no warnings. The delivery axiom check also passed; server preflight requested
the change record for the additional elaboration commands, now included.

## Proved and sorry left

Closed 18 original holes, all attached to
`lem-weil-pbc-reflected-adjunction-coefficient-squares`:

- `CategoryTheory.ReflectedCoefficient.Change.preserves`
- `CategoryTheory.ReflectedCoefficient.Arrow.adjunction_exists`
- `CategoryTheory.ReflectedCoefficient.Square.comparison_naturality`
- `CategoryTheory.ReflectedCoefficient.Square.mate`
- `CategoryTheory.ReflectedCoefficient.Square.normalization`
- `CategoryTheory.ReflectedCoefficient.Change.comp_kappa_unit`
- `CategoryTheory.ReflectedCoefficient.Square.coefficient_pasting`
- `CategoryTheory.ReflectedCoefficient.Arrow.comp_gamma_unit`
- `CategoryTheory.ReflectedCoefficient.Arrow.compositionComparison_spec`
- `CategoryTheory.ReflectedCoefficient.Square.adjunction_pasting`
- `CategoryTheory.ReflectedCoefficient.Change.associativity`
- `CategoryTheory.ReflectedCoefficient.Arrow.associativity`
- `CategoryTheory.ReflectedCoefficient.Square.identity`
- `CategoryTheory.ReflectedCoefficient.Arrow.identity`
- `CategoryTheory.ReflectedCoefficient.Context.stableUnderShift`
- `CategoryTheory.ReflectedCoefficient.Arrow.reflectedAdjunction_commShift`
- `CategoryTheory.ReflectedCoefficient.Square.commShift`
- `CategoryTheory.ReflectedCoefficient.Arrow.compositionComparison_commShift`

Zero holes remain; zero holes added; zero statements split off.

## No longer needed

None. No imports, nodes or modules were removed. The original ten-step DAG route
and all six declared Mathlib proof dependencies are used. The full adjunction
restriction API is a direct implementation of the stated natural-Hom-bijection
step, not a new mathematical dependency. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. Shift structures on definitionally equal
functors need not be definitionally equal: the proofs explicitly insert the
associators, unitors and full-inclusion comparisons to retain the specified
structures. The original declarations already have the correct statements.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
