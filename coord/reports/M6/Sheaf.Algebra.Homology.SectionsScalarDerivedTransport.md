## What changed

Proved `CategoryTheory.SectionsScalarTransport.derived_transport` and
`CategoryTheory.SectionsScalarTransport.roof_naturality` in
`Sheaf.Algebra.Homology.SectionsScalarDerivedTransport`, preserving all existing
public declarations, signatures, definitions and public imports.

The proof constructs the localized functors, uses the supplied cochain models'
universal counits to obtain normalized comparisons, and descends the stipulated
chain cells by fully faithful whiskering. Explicit naturality calculations prove
representative formulas, uniqueness, both units, triple and four-stage coherence,
resolution computations and their inverse formulas. The iterated comparison law
follows from the triple law twice. The roof identity is a direct calculation from
naturality on its two legs. Private helpers only package these proved categorical
calculations; none is an unproved intermediate statement.

For K-flat and flat-term preservation, use the existing independent-coefficient
change-of-rings theorem and the existing site/monoidal tensor comparison. Updated
the item's DAG proof, proof dependencies and proof origin to this route. There
are no new nodes or changes to definitions or statements. The unit record
`sk-thm-sf-compatibility` has no realization bypassed by this proof.

Validation: the entire item compiled through `lcompile.py` with no errors or
warnings and with no `sorry`. Both original theorem signatures were checked
against the shared source. No source-library module is changed.

## Proved and sorry left

Closed 2 original holes:

- `CategoryTheory.SectionsScalarTransport.derived_transport`.
- `CategoryTheory.SectionsScalarTransport.roof_naturality`.

Zero holes remain in the item; zero holes added; zero split off. Both declarations
realize `lem-weil-sections-scalar-derived-transport`. This is a proof from existing
library results, not a decomposition into new unproved statements.

## No longer needed

Removed proof-only imports:

- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`: the cochain model and its
  universal counit are already supplied by the statement's model argument.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`: the computation
  clauses take a resolution as input, and the exactness hypotheses permit direct
  localization on all complexes. No resolution existence choice is made.
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`: replaced by
  `ChangeOfRingsKFlatIndependentCoefficients`, which matches the actual independent
  site and coefficient universes and the recorded scalar functor.
- `Sheaf.Algebra.Homology.RingedKFlatWordComparisonDescent`: descent of the given
  chain isomorphisms and their specified representative formulas follows directly
  from localization full faithfulness; the larger word-comparison theorem is
  unnecessary here.

The node no longer has proof dependencies on `lem-pur-derived-change-of-rings`,
`lem-pc-kflat-resolution`, `lem-pur-kflat-change-of-rings`, or
`lem-trf-ringed-kflat-word-comparison-descent`. Its statement dependency on the
specified derived model remains. Removed the old tool approvals for the last
three nodes (resolution, coefficient-restricted K-flat theorem, word descent);
retained the localization-left-derived-comparison approval in its original order.
Newly used existing dependencies are `lem-pur-kflat-change-of-rings-independent`
and `lem-weil-pbc-independent-sheaf-tensor-colimits`. No modules are withdrawn and
no assertion is made that these dependencies are globally unused by other items.

## Where the brief, the DAG or earlier work was wrong

The original plan was longer than this Lean statement requires. Preservation of
all quasi-isomorphisms makes direct localization available, and a resolution is
an input to the computation clauses, so resolution existence and generic word
descent are unnecessary. The original K-flat dependency's theorem used a more
restricted coefficient setup; the existing independent-coefficient theorem fits
exactly. The assumed iterated chain equation is redundant: the desired derived
iterated equation follows from the triple law and naturality. No hypothesis or
conclusion was changed, and no statement was found false.

## Second reading by M6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
