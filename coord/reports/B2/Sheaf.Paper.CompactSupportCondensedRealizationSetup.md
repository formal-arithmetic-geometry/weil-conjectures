## What changed

Proved the finite-extension and algebraic-closure coefficient flatness obligations in
`Sheaf.Paper.CompactSupportCondensedRealizationSetup` without changing their statements.
Added one proved private helper identifying a coefficient field continuously with its
finite intermediate-field image in the algebraic closure.

For a finite extension E to F, embed F into the algebraic closure and restrict the
embedding to E. The coefficient map factors through the inclusion of these two finite
intermediate fields, with ring isomorphisms on either side. For an algebraic-closure
embedding, factor through its finite intermediate-field image. The existing scalar
flatness theorems apply to the middle maps. Extension across the ring isomorphisms is
exact, and scalar-composition comparisons give the two conclusions.

Added proof imports of the existing algebraic-closure compatibility module and the
scalar-composition/equality comparison API. Both modules were already in the original
item's transitive import closure. All existing signatures, public imports, definitions
and the unit route are retained. No new Lean module or DAG node is needed.

## Proved and sorry left

Closed two of the item's three holes:

- `WeilConjectures.CompactSupportCondensedRealization.fieldExtension_flat`.
- `WeilConjectures.CompactSupportCondensedRealization.omegaExtension_flat`.

One original hole remains unchanged:
`WeilConjectures.CompactSupportCondensedRealization.realizedCoefficient_square`, attached
to `lem-pur-compact-support-condensed-realization-setup`. Its proof needs compatibility of
the normalized finite/integral coefficient charts with the scalar map, followed by
compatibility of the reconstructed section charts. The existing scheme-pullback square
has a different source and does not directly supply this coefficient-extension square.

Added zero holes and split off zero obligations. The private field-image isomorphism is
constructed explicitly and proved inverse in both directions. Mathlib's embedding into
an algebraically closed field is a proved construction, not an unproved existence input.

Validation: the item compiled successfully through `lcompile.py` in 56.6 seconds
with profiling enabled; those temporary profiling options were then removed. The
delivery command repeats the required compile and axiom checks.

## No longer needed

The flatness proofs do not directly use `lem-weil-pbc-condensed-flat-coefficient-calculus`
or its module `Sheaf.Paper.CondensedFlatCoefficientCalculus`. Instead they use
`lem-sfb-subfield-flat` and `lem-sfb-qlbar-flat` after changing coordinates by continuous
field-image isomorphisms. The old direct proof dependency is removed from the item's
node. No original Lean import is removed, and that module remains in the original
transitive import closure and may be needed by other consumers. No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The recorded finite flatness dependency is not directly applicable at the coefficient
universe of the item. However, a new finite-basis construction is unnecessary: every
finite coefficient extension embeds into the algebraic closure, reducing the question
to the existing finite intermediate-field theorem. The same field-image isomorphism
also reduces the algebraic-closure exactness obligation to an existing theorem.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
