## What changed

Completed `WeilConjectures.primitiveQuotientRealizations_unique` in
`Sheaf.Paper.PrimitiveQuotientRealizationsUnique`, with its statement unchanged.
Both clauses compare normalized strict tower isomorphisms by composing one inverse
with the other. The resulting target endomorphism fixes the finite pullback unit
generators or scalar tensor generators, respectively. Existing Hom extensionality
lemmas prove it is the identity. The common normalization postcomparison is
invertible by its equation with the prescribed comparison, so cancellation gives
equality on good representatives. Essential surjectivity and naturality give
equality on the entire ambient derived category.

Added proof-only `import all` lines for
`Sheaf.Paper.IntegralOperationsWellDefined` and
`Sheaf.Paper.IntegralScalarExtensionWellDefined` to use their existing private,
proved generator extensionality and good-localization lemmas. Added three proved
private helpers for finite pullback Hom extensionality, essential surjectivity of
the good localization, and cancellation of normalized postcomparisons. Local
irreducibility attributes keep large chosen functors abstract during elaboration.
Updated the attached node's three proof steps to describe the actual inverse
composition argument; its dependency list is retained. The completed proof
compiled through lcompile.py in 35.4 seconds. The resulting two style warnings
were repaired: the attribute line was wrapped and the declaration-local heartbeat
setting received an explanation. No profiling options remain.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.primitiveQuotientRealizations_unique`
(node `lem-trf-primitive-quotient-realizations-unique`).
Both the pullback and scalar uniqueness clauses are proved from the existing
interfaces. Holes added: zero. Sorries left in the item module: zero.
No statements were split off. Existing dependency holes were not changed.

## No longer needed

None. No imports were removed, and all four declared proof dependencies are used.
No module or node is withdrawn. Semantic search for natural-transformation
extensionality found generic Mathlib localization extensionality, while project
search located the existing restricted pullback Hom extensionality,
`integralScalarReduction_hom_ext`, and the good localization theorem. These
suffice without a new intermediate statement.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The existing plan works with the inverse
composition trick on the target strict towers, avoiding any need to prove a
separate extensionality theorem for their sequence-site source objects. The
scalar counit need not be assumed invertible: invertibility of the entire
postcomparison follows from the normalization equation. The proof works with
independent scheme and coefficient universes and includes zero objects and equal
fields. It uses the latest blueprint's integral comparison paragraph and the
existing lemmas from Stacks 06YS, 06YY, 0941 and their module docstrings.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
