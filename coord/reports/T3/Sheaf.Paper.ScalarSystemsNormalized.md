## What changed

Proved `WeilConjectures.SemilinearSections.scalarSystems_normalized` in
`Sheaf.Paper.ScalarSystemsNormalized`, preserving its complete signature.
All additional declarations are proved private helpers in the item module.
The only new imports are proof imports of Mathlib adjoint uniqueness and the existing
exact-derived-functor comparison API.

The proof constructs the identity-on-sections square of coefficient restrictions,
checks its compatibility with the strict transitions, and localizes that equation.
A categorical calculation with the two composite adjunctions identifies the output
reduction, up to evaluation and adjoint-comparison isomorphisms, with scalar extension
of the input reduction. Naturality of the input transition at the global scalar unit
and `S.transpose_evaluation` supply precisely the equation required by this calculation.
The node proof and proof dependencies now record this argument.

The complete proof compiled through `lcompile.py` in 16.8 seconds. Diagnostic
profiling was used to replace an expensive sectionwise rewrite by explicit equality
steps in separate proof blocks; the delivery contains no profiling or tracing.
Instance suppression is scoped to individual declarations. The delivery tool records
the clean compile and axiom probe for the final packet.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.SemilinearSections.scalarSystems_normalized`
(node `lem-coef-scalar-systems-normalized`).
There are zero remaining holes in the item module and zero holes added elsewhere.
No statements were split off.

## No longer needed

The previous planned dependency `lem-coef-semilinear-derived-sections`, implemented
by `Sheaf.Paper.SemilinearDerivedSections`, is unnecessary for this proof: the given
`S` already contains the scalar adjunctions, evaluation isomorphisms and their
transpose equation. Removed that dependency from the node's proof steps and
`proof_deps`; its module was never imported by the original item and is not imported
by this delivery. Both definition dependencies are retained. No original imports
were removed, and no declarations or modules are withdrawn.

K-flat representatives and `ScalarData.transpose_model` are unnecessary here:
the right-adjoint comparison fixes the required composite left-adjoint comparison.
The argument works for arbitrary specified scalar adjunctions with the supplied
evaluation transpose equation. In particular it includes `m = n`, zero rings,
empty sites and arbitrary unbounded input objects.

## Where the brief, the DAG or earlier work was wrong

The previous proof plan prescribed a K-flat/pure-tensor calculation when adjoint
uniqueness and localization of the ordinary restriction square suffice. The
statement is unchanged. No definition, consumer interface, target, or unit route
was changed. There are no new nodes and no forced adaptations.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
