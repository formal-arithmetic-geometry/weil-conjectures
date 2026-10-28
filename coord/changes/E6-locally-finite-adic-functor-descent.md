## Reason

The original theorem bundled two independent obligations: bijectivity on every derived Hom
and the characterization of the bounded constructible essential image. Splitting those
clauses gives the parent a real assembly proof while retaining the exact target statement.

## Old

`normalizedFunctor_descent` was a single theorem with a conjunction as its conclusion and
one unresolved `sorry` proof. Its direct proof imports listed the finite-stage realization,
coefficient comparison, condensed calculus, local-freeness, and filtered two-colimit APIs.

## New

Two new public theorem modules state the individual Hom and essential-image clauses, each
with its own source text, proof plan, and DAG node. The parent theorem imports them and
combines them using `And.intro`. The parent signature is unchanged.

## Users

The parent constructible realization module continues to import the parent theorem without
any source change. The new modules carry the proof-only imports that the parent formerly
carried directly; no existing declaration or consumer signature changes.

## Status

Open for independent review. All three delivered Lean modules compile in import order.
