## What changed

Restored the upstream unrestricted compact-support reduction declaration and recorded that its
statement is disputed. The declaration remains the named `sorry` attached to this module.
The finite and principal-domain reduction theorems remain unchanged and compile.

## Proved and sorry left

No existing `sorry` was closed. The declaration
`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerShriek` remains a
named `sorry`. No new `sorry` or definitions were added.

## No longer needed

The previous attempted pruning of the unrestricted declaration is withdrawn. No imports,
modules, or DAG nodes are pruned in this delivery.

## Where the brief, the DAG or earlier work was wrong

`STATEMENT-DISPUTED: the unrestricted statement is too strong for arbitrary ideals.` For a
general commutative ring, `Λ/J` need not be dualizable (for example, a non-projective
quotient), while the projection comparison used by `Rf_!` is only known here under finite,
principal nonzerodivisor, or weakly regular hypotheses. The existing finite and
`IsPrincipal` variants express the available valid results. The historical pruning was
rejected by the stage-3 gate because it removed an upstream declaration, so this delivery
retains that declaration and records the issue instead.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
