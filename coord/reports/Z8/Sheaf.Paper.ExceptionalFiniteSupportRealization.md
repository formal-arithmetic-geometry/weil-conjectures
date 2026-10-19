## What changed

Filled the three proofs in `Sheaf.Paper.ExceptionalFiniteSupportRealization` without
changing any existing signature or definition. The ordinary open comparison is the
inverse adjunction mate of `integralExceptionalEtaleInverse`. The derived open
comparison is lifted using fully faithful precomposition with `DerivedCategory.Q`,
retaining the full square on every complex. The right-adjoint comparison is the
right mate of the specified compact-support comparison. Each uniqueness proof
checks the stated normalization, using identity morphisms, localization
extensionality, or the counit as appropriate.

Added proof-only imports of `Sheaf.CategoryTheory.MateIsoAlongEquivalences` and
`WeilConjectures.CategoryTheory.InverseMateEquivalence`. Their existing nodes
`lem-weil-mate-iso-along-equivalences` and `lem-stage3-inverse-mate-equivalences`
are used as generic tools for invertibility of mates along equivalences. No step
of the purity unit route is replaced. Updated the item's node to record these
proofs. The four private helpers are fully proved proof-internal calculations.

## Proved and sorry left

Closed all three original holes, attached to `def-pur-adic-support-realization`:

- `WeilConjectures.integralExceptionalEtaleOpen_existsUnique`.
- `WeilConjectures.integralExceptionalEtaleDerivedOpen_existsUnique`.
- `WeilConjectures.integralExceptionalEtaleRightAdjoint_existsUnique`.

No holes added, none split off, and no `sorry` remains in the delivered module.
The dependency declarations are used with their existing statements; this report
claims closure of this module's holes, not completion of its dependency closure.

## No longer needed

None. The original module had only its statement import
`Sheaf.Paper.ExceptionalFiniteRealization`; it remains necessary. The original
node had no proof dependencies to prune. Both new proof-only imports are used.
No nodes or modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was necessary. The node previously had an empty
proof list, although the declaration docstrings gave the mate and localization
arguments. Those arguments are now implemented and recorded as proof steps.
The previous interrupted compile log was a server-response failure; compilation
was resumed with the existing sandbox rather than treating it as proof feedback.

## Second reading by Z8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
