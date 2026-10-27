## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction.integralNormalizedFamily_exists`.
The proof constructs localization choices at the required coefficient universe, establishes
Noetherianity and invertibility of ell, and applies the declared strict-system, completed-limit
and coefficient-extension theorems. The resulting family retains its completed arrow and reference.

The diagram-category Grothendieck instance is proved using evaluation left adjoints and a separator.
Two proved private logical helpers rearrange the limit witnesses while preserving every finite
normalization, completeness condition, comparison and uniqueness statement. All helpers remain in
the item module. `IntegralFamilyReference`, public signatures, shared definitions and the adopted
source library are unchanged. The node's proof record follows this argument.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction.integralNormalizedFamily_exists`.
No `sorry` remains in the delivered module. Added 0 holes; split off 0 statements.
The three stated diagonal-tower theorems are used as the stage-3 dependency declarations.

## No longer needed

None. All three original geometric proof dependencies are used. No original import, node or module
is withdrawn. The proof additionally uses the existing Grothendieck and localization size results.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was needed. Directly unpacking and rebuilding the nested limit
presentation made kernel checking exceed 60 seconds. Abstract logical helpers in the same module
avoid repeated reduction of concrete sheaf categories; the argument and all conditions are retained.
The characteristic argument uses no nonemptiness assumption on Y and works for every allowed prime.
The complete proof compiled with exit code 0 in 58.2 seconds before removing profiling options.
The delivery tool checks the cleaned file and its probe.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
