## What changed

Proved `WeilConjectures.finiteScalarTensorRealization_Y_representative` without
changing its statement or docstring. The proof unfolds the two scalar wrappers
and applies a fully proved equation with the scalar source already specialized.

Two new theorem modules stage the existing representative-descent argument:
`finiteScalarTensorRealizationForOrdinaryModels_representative` applies the proved
`finiteScalarTensorRealizationOfRepresentatives_fac` with abstract ordinary models;
`finiteScalarTensorRealizationForScalarSourceModels_representative` specializes its
source coefficients and fixed flat-term K-flat class while keeping the target
coefficient ring, ordinary functor and derived realization abstract. The assigned
module then supplies the concrete scalar realization. Both imports are proof-only
at their respective consumers. No existing definition or global attribute changes.

Local transparency settings and native coefficient-instance priorities keep Lean
from expanding realization, localization and sheafification constructions while
matching their already specified data. The derived-category aliases are locally
`implicit_reducible`; their bodies are the same standard localization.

The three proof files compiled individually within the limit: the ordinary-model
helper in 36.6 seconds, scalar-source helper in 49.9 seconds, and concrete item in
55.2 seconds. Diagnostic options were removed and long lines wrapped for delivery.
The assigned declaration's statement was also checked byte-for-byte against the
shared source. Every delivered Lean line has at most 100 characters.

## Proved and sorry left

Closed the sole assigned hole:
`WeilConjectures.finiteScalarTensorRealization_Y_representative`.

The two new supporting declarations are also completely proved:
`WeilConjectures.finiteScalarTensorRealizationForOrdinaryModels_representative` and
`WeilConjectures.finiteScalarTensorRealizationForScalarSourceModels_representative`.

Holes closed: 1 of 1. Holes added: 0. No `sorry` remains in any delivered module.
No unfinished statement was split off, and no definition was added.

## No longer needed

None. The original public import of `Sheaf.Paper.FiniteScalarTensorRealization`
is still needed by the statement. The proof follows the planned representative
descent route and retains its mathematical dependencies. Unused diagnostic and
experimental files were discarded; no existing project module or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan was correct. Directly substituting the concrete coefficient
realization into the generic equation exceeded the file limit during kernel
checking. The two fully proved stages freeze the ordinary-model and scalar-source
data before concrete substitution, keeping each file within the limit. No shared
definition or statement needed repair.

LeanFinder and LeanSearch found ordinary flat tensor facts, without the specified
normalization equation. Loogle found ordinary functor composition lemmas. The
Mathlib grep service returned no wrapper/descent hit; repository searches found
the proved representative-descent theorem used here. The new nodes record those
searches and the exact declarations used.

## New nodes

`lem-sf-finite-scalar-tensor-ordinary-model-representative-equation` records the
fully proved ordinary-model normalization equation. It is the existing generic
representative descent specialized before coefficient realization.

`lem-sf-finite-scalar-tensor-scalar-source-model-representative-equation` records
the fully proved specialization to the scalar source and its fixed representative
class. Its target ring sheaf, ordinary functor and derived functor remain arbitrary.
Neither theorem introduces an assumption or an existence choice. They apply to
all supplied representatives, including zero complexes when these are supplied.

The change record is
`coord/changes/finite-scalar-ordinary-model-representative-equation.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteScalarTensorOrdinaryModelRepresentativeEquation": "a81fe7b0e0e2eb201cedb5b70c3517c633a52ce0", "Sheaf.Paper.FiniteScalarTensorPullbackRepresentativeEquation": "a18b81d78da0f3992e87ff2695ce0021327cc054", "Sheaf.Paper.FiniteScalarTensorScalarSourceModelRepresentativeEquation": "adc2829df6201003e2d6d7282c4c580819c09613"}, "results": {"Sheaf.Paper.FiniteScalarTensorPullbackRepresentatives": {"hash": "5e83ed445a0a0a9b88beb7c8b335db959f28dd14", "status": "OK"}}, "seconds": 157, "time": "2026-10-28T01:40:15+0800", "transitive": 0, "version": 1}
```

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
