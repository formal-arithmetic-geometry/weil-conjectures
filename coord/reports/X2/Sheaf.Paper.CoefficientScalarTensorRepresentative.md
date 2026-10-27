## What changed

The item theorem now constructs a basic package of its supplied comparison data and
proves the displayed section-complex equation by composing two strict substeps. The
new internal substep handles reconstructed internal complexes; the new transport
substep handles arbitrary section complexes via the exact section equivalence. The
comparison equation is named in a small proposition module, and the original public
statement and all its binders are unchanged.

## Proved and sorry left

The original `coefficientScalarTensorRepresentative` declaration is proved from the
two strict substep declarations. The delivery adds two postponed theorem proofs:
`coefficientScalarTensorRepresentative_internal` (node
`lem-sfb-coefficient-scalar-tensor-representative-internal`) and
`coefficientScalarTensorRepresentative_transport` (node
`lem-sfb-coefficient-scalar-tensor-representative-transport`). The data packaging and
equation declarations contain no `sorry`.

## No longer needed

The parent proof dependency declarations for the ordinary sheaf tensor universal
property, internal scalar tensor comparison, section tensor representatives, and
internal-section tensor comparison are no longer direct imports of the item module;
their role is represented by the two strict substep nodes and their documentation.
No existing library module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The prior split treated the whole arbitrary section-complex equation as one remaining
obligation. The actual proof has two independent strict components: the bidegree
signed calculation on internal images and transport across the section equivalence.
The delivery records both components separately, so neither new theorem is the parent
statement under a renamed hypothesis.

## New nodes

`def-sfb-coefficient-scalar-tensor-representative-basic-data` packages the five supplied
comparison objects. `def-sfb-coefficient-scalar-tensor-representative-hypotheses`
packages their four normalization hypotheses. `def-sfb-coefficient-scalar-tensor-representative-equation` names the fixed displayed equality. The two lemma nodes are
the internal-image calculation and the equivalence transport step. No target statement
or source-library declaration changed.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
