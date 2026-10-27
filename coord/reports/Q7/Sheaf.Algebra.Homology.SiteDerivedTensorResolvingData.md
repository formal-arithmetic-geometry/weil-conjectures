## What changed

Proved `SheafOfModules.SiteDerivedTensorResolvingData.counit_existsUnique` with its
statement unchanged. The private helper `model_eq` identifies the recorded
`tensorDescentPair` with `KFlatFixedTensor.representativeIso`, by removing the
identity quotient comparisons. An `import all` proof import of
`Sheaf.Algebra.Homology.RingedKFlatSingleTensorComparison` reuses its existing proved
private `total_comparison` and `functorial_resolution`, without modifying their
module or exposing new public declarations. The comparison's components define the
required natural transformation directly. Functoriality identifies the curried
source maps with the published bifunctor maps; `tensorHom_def` identifies the two
whiskerings in the ordinary target with its tensor map. Uniqueness follows
by naturality along the two resolution augmentations, cancellation of their
invertible derived image, and natural-transformation extensionality.

Updated the owning node's proof, proof dependencies, and proof origin to record this
route. The public definitions, signatures, attributes, and public imports are unchanged.

Validation: `lcompile.py` accepted the complete module without warnings in 20.2 seconds.

## Proved and sorry left

Closed one of one holes:
`SheafOfModules.SiteDerivedTensorResolvingData.counit_existsUnique`
(node `def-pd-site-derived-tensor-resolving-data`). No holes added or split off, and
no `sorry` remains in the item. The proved private helper is
`SheafOfModules.SiteDerivedTensorResolvingData.model_eq`.

## No longer needed

Removed the direct proof import of
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`; it is already
available through the comparison module and remains mathematically needed there.
No module or node is withdrawn. No original proof-dependency nodes were pruned:
the original owning node had an empty proof and proof-dependency list. The
all-pair construction and functorial replacement already proved in the library
avoid rebuilding resolution and common-refinement arguments in this module.

## Where the brief, the DAG or earlier work was wrong

The node supplied no numbered proof steps, although its theorem docstring had the
resolution argument. Existing private lemmas in
`RingedKFlatSingleTensorComparison` already proved the existence and normalization
parts for the same selected tensor. Reusing them is enough; the new argument is
the comparison of model maps and uniqueness on all complex pairs. No statement
correction or change of the unit's route is needed.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
