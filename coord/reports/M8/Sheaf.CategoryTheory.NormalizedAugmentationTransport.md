## What changed

Proved `CategoryTheory.normalized_augmentation_transport` in
`Sheaf.CategoryTheory.NormalizedAugmentationTransport`, preserving all signatures,
definitions, visibility and imports. The first equation is an explicit calculation using
functoriality, the augmentation and normalization hypotheses, and naturality of `b.hom`.
The second follows by postcomposing with `b.inv` and cancelling. The final clause is the
naturality of the already constructed comparison transformation. Updated the node's final
two proof steps to describe this use of Mathlib's naturality API.

The module compiled through `lcompile.py` in 5.9 seconds. Search of the library, Loogle
and LeanFinder identified the ordinary naturality and whiskering APIs; no additional
project dependency is required. Empty categories and noninvertible augmentations require
no cases or extra assumptions: the calculation uses only the explicitly supplied
isomorphism inverse and equations.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.normalized_augmentation_transport`
(node `lem-sf-cbc-normalized-augmentation-transport`).
One hole closed, zero holes added, zero remaining, zero split off.
The two helper definitions remain their original concrete constructions.

## No longer needed

No imports, nodes or modules are pruned. The sole stated dependency
`def-nagata-category` remains used as its Mathlib leaf. The separate hand calculation
of inverse naturality in the original Step 5 is unnecessary: the comparison is already
a natural transformation, whose `naturality` field proves the final clause directly.
No unit-level route changes.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement errors found. The final two planned calculations can be
supplied by the existing naturality field without additional assumptions. No repair,
consumer adaptation or new node is needed.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
