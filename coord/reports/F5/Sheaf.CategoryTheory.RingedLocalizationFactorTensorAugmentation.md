## What changed

Proved `CategoryTheory.ringed_localization_factor_tensor_augmentation_quasiIso` without changing
its signature or any existing definition. Private proved helpers establish the localization tensor-unit
isomorphism, preservation of degreewise split sequences by total tensor, the explicit split
localization sequence, and the acyclic-kernel homology argument. Updated the item node to the
implemented argument. Added only private proof imports.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.ringed_localization_factor_tensor_augmentation_quasiIso`
(node `lem-weil-pbc-ringed-localization-factor-tensor-augmentation`).
No holes added, no split-off statements, and zero `sorry` left in the delivered module.
The final single-file server compile passed without warnings in 36.5 seconds.

## No longer needed

Removed the proof dependency `lem-weil-pbc-ringed-localization-complex-models`
(`Sheaf.Paper.RingedLocalizationModels`): the canonical tensor-unit map is computed directly
from sectionwise localization multiplication and naturality of sheafification tensor, so no
K-flat replacement or slice coefficient model is needed. This module was not imported by the
original item and no import line was removed. This is pruning of this proof edge only; its
other consumers and its declarations stay intact. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The stated localization tensor-product dependency supplies an unspecified isomorphism on
slice coefficients, whereas this obligation needs invertibility of a specific global unit
map. The proof obtains that map directly from multiplication and the canonical natural
tensor comparison. The mathematical one-generator kernel argument in the node is correct.
It includes zero and invertible generators, the zero ring, and the empty site, without any
nonvanishing assumptions. No statement or definition repair was required.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
