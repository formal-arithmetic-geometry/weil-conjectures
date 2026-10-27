## What changed

Filled `AlgebraicGeometry.Scheme.Modules.supportedSections_pushforward` in
`Sheaf.AlgebraicGeometry.SupportedSectionsPushforward`, preserving its statement and the three
supported-module constructions. Added two proved private helpers for the sectionwise range of
the kernel inclusion and its quasi-coherence. Added a proof-only import of
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`.

The proof makes the complementary open inclusion quasi-compact from the affine-open hypothesis,
uses base change for its inverse image, applies qcqs pushforward and quasi-coherent kernel
closure, compares the actual sectionwise linear ranges, and transports support along the given
isomorphism using naturality and its inverse. Updated the item's node proof to match this route.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.Scheme.Modules.supportedSections_pushforward`
(node `lem-trf-supported-sections-pushforward`).

Original holes: 1. Closed: 1. Added: 0. Remaining in this delivery: 0.
No split-off statements and no definition repairs or signature changes.

Validation: `lcompile.py` completed cleanly in 11.6 seconds, exit code 0.
All four original declaration signatures and all three construction bodies are unchanged;
the file has no `sorry` tokens and no lines exceeding 100 characters.

## No longer needed

The declared proof dependency `lem-trf-supported-sections-quasi-coherent`
(module `Sheaf.AlgebraicGeometry.SupportedSectionsQuasiCoherent`) is not needed by this proof.
Its existential subsheaf and affine ideal-power assertions are broader than what is required:
Stacks 07ZP(3) directly proves the quasi-coherence of our existing restriction-unit kernel from
restriction, qcqs pushforward, and the already proved quasi-coherent kernel theorem.
No import of that module is added. No existing imports are removed, and no modules are withdrawn.
The remaining original dependencies are used. The unit and chapter routes stay unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable construction was found. The DAG's Step 2 used a broader lemma;
the kernel argument in its own source, Stacks 07ZP(3), closes this step using existing proved
library results. The public theorem's original proof docstring remains the valid mathematical
plan; the updated node and this report specify the shorter Lean implementation.

Searches performed: Lean Finder on direct image and supported kernel sections, Loogle on
`SheafOfModules.pushforward, CategoryTheory.Limits.kernel`, the logged Mathlib grep on kernels
and restriction/pushforward, and direct source searches under both library roots. No exact
pre-existing combined theorem was found. The proved source kernel range API and quasi-coherent
kernel API provide the shorter route.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
