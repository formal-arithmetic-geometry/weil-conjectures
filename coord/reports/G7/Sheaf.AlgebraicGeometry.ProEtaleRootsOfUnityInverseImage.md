## What changed

Proved `AlgebraicGeometry.Scheme.existsUnique_proEtaleRootsOfUnityDirectImageMap` by constructing its components from `restrictRootsOfUnity` and the canonical roots-section equivalences. Three proved private helpers establish compatibility of these equivalences with the kernel inclusion, restriction, and the base-change projection. The projection square is `pullback.lift_fst`; applying `Hom.appTop` and `Hom.comp_appTop` gives the required equality on units. The construction's projection formula follows from `apply_symm_apply`, and section-equivalence injectivity proves uniqueness. The chosen direct-image map and its inverse-image adjunct keep their original definitions and signatures. Updated the existing node's proof route to this explicit argument.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.Scheme.existsUnique_proEtaleRootsOfUnityDirectImageMap` (node `def-pur-roots-of-unity-inverse-image`). Zero holes added and zero sorries remain in the delivery. This is a proof, not a decomposition. The proof covers every natural exponent, including zero, and uses no positivity, reducedness, or nonempty-scheme assumption.

## No longer needed

Removed the retained sandbox's proof-only import and draft module `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnityDirectImageNaturality`, and its unsubmitted draft node `lem-pur-roots-of-unity-direct-image-naturality`: the entire naturality calculation is now proved by private helpers in the item. These drafts never entered the shared library. No existing library module, public import, or declared dependency is pruned. The unit has no realized proof steps to bypass.

## Where the brief, the DAG or earlier work was wrong

The retained attempt's report described a completed decomposition, but its naturality theorem contained an unfinished proof and failed compilation. Its broad rewriting searched through the kernel construction and exhausted heartbeats. Explicit congruence equalities and a calculation through named local section equivalences compile with the default heartbeat budget; no dependency definition, statement, time limit, or elaboration option was changed. The remaining naturality obligation was proved here, so no new node or split-off is delivered. No mathematical statement repair was needed.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
