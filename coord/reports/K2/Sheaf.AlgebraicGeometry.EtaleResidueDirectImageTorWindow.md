## What changed

Replaced the private helper's use of `DerivedCategory.bounded_heart_amplitude` with
`DerivedCategory.isGE_obj_of_isGE` and `DerivedCategory.isLE_obj_of_isLE`, already proved
in `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`. These apply directly
because the heart class is all module sheaves. The finite cohomology-triangle argument,
constant projection map, residue criterion, public signature and public imports are preserved.
Updated the item's proof node and docstring to record the actual finite truncation argument.
Removed local category aliases in the helper to avoid repeated kernel reductions of inferred
structures. Local braiding priorities align with derived tensor and residue testing, and
local irreducibility keeps derived models behind their proved APIs. These commands export
no changed instance or definition; see
`coord/changes/etale-residue-direct-image-model-transparency.md`.

The complete file compiled in 41.7 seconds; its four line-length warnings have been corrected.
The only downstream consumer, `Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients`, applies the
unchanged public signature, so it needs no adaptation.

## Proved and sorry left

The current shared source already contains B5's complete proof of
`AlgebraicGeometry.Etale.hasTorAmplitudeIn_rightDerivedLowerStar_of_relative_bound` and its
private helper `AlgebraicGeometry.Etale.directImage_tensor_window`: zero original holes.
This delivery prunes a dependency; it claims no additional hole closed. Zero holes added,
zero holes left, zero split-off statements.

## No longer needed

Removed proof import `Sheaf.CategoryTheory.BoundedHeartAmplitude` and the direct dependency
`lem-pur-bounded-heart-amplitude`, together with that obsolete top-level tool approval.
The wrapper module is absent from the item's transitive import closure after this removal.
The adopted library already proves both unrestricted bounded-input amplitude lemmas needed
here. No declaration is withdrawn. Other consumers can continue using the wrapper.
All other direct mathematical dependencies remain: finite presentation, finite-constant
projection, right-derived triangulatedness and single-object comparison, and residue testing.

## Where the brief, the DAG or earlier work was wrong

The dispatch overlapped B5's landing: the source read at session start had zero textual
holes. Its mathematical proof is sound; its general class-restricted amplitude wrapper was
unnecessary for the class of all module sheaves. The replacement uses the same finite
truncation triangles (Stacks derived.tex, Tag 08J5) and retains the unit route. Edge cases
c = 0, a = b, n = 1, zero complexes and empty schemes do not require additional hypotheses;
no residue flatness or perfectness is assumed.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
