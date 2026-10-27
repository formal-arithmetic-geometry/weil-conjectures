## What changed

Proved `AlgebraicGeometry.Scheme.Modules.lineProj_chart_pullback` with its existing
signature unchanged, following all five chartwise steps. The proof establishes the
pure-tensor coefficient formula, the pulled-back frame and basic-open cover,
`G' = h ⁻¹ᵁ G`, equality of the two specified Proj maps, and the common fraction
factorizations and scalar equation. It works for an arbitrary commutative square.

Repaired returned delivery `bd4f25bd20c`: removed the duplicate private theorem
`stalk_generator_bijective` from `AffineTensorGeneratorLocus`. A proof-only
`import all WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes` now
reuses the existing private theorem directly, as the source library itself does in
`NonvanishingTransitionFunctions`. The source module is unchanged, and the redundant
direct `Modules.FlatPullbackStalk` import is removed.

Added the fully proved generic theorem `affine_tensor_generator_locus` in
`Sheaf.AlgebraicGeometry.AffineTensorGeneratorLocus`. It detects stalk surjectivity
on any fixed affine base/frame chart by a single unit coefficient. This supplies the
fixed-chart assertion needed in the existing plan; it does not assume that affine
intersections are affine or that the graded pieces are finitely generated.

Repaired the implementation of `lineProjPullbackMap` to use four named components
pinned by proved equalities to the canonical maps: `lineProjCompHom`, `lineProjCompInv`,
`lineProjSquareCast`, and `lineProjPowHom`. Each construction has an explicit singleton
witness, with no unproved existence or data hole. The public proved equality
`lineProjPullbackMap_canonical` certifies that the new map is the original composite.
This prevents repeated expansion of adjunction, equality-transport and power-comparison
terms during kernel conversion. The generic coefficient specialization checks in about
0.13 seconds; the unpinned version repeatedly exceeded the heartbeat/wall-clock limit.

All eight existing declaration signatures were compared textually and are unchanged.
No source-library declarations or bodies are changed. There are no downstream Lean
modules using the repaired definition; its only current consumer is this item itself.
The unit route is preserved. The change record is
`coord/changes/line-proj-pullback-map-components.md`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Modules.lineProj_chart_pullback`
(node `lem-trf-line-proj-chart-pullback`).

Added 0 holes; split off 0 holes. There are zero `sorry` tokens in both delivered
Lean modules. The new theorem `affine_tensor_generator_locus` and the canonical-map
equality are fully proved, as are all private helpers and all new definition fields.
The main proof uses the existing named affine-chart-atlas theorem and affine tensor-section
comparison as intended by stage 3; any holes in those existing dependencies are unchanged.

Validation: the repaired two-file packet passes `lcompile.py --all`: 9.0 seconds
for the generic criterion and 42.7 seconds for the main module. The duplicate-theorem
check also passes for the repaired generic module. All eight original declaration
signatures match the shared source exactly, and every Lean line is at most 100
characters. The current downstream scan still reports zero consumers of the repaired
definition outside this item. The delivery preflight checks consumers and axioms again.

## No longer needed

Removed the duplicate private stalk-generator proof; its existing source-library
theorem is reused through a proof-only `import all`. The generic module no longer
needs a direct `WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk` import.

Removed direct proof imports:
`Sheaf.AlgebraicGeometry.NagataAffineProjScalarExtension`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`, and
`Mathlib.AlgebraicGeometry.Gluing`. The Tilde API remains available through the needed
`Modules.PullbackSections` import; no source declaration is withdrawn.

The proof no longer uses the declared dependency
`lem-nagata-affine-proj-scalar-extension`: the precise standard-open and fraction
identities needed here are already Mathlib's `Proj.awayι_comp_map` and
`HomogeneousLocalization.Away.map_mk`. Its module remains in the shared library and may
still be needed by other consumers; it is not deleted.

The proof no longer uses `lem-weil-pbc-module-pullback-quasi-coherent`:
quasi-coherence of the given primed algebra is already part of its data. Each graded
piece is a retract of the given quasi-coherent total algebra and is identified with
a kernel, using `isQuasicoherent_kernel`. Thus no theorem about preservation of
quasi-coherence under pullback is required here.

The proof no longer uses `lem-weil-pbc-scheme-morphism-gluing`: equality is local for
Mathlib's existing `openCoverOfIsOpenCover`, and its `hom_ext` gives the required
uniqueness directly. No morphism is constructed by a new gluing theorem.

Removed the obsolete top-level tool approvals for the affine scalar-extension theorem
and pullback quasi-coherence theorem from the copied item node. The affine tensor-section
comparison and the existing canonical relative-Proj comparison remain needed.
No library module is withdrawn, and no blueprint unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The landing return correctly identified that the private stalk-generator theorem
had already been proved verbatim in the adopted source module. Its private visibility
requires `import all`, rather than an ordinary import; no duplicate declaration or
source-library visibility change is needed.

The mathematical statement is correct. The atlas alone does not immediately yield
the asserted cover using sections from one fixed affine base V. The new proved
`affine_tensor_generator_locus` supplies that assertion by representing a lifted frame
germ on an affine neighborhood and applying the finite-tensor/local-maximal-ideal argument.

The original composite is mathematically correct but expensive for kernel conversion.
The equality-pinned component implementation repairs this without changing its map,
any hypothesis, or any conclusion. The zero ring, empty opens, zero/nilpotent coefficients,
nonflat morphisms and exponent zero require no separate regularity assumptions:
all fraction comparisons cancel a unit only on its actual coefficient basic open.

## New nodes

`lem-trf-affine-tensor-generator-locus`: the fixed-affine tensor generator criterion,
proved in its own module from affine tensor sections, frame germs and the local-ring
maximal ideal criterion. Source: Stacks Tags 01NK, 01O9 and the tensor argument of the
item's first and third steps. Grep, Loogle and LeanFinder searches found no existing
fixed-affine-base statement. This introduces zero holes.

`def-trf-line-proj-comparison-components`: four equality-pinned names for the existing
canonical composition, equality-transport and power-comparison maps. Source: Stacks
Tags 0095/0097 and the canonical power comparison used in 0D2Z(3). Grep, Loogle and
LeanFinder searches found no such component interface. Its equality predicates have
explicit witnesses and its private equality lemmas are proved. Change record:
`coord/changes/line-proj-pullback-map-components.md`.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
