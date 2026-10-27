## What changed

Replaced the only `sorry` in `Sheaf.AlgebraicGeometry.CanonicalProjOpenCoverGluing`
with a complete combination proof. It obtains the global section algebra and its normalized
comparisons from `exists_section_algebra_open_cover_descent`, obtains global full generation,
the canonical map and restriction equations from `section_canonical_map_open_descent`, and
proves the open-immersion conclusion in Lean. The comparison maps are open immersions by
`PullbackData.isPullback`; the local canonical maps give open immersions on each inverse-image
open. The structural equation makes equal-image points have the same base point, so they lie
in a common member of the cover and local injectivity gives equality. Mathlib's
`IsOpenImmersion.of_forall_source_exists` completes the argument, also for empty schemes/covers.

The two missing construction/comparison steps are stated in separate new modules, with their
actual normalized section equations expanded to avoid importing the parent module. This keeps
`canonicalSectionOpenPull` and `RelativeSectionAlgebra.OpenComparison` in their existing module
with identical bodies and signatures. The target theorem signature is byte-identical.
The node proof now records this decomposition. A full `lcompile.py --all` check passed
with no diagnostics; its three file times were 17.2 s, 16.3 s and 19.8 s, all below 60 s.
The final delivery also runs its compile/axiom/preflight checks. Public import cleanup is documented in
`coord/changes/A6-canonical-proj-open-cover-proof-imports.md`. No existing consumer is changed.

## Proved and sorry left

Closed the textual hole in
`AlgebraicGeometry.Scheme.Modules.canonical_proj_open_cover_gluing`
(node `lem-trf-canonical-proj-open-cover-gluing`). Its proof combines the two new lemmas and
proves the final geometric step; there are zero `sorry`s left in the item module.
This is a decomposition, not a proof independent of new holes: one upper hole closed,
two lower holes added, net -1 before any import-closure pruning. Zero original holes are
claimed fully discharged without new holes.

The delivery adds exactly these two remaining `sorry`s, both the complete proof of a public
named theorem, with no data definition using `sorry`:

- `AlgebraicGeometry.Scheme.Modules.exists_section_algebra_open_cover_descent`
  (`lem-trf-section-algebra-open-cover-descent`): constructs the global graded section algebra
  and its normalized open comparisons, without any generation, canonical-map or openness input.
- `AlgebraicGeometry.Scheme.Modules.section_canonical_map_open_descent`
  (`lem-trf-section-canonical-map-open-descent`): for an already given global algebra and normalized
  comparisons, descends generation and the canonical maps. It has no local openness hypothesis
  and no openness conclusion.

Both are strictly parts of the original four-step argument. The first has no map assertion;
the second does not construct the algebra or prove an immersion. Their combination alone does
not imply the conclusion; the written injectivity and locality proof is necessary.

## No longer needed

Removed direct imports:

- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`
- `WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons`
- `Sheaf.TraceFormula.SpaceLineModuleProjMap`
- `WeilConjectures.AlgebraicGeometry.GradedSheafStructures`
- `WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Universal`
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`

The first, second, fourth, fifth and seventh APIs needed by the signatures/proof remain
available through the two core public imports. The cochain-universe instance is not used.
The quasi-coherence and algebraic-space canonical-map arguments have moved into the proof plans
of the two new nodes, so their mathematical dependencies are retained there. No original DAG
node is declared permanently unnecessary, and no module is withdrawn. In particular, the
relative-Proj existence, base-change and space-line-map nodes remain in the combined argument;
this does not bypass the unit route.

A static import-closure comparison for this item loses `CoherentFiniteType`,
`SpaceLineModuleProjMap`, `SpaceLineGenerationOpen`, `SpaceLineTestMap`, `SpaceLineTestBaseChange`,
and `WeilConjectures.AlgebraicGeometry.Modules.GeneratesFibre`. This is the current textual import
closure only; the missing canonical-map proof may import these again. They are not claimed
permanently pruned from the targets. The downstream/direct-import searches find zero current
Lean importers of the item. Its unfinished DAG parents are kept.

## Where the brief, the DAG or earlier work was wrong

No false statement or unit-route error was found. The original step 1 labels the section-ring
construction and affine-basis quasi-coherence compatibility elementary, but the existing Lean
interfaces do not supply that construction in one application. The original steps 2-3 also
require building the scheme-specialized graded evaluation and checking the section/stalk
normalizations before applying the algebraic-space theorem. These are the two explicitly
recorded gaps, rather than a claim that the existing (possibly holed) dependencies are unusable.

Searched the actual dependencies, the source library and Mathlib before splitting. LeanSearch
returned generic quasicoherence constructors/presentation fields for the first step and absolute
Proj maps for the second; LeanFinder/Loogle returned absolute Proj basic-open constructions.
Read the signatures in `ProjectiveSpectrum/Basic.lean:435-515`: none states this normalized
relative section-algebra descent. msearch grep returned no matches; local searches found the
existing definitions and the specialized projective-polarization section-ring construction,
which has different hypotheses and no arbitrary affine-base descent. A title search of all DAG
nodes and blueprint searches for section algebra / section-algebra found no duplicate. The
broader canonical Proj blueprint search returned unrelated nodes. Searches are recorded on
both new nodes.

The new statements were checked on the identity/singleton cover, empty base/empty index cover,
infinite covers and non-affine overlaps; no finite subcover or affine-overlap assumption is
introduced. Degree zero and the scalar/unit normalization are retained, and no equality of
A_0 with the base structure sheaf is required. No shared definition or target is changed.

## New nodes

`lem-trf-section-algebra-open-cover-descent` realizes original proof step 1, from Stacks 01VJ,
section-algebra paragraph. Its conclusion fixes the comparison on every homogeneous section
and coefficientwise base change, not merely existence of unrelated algebras.

`lem-trf-section-canonical-map-open-descent` realizes original proof steps 2-3, from Stacks
01O9(3) and the 01VJ restriction paragraph. It uses the existing relative-Proj and canonical-map
nodes and states the remaining normalized-evaluation bridge without any openness assertion.

Both inherit `sec-trace-formula` / `sk-i-curve-zero` and the same blueprint ancestor, and have
complete proof docstrings and verbatim Lean signature records. No definitions or existing
statements are altered. Change record: `coord/changes/A6-canonical-proj-open-cover-proof-imports.md`.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
