## What changed

Filled `AlgebraicGeometry.separated_lqf_fppf_effective_descent` in
`Sheaf.SecTraceFormula.SeparatedLqfFppfEffectiveDescent`, preserving its signature.
The proof follows Stacks Tag 02W8 in `literature/stacks-project/more-morphisms.tex`:
reduce the family to affine singletons, obtain saturated quasi-affine opens, restrict
the datum, descend each restricted datum, and glue by invariant-open effectivity.
Imported the two existing saturation modules and the proved source-library comparison
`Scheme.Hom.isLocallyQuasiFinite_iff`. A fully proved private helper establishes finite
coproduct stability for target-local properties by identifying each component square
as a pullback. The morphism property is separatedness together with Mathlib local
quasi-finiteness and local finite type, exactly equivalent to the original hypotheses.
Updated the existing node's proof and dependencies to match these choices.

The empty finite coproduct is covered by target locality with an empty open cover.
An empty local scheme is covered by the saturation-cover supremum equality; no
nonemptiness, quasi-compactness or local finite-presentation assumption on the local
structure morphisms is introduced. All construction choices occur inside the proof.
No public interface, definition, consumer, source-library file or target changed.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.separated_lqf_fppf_effective_descent`
(node `lem-trf-separated-lqf-fppf-effective-descent`).
The private helper `AlgebraicGeometry.property_sigmaMap` is completely proved.
Zero holes remain in the item; zero holes added; zero statements split off.
The existing imported family reduction, saturation lemmas and quasi-affine descent
remain dependencies, with their existing proofs or holes unchanged.

## No longer needed

Removed direct imports:

- `Sheaf.AlgebraicGeometry.FppfAffineRefinement`: the singleton is fpqc directly by
  `Scheme.Hom.singleton_mem_fpqcPrecoverage`; this module remains a dependency of the
  existing family reduction, so no global withdrawal is claimed.
- `WeilConjectures.AlgebraicGeometry.IsLocallyQuasiFiniteResLE` and
  `WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite`:
  restriction is already encapsulated by the saturation theorem; the comparison API
  handles finite type. They remain used by existing dependencies.
- `WeilConjectures.AlgebraicGeometry.SeparatedLqfBaseChange`: base-change stability
  follows from Mathlib instances for the three conjuncts, using the comparison API.
- `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum` and
  `WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine`: supplied by the statement
  imports of the used descent theorems; separate imports are redundant.

Removed the direct proof dependencies `lem-weil-pbc-separated-lqf-base-change`,
`lem-pc-fppf-affine-refinement`, and `def-pc-fppf-site`. Removed obsolete tool-use entries
`lem-weil-pbc-separated-lqf-base-change`, `lem-pc-fppf-affine-refinement`,
`lem-weil-pbc-qcqs-morphism-permanence`, `lem-weil-pbc-lqf-locally-finite-type`, and
`lem-weil-pbc-lqf-restriction-to-opens`. The latter three were already absent from the
current proof-dependency list. No module is withdrawn or asserted globally unreachable.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The affine singleton's fpqc-cover
check can use its already supplied quasi-compactness, instead of repeating finite affine
refinement. The existing comparison theorem allows standard Mathlib permanence and
locality APIs to discharge the family reduction's property hypotheses. The two recent
saturation nodes supply exactly the intermediate data used in steps 3 and 4.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
