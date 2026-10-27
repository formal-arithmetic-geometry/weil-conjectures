## What changed

Replaced the proof of `ModuleCat.derived_bimodule_tensor_hom` by an assembly from the
existing enriched coinduction theorem and Mathlib internal currying. Every existing public signature and the theorem statement are preserved. The comparison
and scalar-unit definitions become definitionally equal aliases of the canonical
constructions now named in the new coinduction module; all other definition bodies are
preserved verbatim. Private proved helpers
establish the currying isomorphism, its three-variable naturality, its global-class formula,
the comparison natural isomorphism, the ordinary coinduction naturality reduction through a generic closed-category helper, and the
composite counit formula. Restriction compatibility follows by applying the functor to the
proved equations.

Added `Sheaf.Algebra.Homology.DerivedCoinductionEnrichedClass` for the coinduction-only
identity-class/counit normalization. This separate source lemma has no tensor parameter E:
the proof in the item derives arbitrary coinduction maps from its identity case by naturality,
then combines it with the independently proved internal currying formula. Its docstring and
node give the evaluation-at-one proof on K-injective representatives.

Updated the item node's proof, proof dependencies and proof origin to match this route.
Removed obsolete top-level tool-use approvals. The new module is publicly imported because it supplies the two definitionally equal
canonical constructions. No existing signature, definition data or source-library file
changes. The factored modules compiled in 19.1 and 44.0 seconds; the sole long-line
warning in that run was subsequently corrected. The definition repair and consumer audit are recorded in
`coord/changes/h7-coinduction-normalization-api.md`.

## Proved and sorry left

Closed the original named hole `ModuleCat.derived_bimodule_tensor_hom` (one of one),
conditional on the named source lemmas it imports. Added one named hole:
`ModuleCat.derived_coinduction_enriched_class`, node
`lem-trf-derived-coinduction-enriched-class`. This is a decomposition: one upper hole
closed and one strictly narrower lower hole added; net hole reduction zero. There are no
`sorry`s in definitions, private helpers or partial proofs. The item module has zero holes;
the added module has one. Existing imported theorem holes are preserved.

## No longer needed

The replacement proof does not use these planned nodes:

- `lem-trf-bimodule-resolved-hom-tensor-models`: the existing algebraic-shriek theorem
  already supplies the normalized Hom model and evaluation-at-one chain isomorphism.
- `lem-trf-bimodule-chain-currying-descent`: native closed internal currying provides the
  isomorphism and its naturality without constructing a second chain descent.
- `lem-trf-bimodule-adjunction-evaluation-scalars`: generic adjunction formulas provide
  the counit and scalar restriction; only the separate coinduction identity-class
  normalization remains.
- Direct use of `prop-pur-kinjective-resolutions-exist` and `lem-pc-kflat-resolution`:
  this assembly introduces no new resolutions. Their uses inside imported theorems remain.

Removed these unused private proof imports:

- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap`
- `Mathlib.Algebra.Homology.BifunctorShift`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`
- `WeilConjectures.Algebra.Homology.ModuleHomComplexQuotient`
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`
- `WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal`

Removed the item's obsolete `tool_uses` entries for `lem-pc-kflat-resolution`,
`def-sc-module-total-hom-complex`, `lem-pur-rhom-well-defined`,
`def-pc-kflat-complex`, `lem-sc-module-hom-complex-quotient`,
`lem-pc-derived-tensor-second-factor-functor`, `def-pur-derived-internal-hom`,
`lem-pur-rhom-into-kinjective-local`, and `prop-pur-kinjective-resolutions-exist`.
Statement dependencies and all old public imports remain intact; no declaration or module
is withdrawn, and no claim is made that other consumers cease to need those nodes.
The unit `sk-i-curve-zero` and its realized route are unchanged. The proof uses
`lem-asd-derived-category-symmetric` as a generic categorical tool: it supplies involutivity
of the already imported canonical derived braiding, needed only to identify the two tensor
orders in the global-class calculation. It replaces no geometric unit step. The maintainer
may record this tool use; the worker has not added a tool approval.

## Where the brief, the DAG or earlier work was wrong

The current item's three model-package proof dependencies have no Lean attachment, despite
the dispatch's dependency-readiness assertion. The older, already stated
`ModuleCat.algebraicShriek_derivedHom_adjunction` covers the required model clauses, so
this does not prevent the shorter route above. Its normalization clauses specify comparison
maps on complexes but do not themselves state that their identity global class is the
counit of the separately constructed ordinary derived adjunction. That missing compatibility
is isolated explicitly rather than assumed definitionally.

The launcher resumed this item with a fresh `.budget` reference start
1792775516.8545651 (2026-10-23 17:11:56 UTC); the original work and searches began
2026-10-23 12:38 UTC. The worker did not edit this metadata. No delivery had begun at
the interruption; the pending compile was checked before another compile was submitted. The resumed main
compile result is recorded by the launcher as `4e19833c044685a0af35ae56`, and the
independent normalization scratch compile as `551955cd6d215163fe8c1f2b`.

## New nodes

`lem-trf-derived-coinduction-enriched-class`, in
`dag/nodes/sec-trace-formula/lem-trf-derived-coinduction-enriched-class.json`, records
the normalized coinduction identity-class equation. The node cites Stacks dualizing.tex
Tags 0A70 and 0A71, its own three-step proof, the already stated Hom-model, projective evaluation and counit
lemmas, and logged LeanFinder, grep and LeanSearch searches. Its dependency closure was
checked and does not return to the item. Edge cases checked in the mathematical argument:
zero objects, the zero ring, identity and non-flat ring maps; evaluation at one and the
unit map require none of the excluded flatness or boundedness assumptions.

The definition repair record is `coord/changes/h7-coinduction-normalization-api.md`.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
