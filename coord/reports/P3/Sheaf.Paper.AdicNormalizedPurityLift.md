## What changed

Replaced the body of `WeilConjectures.AdicNormalizedPurity.normalized_purity_lift`
with a reduction that preserves its exact signature and all five clauses. The Lean
argument derives the finite purity isomorphisms from finite smooth purity, pastes finite
reduction with naturality to obtain the quotient square, detects invertibility of the
normalizations by their Hom bijections, transposes the square through the scalar
adjunction, restricts it to completed coefficients, and lifts the compatible maps to
an actual morphism of strict derived towers with the required evaluations.

The ten canonical definitions moved verbatim to the publicly reexported
`Sheaf.Paper.AdicNormalizedPuritySystems` to permit independent proof modules without
an import cycle. A textual declaration comparison verified that their signatures
and bodies are unchanged. See `coord/changes/P3-adic-normalized-purity-systems.md`.

Added a proved helper `WeilConjectures.normalizedDVRTowerEvaluation_full`. The existing
sequential-tower theorem fixes the raw site universe to its coefficient universe;
completed integral coefficients use independent universes. The new module adapts its
private chain-map proof to an arbitrary Grothendieck abelian category and specializes
to the actual completed-coefficient module category. It introduces no hole. The
sequential homotopy-correction route and unit route are preserved.

## Proved and sorry left

Original holes: 1, `WeilConjectures.AdicNormalizedPurity.normalized_purity_lift`.
Its body contains no sorry after this delivery, but this is a decomposition, not a
net proof: two strictly smaller public obligations are added:

- `WeilConjectures.AdicNormalizedPurity.actual_systems_normalized`, node
  `lem-pur-adic-actual-systems-normalized`: existence of the two actual normalized
  systems with their specified objects, evaluations and transitions; no purity
  invertibility, quotient square, exceptional-mate identity or morphism lift.
- `WeilConjectures.AdicNormalizedPurity.exceptional_normalization_mate`, node
  `lem-pur-adic-exceptional-normalization-mate`: only the identification of the
  specified exceptional quotient comparison with the actual transition mate.

Validation: all five packet modules compile through `lcompile.py`; the final item
compile completed without warnings in 53.4 seconds.

There are zero holes in the item module and two new holes in the packet. The tower
fullness helper and every private glue lemma are proved. Existing imported theorem
holes are retained as dependencies, not counted as holes closed here.

## No longer needed

No source-library declaration or module is withdrawn. No parent dependency or unit
step is removed. The item has no current Lean importers, but remains needed by its
unfinished parent in the DAG.

The original private proof imports `Sheaf.Paper.AdicCoefficientDatum`,
`Sheaf.SixFunctors.FiniteExceptional`, `Sheaf.Paper.CoefficientSystemDerivedComparison`,
`Sheaf.Paper.EtaleCoefficientSystemAdjoint`, and `Sheaf.Paper.ProEtaleConstructibleOrigin`
move to the interface or component lemmas that actually require them. Their nodes
remain needed transitively. `Sheaf.CategoryTheory.SequentialTowerEvaluationFull` is
replaced by the proved independent-universe specialization, preserving its argument.
No assertion is made that the original generic module is globally unused.

The item's direct proof-dependency list now records the two component lemmas, finite
smooth purity, finite reduction, naturality, source-normalization definitions,
normalized-tower definitions, and the new proved fullness helper. The old normalization
dependencies remain below the component nodes. The original direct tool approvals
`lem-weil-pbc-sequential-tower-evaluation-full`, `lem-coef-finite-exceptional`,
`lem-pur-coefficient-system-derived-comparison`, `lem-pur-etale-coefficient-system-adjoint`,
and `lem-sf-proetale-constructible-origin` are removed from the item node. The last
four remain dependencies of the component lemmas; the first is replaced by the
proved universe-general lifting argument.

## Where the brief, the DAG or earlier work was wrong

The existing sequential-tower fullness statement is universe-restricted relative to
the actual completed integral tower construction. This requires the proved
independent-universe version, not an arbitrary endpoint identification. Hidden bodies
of `no_expose` canonical definitions also require explicit private `import all` proof
imports when using their defining equations; no public visibility is changed.

Read the current transport coefficient-change proof (1), tower-gamma proof (1)--(3),
and reduction-compatibilities proof (1)--(3). The decomposition follows the original
node's normalization and mate-comparison steps. Equal quotient indices, the first
positive exponent, d=0, zero K and empty schemes impose no additional hypotheses:
identity quotients use the unit/triangle identities and the constructions are
functorial on zero objects. No target statement changes, and no mathematical error
or alternative unit route is claimed.

## New nodes

`def-pur-adic-normalized-purity-systems` owns the ten unchanged canonical definitions
in the new reexported interface; it asserts no normalization or purity theorem.

`lem-pur-adic-actual-systems-normalized` states original proof steps 1--2, with their
full source, proof in words, and dependencies, as an independent proof obligation.

`lem-pur-adic-exceptional-normalization-mate` states the adjunction-mate identification
in original proof step 3, retaining the exact canonical comparisons.

`lem-pur-normalized-dvr-tower-evaluation-full` records the proved specialization of
sequential lifting to the actual completed coefficients with independent universes.
The original chain-map proof and its prerequisites are explicitly recorded.

Each node has the three logged Mathlib searches. Searches found only general
adjunction, derived-category or ordinary adic-completion results, not these actual
coefficient-system statements. Blueprint-wide searches found no duplicate of the
new interfaces; the existing generic tower theorem is reused at the argument level
because its public signature does not cover the required universes.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
