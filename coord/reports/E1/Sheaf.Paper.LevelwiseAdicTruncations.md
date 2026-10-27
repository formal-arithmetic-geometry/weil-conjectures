## What changed

Restore the complete LevelwiseAdicTruncations proof packet recorded in red-build
repair 48160399e7852af6, retaining the earlier E1 local elaboration repair. Restore
seven fully proved helper modules and their nodes from the repair record. The four
remaining clauses are the uniformizer Tor criterion, constructible truncations,
the residue counterexample, and compatible retained origins.

Repair the cause of the global-build return by preserving BoundedConstructibleTower
verbatim. In particular, pbcAdicCompletion continues to abbreviate
AdicCoefficients.completedRing; the failed G1 change to its alias is not restored.
The reduction-tower section locally makes completedReductionCoefficient semireducible
while keeping the chosen limit irreducible, and explicitly finishes the private
comparison equality by rfl. Public signatures and definition bodies are preserved. Two broad simplifier calls
in construct_truncations are replaced by explicit endpoint equalities and identity
simplification; this avoids unfolding the complete tower witnesses.
The mathematical proof route is restored in the parent node.

Change record: coord/changes/E1-levelwise-reduction-presentation-scope.md.

## Proved and sorry left

Against the current post-rollback source, this delivery closes all four holes:

- AlgebraicGeometry.Scheme.pbc_levelwise_tor_of_uniformizer_injective.
- AlgebraicGeometry.Scheme.pbc_levelwise_truncations_constructible.
- AlgebraicGeometry.Scheme.pbc_levelwise_truncation_counterexample.
- AlgebraicGeometry.Scheme.pbc_levelwise_truncation_compatible_origins.

These mathematical proofs are restored from the prior G1 packet, not claimed as
newly discovered proofs by E1. E1 repairs their compilation against the original
public coefficient presentation and restores the supporting files rolled back
with that packet. The earlier E1 report counted zero holes before the asynchronous
rollback; the current shared source contains the four holes listed above.

Holes closed: four. Holes added: zero. Sorry left: none in any of the eight delivered
Lean files. No postponed lemma, axiom, or hollow definition is introduced. The seven restored
helper modules compile cleanly (0.2 to 6.2 seconds per file). The complete item compiles
cleanly in 39.2 seconds against those artifacts and the preserved public coefficient
presentation. Diagnostic profiler options and temporary diagnostic modules are removed.

## No longer needed

No Lean module is withdrawn. No public or proof import of the current item is removed.
The failed public-alias change to Sheaf.Paper.BoundedConstructibleTower is unnecessary;
its original source and node attachment are retained without adaptation.

The restored shorter argument does not directly use these former parent proof
nodes: def-weil-pbc-proetale-operations, lem-cbc-proetale-comparison-stalk,
lem-pur-proetale-inverse-image-stalk, lem-weil-pbc-finite-ring-constructible-sheaf-origin,
lemma-openclosed-point-ulift, or lem-pc-bounded-above-flat-kflat-site. Local-to-global
bounds instead use the published noetherian stratum-cover detector; the new alternating
resolution uses the existing independent-coefficient bounded-flat K-flat API. These
are parent dependency removals only, not claims that their modules are unused elsewhere.
The unit sk-rem-rest has no realized steps being bypassed.

## Where the brief, the DAG or earlier work was wrong

The retained packet initially compiled only because the seven helper modules were
still in the published build. After the G1 global-build rollback, their sources were
absent and deliver3.py correctly refused the four now-missing direct imports. They
are restored, with their own proof nodes, from coord/repair-notes/
Sheaf.Paper.LevelwiseAdicTruncations.json. No quarantine archive is deleted.

The registered repair identifies four failed downstream modules:
CompletedPullbackReduction, CompletedTowerDirectImage, FiniteExtensionReductionConeBound,
and PerfectChartTensorComparison. Their reported errors arise from the globally
changed pbcAdicCompletion presentation. This packet preserves that public definition,
so none requires a forced adaptation. It does not restore the obsolete G1 alias-change
record or the corresponding definition-node edit.

The earlier gate failure saying nothing was proved was recorded before the rollback
and before the current registered repair existed. It is not the current diagnostic.
The four original downstream consumers all compile unchanged against the published
build and this sandbox's restored helper artifacts: CompletedPullbackReduction
(56.9 seconds), CompletedTowerDirectImage (30.4), FiniteExtensionReductionConeBound
(9.3), and PerfectChartTensorComparison (28.9). Their temporary verification copies
are not delivered. All compiles use the documented LCOMPILE_NO_LOCAL setting with lcompile.py. No launcher
or project script is changed, and no resource limit is raised.

## New nodes

All seven nodes and their complete Lean proofs are restored from the returned G1
packet. They introduce no holes:

- lem-weil-pbc-alternating-unit-resolution: explicit bounded-above alternating unit
  complex, its K-flat augmentation, and its tensor homology.
- lem-weil-pbc-integral-local-reduction-lower-bound: the actual inverse-image completed
  principal quotient loses at most one lower cohomological degree.
- lem-weil-pbc-uniformizer-reduction-cohomology: injectivity of the next cohomology's
  scalar makes the canonical cohomology reduction comparison invertible.
- lem-weil-pbc-regular-single-reduction: reduction preserves degree-zero concentration
  for a module with injective principal scalar.
- lem-weil-pbc-regular-quotient-self-cohomology: regular self-reduction has precisely
  degree-zero and degree-minus-one cohomology.
- lem-weil-pbc-periodic-quotient-tor: the alternating unit resolution computes all
  nonpositive Tor for a module annihilated by its two differentials.
- lem-weil-pbc-principal-adjacent-quotient-tor: specialize this calculation to adjacent
  principal adic quotients and the residue module.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
