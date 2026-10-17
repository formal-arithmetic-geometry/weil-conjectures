## What changed

Repaired `Sheaf.Paper.ProEtalePointComponentsMaps` on the current shared source.
`AlgebraicGeometry.ProEtale.specMapEquiv` now explicitly composes `Spec.homEquiv`
with a locally constant ring Hom correspondence. Its inverse is the existing,
proved `LocallyConstant.liftPrimeSpectrum`. A characteristic-idempotent argument
checks evaluation in every prime localization and proves the inverse law.
The restored evaluation lemmas and the public theorem prove affine transport,
the relative pullback correspondence and both naturality identities.

Every existing declaration signature, universe and visibility is byte-identical,
including the four helpers disabled in the baseline. Public imports are unchanged.
Only this Lean module, its main existing node and this report are delivered.
The two added ordinary imports provide the prime-spectrum and spectral-component
proof APIs. No new declaration, node or change record is introduced.

## Proved and sorry left

Closed both active baseline holes, by declaration name:

- `AlgebraicGeometry.ProEtale.specMapEquiv`: repaired the hollow private definition
  with an explicit equivalence and fully proved inverse identities.
- `AlgebraicGeometry.ProEtale.proEtale_point_components_maps`
  (node `lem-weil-pbc-proetale-point-components-maps`): proved all three
  topological properties, the correspondence and both naturality identities.

No holes are added, no holes remain in this module, and no statements are split off.
This closes 2 of 2 active holes: one theorem proof and one hollow-definition repair,
with raw net 2. The four disabled helper proofs do not count as active baseline
holes. The project's pinned sorry ledger determines its progress figures.

The item and a scratch copy auditing all twelve declarations compile cleanly
through `lcompile.py`, with the stale local Basic artifact removed. The spectrum
and affine equivalences use only `propext`, `Classical.choice` and `Quot.sound`.
The relative equivalences and public theorem additionally reach `sorryAx` through
the existing imported `weaklyEtale_toSpecZ_profiniteToScheme`, used to construct
`profiniteToProEtOf`. That dependency remains open in the current shared Basic
source; this delivery adds no such hole. The proved `liftPrimeSpectrum` itself
uses only the three permitted standard axioms.

## No longer needed

Removed the proof-only `import all
WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: its private Hom-equivalence
helpers are absent from the current source. Its public functor API is already
exported by `ProfiniteTestObjectFunctor`.

Removed `def-weil-pbc-profinite-locally-constant-hom-equiv` from this item's
`proof_deps`: the proof directly uses the source spectrum-lifting construction.
The definition node itself is left unchanged. Retained the spectral-scheme,
clopen-component and locally-constant-prime-spectrum dependencies, which support
the actual proof. Withdrew the unused top-level coproduct tool approval
`lem-galois-coproduct-copies-morphisms-clopen`. No whole module is claimed pruned
from the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The first worker's final implementation reused restored private helpers in Basic.
During this second reading the shared source changed again (Basic's source file
was refreshed at 2026-10-17 06:59 +08); those helpers are now absent. The sandbox
still contained a compiled Basic overlay, so the first compilation masked that
source mismatch. A scratch audit without the overlay exposed it. Removed the
stale Basic artifact and replaced the dependency with the explicit construction
inside the existing `specMapEquiv` body. No duplicate global helper was added.

Independent searches found the same elementary argument in the downstream
`CondensedFieldContinuousRealization`, which already imports this item. Importing
it here would create a cycle, so its elementary argument is reused locally.
Loogle `LocallyConstant, PrimeSpectrum, RingHom` returned no Mathlib match.
The main node now records the actual proof. The existing public docstring retains
the old finite-quotient plan; its direct affine replacement stays below unit level.
Weak contractibility remains in the unchanged statement and is unused by this
stronger affine construction.

## Second reading by B3

1. Compared every delivered file with the shared repository. All twelve existing
   declaration headers are byte-identical, including disabled helpers. No target,
   public import, universe, hypothesis, conclusion or visibility changes.
   The node changes only stage-3 proof fields and withdraws an obsolete tool use.
   Verdict: pass.
2. Read every construction, inverse law and naturality proof, compiled the item
   and a scratch copy with `#print axioms` for all twelve declarations. No local
   `sorry`, forbidden axiom, unsafe/opaque declaration, foreign implementation or
   hollow data remains. `liftPrimeSpectrum` is proved and its value is uniquely
   determined by all prime-localization images. The imported open weak-etaleness
   dependency and its `sorryAx` are explicitly recorded above. Verdict: pass.
3. There are no split-off statements or new nodes. Independently searched the
   library for ring Hom correspondences, component lifts and spectrum lifts, and
   ran the Loogle query above. Reused the proved spectrum APIs and the existing
   elementary inverse argument without importing a downstream module. Checked
   empty source and target spaces, singleton targets and the zero ring: no point
   is chosen globally and the pointwise assertions handle empty spectra vacuously.
   Equality in all prime localizations handles the zero ring. Verdict: pass.
4. Read downward from the public theorem: spectral component instances, affine
   correspondence, terminal-Spec-Z pullback equivalence, then pointwise naturality
   using quotient surjectivity. Reviewed every old proof dependency and import;
   the removed ones are listed above. Read `sk-thm-properbasechange` and its
   `realized` record: this item realizes none of that unit's statement or steps,
   so the direct affine argument stays below its fixed route. Verdict: pass.
5. Compared the node's proof, `proof_deps` and `proof_origin` with the final Lean;
   updated them to remove the unavailable Basic correspondence and describe the
   explicit localization inverse argument. All retained dependencies are used.
   The existing definition node and maintainer metadata are untouched. Verdict: pass.

Second reading changed: eliminated the stale Basic overlay dependency; constructed
its replacement inside the existing private equivalence; repaired its evaluation
proof; removed the proof-only Basic import and obsolete Hom-equivalence dependency;
corrected the report's axiom claims and aligned the main node with the actual proof.

Final dry run: `deliver3.py B3 Sheaf.Paper.ProEtalePointComponentsMaps --no-push`
printed OK at commit `5252ad6457`: compilation and preflight passed, classified
CODEX because this returned repair changes the node's proof metadata.
