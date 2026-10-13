## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.FiniteAffineCechModelAcyclicResolution` with a proof using
`AlgebraicGeometry.exists_affineAlternatingCech_augmented_construction` on the canonical
chart `f ≫ T.toSpecΓ`, with identity base change. Its augmentation, section comparison,
and finite-product term descriptions are used. The auxiliary tensor additivity instance
is proved from `nonempty_tensorPullbackAdjunction`; its extra base-change conclusion is
not needed. The construction node is used as a general tool from
`sk-thm-picard-f-representable`; this item's unit, `sk-thm-picard-coherence`,
has empty `realized.statement` and `realized.steps` entries. The route remains the
finite affine Čech resolution and affine acyclicity described by that unit.

Five proved private helpers establish the affine vanishing argument without the cyclic
`AffineMorphism` module: `cechAcyclicOnAffines_toAb_of_injective`,
`cechAcyclicOnAffines_toAb_X₃`, `epi_pushforward_map_g_of_cechAcyclicOnAffines`,
`affine_rightAcyclic`, and `affine_open_rightAcyclic`. The first three reproduce the
proved source's local dimension-shifting setup; the fourth applies
`Functor.rightAcyclic_of_epi_map_g`; the fifth uses the existing ordinary derived
open-pushforward comparison. Finite products then give acyclicity of every term.

The final ordinary chain isomorphism uses `pullbackIsoPushforwardInv`,
`pushforwardComp`, `pushforwardCongr`, and `Functor.mapHomologicalComplexCompIso`.
It identifies pullback of the canonical-chart section model with exactly
`finiteAffineCechModel`, without altering any signature, definition, or public import.
All new imports are proof-only. The node copy records this route.

The five private helpers were compiled separately and `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound` for each. The combining proof and
chart transport compile in the excluded scratch test. Removing `Exact` was tested
and rejected: its specialized underlying-abelian-sheaf instances are needed.
On this retry all five helpers compile and their axiom lists contain only the three
allowed axioms. Removing `QuasicoherentKernel` was also tested and rejected:
`epi_of_forall_exists_app_eq` is declared there and used by the lifting helper.
The target signature is unchanged, the delivered module has no textual holes,
all lines are within 100 characters, and only the allowed proof fields of the node
have changed.

Searches: Lean Finder returned general sheaf/quasi-coherence results without an exact
resolution; Loogle did not recognize the project's `Functor.rightAcyclic`; Mathlib
grep found pushforward composition and adjunction infrastructure. Repository searches
found the usable increasing-tuple construction and the import cycle described below.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.exists_finiteAffineCechModel_acyclic_resolution`
(node `lem-pc-finite-affine-cech-model-acyclic-resolution`), by the written Lean proof
from existing declarations. One upper hole is replaced; zero new holes are added.
The full module compiles against the actual construction import. No sorry
remains in the delivered module. The existing imported construction theorem remains
an upstream proof obligation; it is not a new statement or a hole added here.

The empty cover, empty affine opens, zero coefficient module, and degrees without
increasing tuples are included by the existing construction and closure of rightAcyclic
under empty finite products. No existential witness is used in a definition.

## No longer needed

No original import was removed: the existing public imports support the statement,
its inference, and the acyclicity proof. No additional unused proof import remains.
The following original direct proof dependencies are no longer used directly:

- `lem-pc-cech-sheaf-resolution` / `Sheaf.AlgebraicGeometry.CechSheafResolution`;
- `lem-pc-alternating-cech-computes` / `Sheaf.AlgebraicGeometry.AlternatingCechComputes`;
- `lem-pc-affine-open-pushforward-acyclic` /
  `Sheaf.AlgebraicGeometry.AffineOpenPushforwardAcyclic`;
- `lem-weil-pbc-separated-affine-open-intersection` (Mathlib leaf);
- `lem-weil-pbc-pushforward-tilde-spec` (Mathlib leaf);
- `lem-weil-pbc-affine-tilde-gamma-adjunction` (used internally by the existing
  augmented construction, not a direct dependency of this proof).

The full derived resolution-core and exchange modules are not needed. The cyclic
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism` import is
avoided. This is direct-dependency pruning; no claim is made that other target
routes or transitive imports cease to need all these nodes.

## Where the brief, the DAG or earlier work was wrong

The planned `AffineOpenPushforwardAcyclic` dependency cannot be imported here:
`import_direction.py may` rejects it because its source affine-vanishing import
reaches this item through `FiniteFreeComplex`. The proof instead reuses the lower
proved affine Cech, section-lifting, injective-flasque, and dimension-shifting
infrastructure, plus the acyclic open-pushforward derived comparison, none of which
reaches this item.

The source `AffineAlternatingCechAugmentedConstruction` is landed but was initially
absent from the last published compiled snapshot. During that delay the helpers,
finite-product argument, and chart transport were checked in an excluded scratch
file against a temporary assumption of just the construction data. That assumption
is not present in the delivered Lean. The full compiler and dry run now check the
actual existing theorem after publication.


On this retry the published construction artifact is available. The full item compiled
cleanly against the actual imported theorem. The first dry run completed compilation
and its axiom probe, then identified a namespace-level `variable` command as an
interface change. That command was removed: the same binders now occur explicitly
in the private helper signatures, with no change to the public theorem signature.
The previous publication blocker is resolved. The second reading is reserved for
the independent reader; no second-reading section is written by this worker.

Final validation: `lcompile.py` compiled the delivered file cleanly in 9.9 seconds.
`deliver3.py N2 Sheaf.AlgebraicGeometry.FiniteAffineCechModelAcyclicResolution --no-push`
printed OK: compilation and preflight pass except for the second reading, which
the second reader writes. Nothing was pushed.

## Second reading by N2

1. **Interface: pass.** Read the entire repository/sandbox diff. The existing public
   theorem signature is byte-for-byte identical, independently checked by extracting
   the text before `:= by`. No existing definition, docstring, visibility, public
   import, target, or other module changed. The additions are seven proof-only imports,
   five private proved helpers, and the target proof. No change record is required.
2. **Proof: pass, conditional on the existing construction obligation.** Independently
   compiled the full delivered module cleanly (11.4 seconds). Compiled a scratch copy
   with `#print axioms` for all six declarations. Each private helper uses only
   `propext`, `Classical.choice`, and `Quot.sound`; the public theorem also uses
   `sorryAx` from the existing augmented-construction theorem. There is no textual
   sorry, forbidden declaration, or definition choosing an existential witness in
   this delivery. The witnesses D, epsilon, and comparison isomorphisms are consumed
   solely inside the theorem proof. This closes one local hole, adds zero holes,
   and does not claim an axiom-free proof of the complete import closure.
3. **Split statements: pass (none).** There are no new public statements, new nodes,
   or split-off holes. Read the existing construction statement: its finite-product
   terms and augmentation supply the geometric part; the added acyclicity argument
   is a genuine further reduction, not a newly holed restatement. The empty cover,
   empty affine opens, zero module, and empty finite product require no extra
   hypotheses. No split-off statement remains to close.
4. **Route and pruning: pass.** Searched the repository for affine right-acyclicity,
   section-surjectivity, and derived open-pushforward comparisons, and read
   `DirectImage.AffineMorphism`, `FiniteAffineCechModelComparison`, and
   `AffineOpenPushforwardAcyclic`. The existing public affine vanishing theorem is
   bundled with imports reaching this item; the equivalent helpers in the comparison
   module are private. The five helpers here reproduce the proved lower argument,
   avoiding that cycle. Read the ordinary derived comparison and the explicit model
   definition: the final chart transport has exactly the required target complex.
   Every added proof import supplies a used declaration or instance; the original
   public imports are preserved. The report lists all six removed old direct proof
   dependencies. Read both `sk-thm-picard-coherence` (the item's actual unit) and
   `sk-thm-picard-f-representable` (the construction's unit): their realization lists
   are empty. The construction is used as a generic Čech tool; the item's argument
   still follows the finite affine Čech and affine-acyclicity route, with no change
   to a unit statement or step.
5. **DAG: pass.** Compared both node files. Only `proof`, `proof_deps`, and
   `proof_origin` changed. Read the recorded dependency declarations, including the
   affine Čech exactness and section-lifting nodes. The new dependency list is the
   union of the written proof steps' uses; the chart transport and finite-product
   acyclicity agree with the Lean proof. There are no new-node records to check.

Second reading changed only this report: corrected the item's unit reference and
recorded the independent review and axiom results. No Lean or node repair was needed.
