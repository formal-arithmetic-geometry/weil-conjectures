## What changed

Replaced the sole hole in `Sheaf.Paper.HigherDirectImagePresheaf` with the five-clause
categorical proof. The public signature and all public imports are unchanged. Added
proof imports of `Mathlib.Topology.Sheaves.Sheafify` and
`Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous`. Updated the item's node
proof and dependencies to the actual route.

The sheafification comparison is invertible because exact sheafification commutes with
homology and its counit is invertible degreewise. The adjunction gives the universal
factor explicitly and proves uniqueness by cancellation. Forgetting scalars reduces
the stalk unit to Mathlib's stalk-sheafification theorem. For restriction, derive the
sectionwise transformation, compute it in the chosen resolution, and use naturality
of the exact evaluation-homology comparison. Module pushforward is a right adjoint,
so Mathlib's left-exact degree-zero derived isomorphism applies.

## Proved and sorry left

Closed `AlgebraicGeometry.higherDirectImagePresheaf`
(node `lem-weil-pbc-higher-direct-image-presheaf`): 1 of 1 original holes.
No holes added or split off. No `sorry` remains in the delivered module.
The imported canonical definitions retain their existing dependencies and holes;
this delivery does not claim to close those dependencies.

## No longer needed

Removed these six proof-only imports:
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMap`
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties`
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial`
- `Sheaf.AlgebraicGeometry.ModuleOpenRestrictionInjectives`
- `Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives`
- `Sheaf.Paper.PQFCohomology`

The actual proof does not use these former direct proof dependencies:
- `lem-weil-pbc-scheme-modules-enough-injectives`
- `def-weil-pbc-module-cohomology-fmap`
- `def-weil-sheaf-of-modules-category`
- `pqf-def-cohomology`
- `lem-weil-pbc-module-open-restriction-injectives`
- `lem-weil-pbc-module-restriction-open-immersion-colimits`
- `lem-weil-pbc-module-cohomology-fmap-basic-properties`
- `lem-weil-pbc-module-cohomology-fmap-functorial`

Some remain transitively imported by the public canonical-definition modules; this is
pruning this theorem's proof route, not a claim that those modules have left the entire
target closure. No unit statement or realized unit step is bypassed: this node is not
itself a realized statement or step in `dag/units/sk-thm-p1.json`.

## Where the brief, the DAG or earlier work was wrong

The planned comparison through separately restricted injective resolutions and the
choice-based h-map is unnecessary for the exact Lean statement: its restriction is
already defined as the right-derived sectionwise transformation. Mathlib's
`InjectiveResolution.rightDerived_app_eq` and
`ShortComplex.homologyMap_mapNatTrans` give precisely its required compatibility.
No statement or definition correction was needed.

Searches used LeanFinder for sheafification and stalk comparisons, Loogle for
`mapHomologyIso`, and grep for `homologyMap_mapNatTrans|rightDerived_app_eq`, together
with repository and Mathlib reads. They found the exact Mathlib tools used above.
Edge cases introduce no new hypotheses: the categorical arguments apply also to
zero modules, empty schemes and opens, degree zero, and identity restrictions.

## Second reading by X3

1. **Interface unchanged — pass.** Compared the sole delivered Lean module with
   the repository by diff and checked the existing theorem signature byte for byte.
   Its statement, docstring, all public imports, and all definitions are unchanged.
   The node diff changes only `proof`, `proof_deps`, and `proof_origin`; there is no
   undeclared statement change or change record.
2. **Proof — pass.** Independently compiled the delivered module through
   `lcompile.py`: clean, 52.6 seconds. Read all five conjunct proofs. The counit is
   invertible degreewise, the universal factor is constructed through the adjunction
   and uniqueness follows by cancellation, the stalk unit is checked after a
   forgetful functor that reflects isomorphisms, restriction uses naturality of the
   homology comparison, and the degree-zero claim uses left exact pushforward.
   No `sorry`, forbidden declaration, hollow definition, or arbitrary witness was
   added. A scratch copy prints the theorem's axioms; the delivery tool also probes
   all delivered declarations. The scratch check compiled in 55.8 seconds and
   printed exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; the
   last comes from existing imported proof holes, which are not claimed closed.
3. **Split statements — pass, none.** There are no new statements or nodes and no
   split-off holes. The proof is a real combination of existing Mathlib results,
   not a restatement. Checked the cited Mathlib declarations in their source files,
   searched the repository and upstream direct-image modules under alternate terms,
   and queried Loogle for the homology-naturality result (the service did not index
   that identifier; the local source supplies it). The upstream section comparisons
   have additional geometric hypotheses and do not replace this general theorem.
   Zero modules, degree zero, empty opens/schemes, and identity restrictions add no
   hypotheses to these categorical arguments.
4. **Route and pruning — pass.** The direct canonical comparison and derived
   sectionwise restriction give the shorter route for the existing statement.
   The two new imports are proof-only: the stalk-sheafification theorem and the
   module-pushforward adjunction instance. All six removed imports and every one
   of the eight old proof dependencies absent from the new proof are reported under
   `No longer needed`. Checked the unit's `realized` record and searched the unit
   records for the pruned nodes: no realized unit statement or step is bypassed.
5. **DAG agrees — pass.** Read the old and new node and the canonical definitions
   used by the proof. The five proof steps track the five Lean conjuncts, their
   `uses` union is exactly `proof_deps`, and `proof_origin` correctly records an
   agent-written categorical implementation following the cited source. The
   existing `lean` record still matches the unchanged declaration.

Changes by the second reader: this review section only; no Lean or node repair was
needed. Several compiler attempts hit the 60-second wall-clock limit before a clean
52.6-second compile of the unchanged module; no limit or tool was changed. A shorter
scratch variant failed its final type comparison and was not adopted. Holes closed:
`AlgebraicGeometry.higherDirectImagePresheaf`; holes added: none (1 of 1, 0 split).
