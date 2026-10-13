## What changed

Proved `AlgebraicGeometry.Scheme.exists_singletonTensorDegreeComparison_hom`
with its signature unchanged. Tensor universality combines the product projections
with the existing semilinear section restriction; ULift and Pi.lift produce the
required degree morphism. All private helpers are proved. The second reader adapted the private section-map
helpers to the upstream morphism-equality form of restriction semilinearity, and
proved its pointwise consequence for arbitrary scheme modules before specialization. No new modules, public
statements, definitions, or holes were introduced. Updated the existing node's
proof route and proof dependencies.

The proof locally reuses the normalization predicate's generated limit witnesses
`IsSingletonTensorDegreeComparison._proof_1` and `_proof_2`. Without this sharing,
kernel proof-irrelevance repeatedly compares large tensor-pullback types and exceeds
the 60-second compiler limit. The local instance attributes change no public
interface. Static preflight requests their documentation in
`coord/changes/singletonTensorDegreeHomLocalLimitWitnesses.md`. These auxiliary names require updating if the normalization module is
refactored. The complete file compiles in approximately 7 seconds.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.exists_singletonTensorDegreeComparison_hom`
(node `new-etale-affine-singleton-tensor-degree-comparison-hom`).
No sorry remains in this module; no holes were added or split off.
The final theorem and all 13 private helpers have been checked with `#print axioms`
in a scratch copy: only `propext`, `Classical.choice`, and `Quot.sound`, with no
`sorryAx`. The upstream restriction semilinearity theorem
`AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsRestriction_smul`
(node `lem-sc-etale-qcoherent-presheaf-functorial`) is now proved in the library.

## No longer needed

Removed direct proof imports:
- `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`.
- `Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf` (already available through
  the unchanged normalization public import).
- `Sheaf.AlgebraicGeometry.TensorPullback` (already available transitively).

The proof no longer uses the nodes
`lem-weil-pbc-module-pullback-affine-sections`,
`lem-weil-pbc-module-pullback-quasi-coherent`,
`lem-weil-pbc-fibre-product-affine-spectra`, or
`lem-pc-module-pullback-identity-composition` as direct proof dependencies.
The sheaf definition, normalization definition, and section semilinearity remain
needed. Their transitive imports remain; this report does not claim that the
removed modules are globally unreachable from every target. The unit record
`sk-prop-h2` has no realized statement or step carried by these auxiliary nodes,
and its route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The old DAG route constructs an affine sections identification, stronger than the
existence of the normalized additive morphism asked here. Tensor universality and
restriction semilinearity suffice, without affineness or an inverse comparison.
The earlier sandbox proof candidates failed kernel checking; they are not counted
as deliveries. This attempt isolated the failure to comparing newly inferred
limit witnesses with the normalization predicate's witnesses, and shares the
existing witnesses locally. It raises no heartbeat limit, changes no definition,
and does not split files to evade the compiler limit.


## Second reading by F1

1. Compared the delivered Lean module with the repository version using `diff`.
   The only existing declaration's signature is byte-for-byte unchanged, including
   affineness and quasi-coherence hypotheses. No public definition or target changed.
   The unchanged public normalization import is retained. The documented witness
   attributes are local to the section; they export no instance or interface change.
   Verdict: pass.
2. Independently compiled the complete final module using `lcompile.py`: clean,
   approximately 7 seconds. Scanned for forbidden declarations and every `sorry`:
   none. A scratch copy prints axioms for the theorem and all 13 private helpers;
   every result uses only `propext`, `Classical.choice`, and `Quot.sound`.
   Both private definitions construct their data by tensor lift or categorical
   product lift. Witness choices occur within proofs from proved existence lemmas;
   no arbitrary data is chosen from an unproved existence theorem. Verdict: pass.
3. No split-off statements or new nodes exist. Checked the generic finite tensor
   construction at an empty index set (empty product is 1), singleton indices,
   zero modules, and zero rings; the universal-property argument remains valid.
   The actual degree uses nonempty `Fin (n + 1)`, including degree zero, and
   `Fin (n + 1) → Fin 1` has exactly one index. The evaluation bridge is simply
   congruence applied to equality of additive morphisms. Verdict: pass.
4. Searched again using leanfinder for semilinear tensor universality, loogle for
   `TensorProduct.lift`, and grep plus `rg` for tensor-product section maps.
   The proof already uses the existing upstream `PiTensorProduct.liftCommAlgHom`
   and Mathlib tensor and product lifts; no complete comparison lemma was found.
   Checked every removed old proof dependency against the report. All four are
   listed, and the four removed imports are private proof imports. The auxiliary
   construction does not replace any realized step of `sk-prop-h2`; its unit
   record and route are untouched. Verdict: pass.
5. Compared the node diff: only `proof`, `proof_deps`, and `proof_origin` change.
   Their steps match the compatible projection ring maps, semilinear tensor lift,
   ULift, categorical product lift, and normalization equation in Lean. The
   unchanged node Lean statement agrees verbatim with the theorem signature.
   There are no new nodes to validate. Verdict: pass.

Second-reading repairs: the first compilation failed because upstream changed
`etaleTensorSectionsRestriction_smul` from a pointwise equation to an equality
of additive morphisms (documented in
`coord/changes/etale-tensor-restriction-semilinearity-map-form.md`). Added the
proved private `semilinearOfSmulHom` evaluation helper and changed only the two
private section-map helpers to accept that equality. Evaluation now occurs for
arbitrary modules, before tensor-pullback specialization, avoiding the expensive
instance comparison. No extra instance or transparency controls were needed.
Corrected the earlier report's stale claim that upstream semilinearity remains
sorry. No public signature, definition, import, node route, or hole changed during
this second reading. The first worker's proof docstring describes the shorter
universal-property route rather than the old affine-isomorphism route.
