## What changed

The original theorem now has a complete Lean proof from two strictly smaller steps.
`Sheaf.Paper.CondensedFinitePresentationMatrices` proves the entire local matrix
step: finite affine refinement, preservation of presentations under pullback,
simultaneous descent of all matrix entries, and the scalar-extension comparison
of their cokernels. Its explicit proof uses the section clause of the
existing qcqs calculus and proved library/Mathlib declarations.

`Sheaf.Paper.CondensedLocalModelGluing` isolates overlap descent and effective gluing
for local models that have already been supplied. The original module
proves that the resulting global model is locally finitely presented, using the existing proved finite-presentation
transport API in `Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars`. Its public signature is unchanged.

All work uses the actual inverse-image coefficient rings throughout, avoiding
transport to the standard coefficient rings on the stratum. The DAG records this
route. No target statement or existing definition changes.

Repair of the returned landing: `fp_iff_of_iso`, `fp_map`, and `fp_extend`
are now public in their existing unclaimed module
`Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars`, with identical
statements and proofs. The matrix and parent modules import and reuse them.
The duplicate helper proofs and parent regular-module isomorphism are removed.
The DAG records this shared proof dependency. No new hole is introduced by
this repair.

H4 repair of returned head `6ac00d95e`: deleted the entire private
`AlgebraicGeometry.ProEtale.regularRingIso` definition from the matrix module.
Its sole call now uses the already-public `Mod.regularIsoOfIsIso eR.hom` from
`WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod`. The required regular-module
isomorphism has definitionally the same type. No new helper is introduced, and
there is no Compatibility source or visibility change in this delivery.

This deliberately differs from H4's prescribed helper name: F3's
`Mod.regularRingIso` remains private, but its more general public counterpart
already exists. Reusing that API removes the external publication prerequisite.
The change record gives both signatures and the precise difference for review.
All four retained modules now compile against the shared baseline, without a
Compatibility overlay. The prior second-reading section below is historical,
not a reading of this H4 repair.

## Proved and sorry left

The H4 repair itself closes zero holes and adds zero holes. The retained delivery
contains exactly one `sorry`, the gluing theorem named below. Counts relative to
the original assigned module are one hole closed and one lower hole added.

Closed the original hole:
`AlgebraicGeometry.ProEtale.exists_lfp_finiteCoefficient_model_on_immersion`.

Also proved the new intermediate theorem:
`AlgebraicGeometry.ProEtale.exists_common_finiteCoefficient_presentation_matrices`.
This is a full proof relative to the existing qcqs section-calculus declaration;
it contains no new holes.

Added one remaining hole, and this is every `sorry` in the delivered Lean files:
`AlgebraicGeometry.ProEtale.exists_finiteCoefficient_gluing_of_local_models`.
It assumes the finite cover and all local models and comparison isomorphisms;
it only supplies a common enlargement and their global gluing. It does not
assert local finite presentation of the global model. Thus this delivery is a
decomposition (one original hole closed, one lower hole added; net zero holes),
with the substantial local-matrix part proved.

The remaining gluing proof needs: (1) restriction, regular-module and scalar-extension
compatibilities for the existing
`CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence`; (2) the Hom part
of the existing qcqs calculus plus tensor adjunction on pairwise and triple overlaps,
to descend transition maps and their finitely many equations; (3) the existing ringed-site
gluing, weakly-etale localization, tensor-pullback and Hom-gluing interfaces, transported
through that equivalence. The equivalence itself is already proved in
`Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence` and must be reused.
The source and full argument are in the gluing theorem's docstring and new node.

Fresh validation of the repaired files: all four modules compile through
`lcompile.py --all` against the shared baseline. The matrix theorem and the reused public helper have exactly the allowed
axioms (`propext`, `Classical.choice`, `Quot.sound`). The two existing direct
consumers of the public finite-presentation helpers,
`Sheaf.Paper.ContinuousIntegralComparisons` and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`, also compile
against the changed sandbox dependencies without adaptations. The required dry
run's final output is saved in `scratchpad/h4-public-regular-iso-dry-run.log`.
Nothing was pushed.

During this repair session, the remaining gluing proof was pursued in scratch:
finite presentations give categorical finite presentability on qcqs schemes;
maps to the coefficient colimit descend to finite stages; finitely many maps and
equalities have common stages; the internal/sectionwise equivalence commutes with
restriction and transported scalar extension; and the compatible-tuples module
has the expected comparison isomorphism when checked on a cover. These compiled
proofs are retained in `scratchpad/` for continuation. They introduce no delivered
imports, declarations or holes. What still needs combining is weakly-etale
localization and the actual overlap transition/cocycle descent.

## No longer needed

The current second reading also removes the matrix module's redundant proof-only imports
`Mathlib.Algebra.Category.Grp.ForgetCorepresentable` and `Mathlib.Order.ULift`.
Both APIs are already available through the retained imports.

The original proof-only import `Sheaf.Paper.ProfinitePointPullback`, node
`lem-weil-pbc-profinite-point-pullback`, is absent from every delivered proof.
Pulling back the already-proved coefficient colimit twice gives the required
colimit directly, so no point-pullback or coefficient-ring identification is needed
for this item. This is pruning of this item's dependency edge; other users may
still need that module.

The original proof-dependency edges to
`lem-weil-pbc-quasi-separated-affine-cover-criterion` and
`def-weil-pbc-scheme-conventions` are also unnecessary: existing Mathlib instances
supply quasi-compactness and quasi-separatedness from noetherianity, and
`QuasiCompactCover.exists_hom` supplies the finite affine refinement.

All seven original proof-only imports were removed from the parent module.
The matrix theorem imports only the qcqs calculus and the small APIs its actual
proof uses. The gluing theorem has only the public imports required to state it;
its future proof will need the gluing/localization/tensor/Hom interfaces still
listed in its DAG plan. In particular, these four modules are no longer directly
imported by any delivered file:
`Sheaf.CategoryTheory.SiteModuleSheafGluing`,
`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`,
`Sheaf.CategoryTheory.ModulePullbackTensorIso`, and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`.
This import cleanup does not claim their mathematical gluing steps unnecessary.
No module is withdrawn. The repair also removes the duplicate local proofs of
`fp_iff_of_iso` and `fp_map` in both new proofs, plus the parent
`extendScalarsRegularIso` and `fp_extend`; the existing shared declarations
supply their results. The H4 repair additionally removes the matrix module's
private `regularRingIso` duplicate and uses the already-public
`CategoryTheory.Mod.regularIsoOfIsIso` through the existing import closure.
F3's private helper and its requested publication are not needed by this route.

Every removed original `proof_deps` edge is accounted for below. The parent no longer
uses these declarations directly; the indicated new nodes keep the required steps:

- `def-weil-finite-subextension-directed-set`: used in both new nodes.
- `def-weil-pbc-condensed-e-module-category`: used in both new nodes.
- `def-weil-pbc-proetale-covering`: used in both new nodes.
- `lem-weil-pbc-proetale-qcqs-fp-section-calculus`: used in both new nodes.
- `lem-pur-sheaf-hom-cover-gluing`: retained in the gluing plan.
- `lem-weil-pbc-ringed-topoi-module-pullback-tensor`: retained in the gluing plan.
- `lem-weil-pbc-site-module-sheaf-gluing`: retained in the gluing plan.
- `lem-weil-proetale-weakly-etale-localization`: retained in the gluing plan.
- `lem-weil-pbc-profinite-point-pullback`: pruned from this item's route.
- `lem-weil-pbc-quasi-separated-affine-cover-criterion`: pruned from this item's route.
- `def-weil-pbc-scheme-conventions`: pruned from this item's proof dependencies.

The removed `Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse` import is also
unnecessary in the delivered proofs: the coefficient-colimit API is already available
from the public coefficient imports. The second reading reuses
`Sheaf.Paper.RegularExtensionComparison` for its proved regular-module isomorphism and
naturality, removing the matrix module's duplicate construction and adjunction lemmas.

## Where the brief, the DAG or earlier work was wrong

The old plan made coefficient-ring identification on X a prerequisite. It is
unnecessary: the coefficient cocone on T remains a colimit after both inverse
images. The proved matrix theorem handles these precise rings directly.

The gluing interfaces are statements about `SheafOfModules`, whereas the item
uses internal `CategoryTheory.Mod` in abelian sheaves. They do not apply directly;
one must use the existing internal/sectionwise equivalence and prove its
pullback/tensor compatibility, or prove internal-module gluing directly. The remaining
node now cites the existing equivalence explicitly in its proof plan. No false statement or target-signature change was found. The returned version
repeated private helper theorems already present in the library; those helpers
must be made reusable in place instead of proved again. This repair does so.

H4 named a private helper whose public counterpart was already available:
`Mod.regularIsoOfIsIso` in `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod`.
The repair uses that existing public API instead of changing F3's visibility.
This deviation from the requested helper name is explicit in the change record.

## New nodes

- `lem-weil-pbc-condensed-local-presentation-matrices`, implemented and proved in
  `Sheaf.Paper.CondensedFinitePresentationMatrices`.
- `lem-weil-pbc-condensed-local-model-gluing`, the remaining named theorem in
  `Sheaf.Paper.CondensedLocalModelGluing`.

Both inherit the parent's chapter/unit and exact blueprint ancestry. Searches
found no equivalent imported blueprint nodes. Mathlib search records include the
actual unavailable LeanSearch responses, LeanFinder results and grep results.

Interface/addition record: `coord/changes/condensed-local-matrix-gluing.md`.

Additional repair records: `coord/changes/condensed-fp-shared-api.md` and
`coord/changes/condensed-regular-ring-iso-reuse.md`.

## Earlier second reading (a previous round; superseded)

1. **Visible declarations: pass.** Compared all four delivered modules with the shared
   repository. The original model theorem's signature is byte for byte identical.
   The only existing-module interface changes are removal of `private` from
   `fp_iff_of_iso`, `fp_map`, and `fp_extend`, exactly as declared in
   `coord/changes/condensed-fp-shared-api.md`; their statements and proofs are identical.
   The other two modules and their theorem statements are new. No definitions change.
2. **Proof and axioms: pass.** Compiled all four modules with `lcompile.py --all`.
   Scanned every delivered file for forbidden declarations and hidden holes; the sole
   `sorry` is the reported named gluing theorem. Scratch copies with `#print axioms`
   show only `propext`, `Classical.choice`, and `Quot.sound` for the matrix theorem and
   all three shared helpers. The parent additionally uses `sorryAx` through the gluing
   theorem, as reported. No data is chosen from an unproved existence theorem.
3. **Split statements and reuse: pass after repair.** Read both statements and their
   source arguments. A finite affine cover makes X quasi-compact; quasi-separatedness
   makes its pairwise and triple overlaps qcqs. Finite presentations make Hom commute
   with the required coefficient colimits. Empty covers force the empty base, and zero
   ranks use empty matrices, so these cases require no added assumptions. The gluing
   hole assumes supplied local models, and does not supply local finite presentation:
   it is the remaining descent/gluing subargument, strictly below the original item.
   Repeated LeanFinder, Loogle and grep searches with different queries. No equivalent
   whole descent/gluing theorem was found. Repository searches did find the proved
   `sectionModuleEquivalence` and `Mod.regularExtensionIso_naturality`; the proof plan
   now reuses the former, and the matrix proof reuses the latter. Completing all gluing
   compatibilities is substantial, so that named hole remains.
4. **Route, imports and pruning: pass after repair.** Read the argument top downward:
   simultaneous local matrices, enlargement and gluing, then finite-presentation
   transport. All added proof imports are private to the proof. Every removed old
   dependency edge is now listed above, distinguishing pruning from transfer into
   the new nodes. The unit `sk-thm-properbasechange` and its `realized` statement and
   three steps remain unchanged; this is a reduction below the unit's route.
5. **DAG: pass after repair.** Checked all three node Lean statements verbatim and
   checked each `proof_deps` against the union of the proof steps' `uses`. Only
   `proof`, `proof_deps`, and `proof_origin` change in the old node. Both new nodes
   have the required source, creation, blueprint ancestry, chapter/unit, search and
   Lean records. The matrix route now cites the regular-extension comparison, and
   the gluing route cites the existing module equivalence.

Changes in this second reading: replaced the duplicate regular-module construction
and adjunction naturality proof by the existing shared comparison; corrected the
claim that the internal/sectionwise equivalence still needs constructing; updated
the gluing docstring and both new proof plans; completed the removed-edge accounting.
No existing theorem signature, definition, or hole count changed.


## Second reading by A4

This is an independent reading of the repaired H4 sandbox, after the superseded
reading above. I read all four delivered Lean modules, all three node records,
the three change records, the current return, the unit and its blueprint source,
and the upstream TwoColimit module's (Obj) paragraph. The archived source path in
the nodes is absent on this machine; the corresponding live upstream module was
read instead. I also checked [Stacks 04TR](https://stacks.math.columbia.edu/tag/04TR),
[04TQ](https://stacks.math.columbia.edu/tag/04TQ), and
[03EL](https://stacks.math.columbia.edu/tag/03EL) for effective gluing, uniqueness
of glued maps, and the tensor-pullback comparison respectively.

1. **Visible declarations: pass.** Diffed every delivered module against the shared
   repository and checked the declaration tables. The original theorem's signature
   is byte for byte unchanged. In BoundedConstructibleExtendScalars, the entire
   diff removes only three `private` modifiers, as declared in the shared-API
   change record; signatures and proof bodies are unchanged. That module is still
   unclaimed. The two other modules are new. No definition or target changes.
   In particular Compatibility remains held by F3 and is absent from this delivery.
2. **Proof and axioms: pass.** Compiled all four files through `lcompile.py --all`,
   and recompiled the matrix file after import cleanup. The sole delivered `sorry`
   is exactly the whole proof of the public named gluing theorem. No forbidden
   declarations, hidden proof holes, or hollow definitions occur. Fresh scratch
   copies with `#print axioms` show only propext, Classical.choice and Quot.sound
   for the matrix theorem and all three shared helpers. The parent and gluing
   theorem additionally depend on sorryAx, exactly as reported. The H4 replacement
   uses the existing public `Mod.regularIsoOfIsIso eR.hom`: its inverse coefficient
   morphism is definitionally eR.inv and its regular-module target is precisely
   what fp_map requires. No data definition selects an arbitrary witness from an
   unproved existence theorem. Both unchanged direct consumers of the shared API
   were also compiled against the sandbox overlay.
3. **Split statements and reuse: pass.** The matrix theorem proves finite affine
   refinement, simultaneous descent of the finitely many entries, and the
   cokernel comparison. The remaining theorem takes those local models as input
   and asks only for enlargement and effective gluing; it is a strict remaining
   subargument, not a renamed version of the original statement. On pairwise and
   triple overlaps quasi-separatedness supplies quasi-compactness; pullback and
   scalar extension preserve the finite presentations needed for Hom continuity.
   Descend the overlap maps and their inverses and then their finitely many
   equations before gluing. Empty covers force an empty base; zero ranks are empty
   matrices; a one-member cover still requires its self-overlap descent datum.
   Repeated LeanFinder, Loogle and Mathlib grep searches with different wording,
   and repository searches, found no whole theorem already giving this descent.
   The ordinary-field subfield-model theorem and the Qbar finite-free refinement
   theorem have different objects and conclusions. Existing sectionModuleEquivalence,
   regularExtensionIso_naturality and regularIsoOfIsIso are reused rather than
   reconstructed. Finishing the remaining localization and cocycle compatibilities
   is substantial, so no further hole was closed in this reading.
4. **Route, imports and pruning: pass after cleanup.** Read the parent proof top
   downward: descend matrices, glue their cokernels, then transport finite
   presentation. All original public imports remain unchanged. Removed two
   redundant proof-only Mathlib imports from the new matrix module; it compiles
   without them. The No longer needed section accounts for every removed original
   proof dependency, distinguishing pruned edges from steps transferred into the
   new nodes. The unit's realized statement and all three steps remain unchanged.
   No whole module is withdrawn or claimed globally unreachable. This delivery
   closes one original hole and adds one lower hole: a decomposition, net zero.
5. **DAG and records: pass after documentation cleanup.** Checked the three Lean
   statement strings verbatim and verified each proof_deps is exactly the union
   of the proof steps' uses. The old node changes only proof, proof_deps and
   proof_origin. Both new nodes have the required source, creation, searches,
   blueprint ancestry, chapter/unit and Lean records. The matrix plan records
   the public-helper substitution and the gluing plan records the existing
   internal/sectionwise equivalence. Re-ran downstream.py --uses for all three
   exposed helpers; expanded the change record's Users table to include every
   downstream module, with current holders and unchanged semantics.

Changes in this reading: removed the redundant ForgetCorepresentable and Order.ULift
proof imports, completed the shared-API users table, updated the H4 change record
for that import cleanup, and appended this review. No signature, definition,
proof body, DAG route, or hole count changed. The public-helper H4 substitution
is accepted; publication of F3's private helper is unnecessary.
