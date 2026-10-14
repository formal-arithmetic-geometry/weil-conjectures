## What changed

Restored the supplied tested direct proof in
`lean/Sheaf/AlgebraicGeometry/PicardScalarCechExternalCup.lean`.
`picardScalarCech_externalCup_core` now takes hUc and hVc and proves compatibility
by cyclesMap_i, homologyπ_naturality, picardModuleCech_externalPairing and
scalarExternalCup_moduleComparison. The enclosing `picardScalarCech_externalCup`
keeps its signature and passes its existing cover equalities to the corrected core.
A small private equality-congruence lemma is proved locally. No definitions or other
modules are changed.

Added plain proof imports: Sheaf.AlgebraicGeometry.PicardExternalCechCupBidegree,
Sheaf.AlgebraicGeometry.PicardModuleCechExternalPairing,
Sheaf.AlgebraicGeometry.ScalarExternalCupModuleComparison, and
Sheaf.Paper.ModuleCohomologyCupProduct. Both original public imports remain.
The two existing node copies record the actual route and the corrected core statement.
Change record: `coord/changes/picardScalarCech_externalCup_core-cover-repair.md`.

The replacement compiled locally in 11.6 seconds. The temporary print command used
for that check is removed from the delivery. Final validation is deliver3.py --no-push.
The ordinary cup is chosen from exists_unique_moduleCupProduct; its characterization
determines it uniquely.

## Proved and sorry left

Closed the one local hole:
`AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup_core`
(node `lem-sc-picard-scalar-cech-external-cup-core`), after the mandatory statement
repair. The invalid cover-free statement is corrected, not claimed proved.
The unchanged enclosing theorem
`AlgebraicGeometry.Scheme.Modules.picardScalarCech_externalCup`
(node `lem-sc-picard-scalar-cech-external-cup`) now applies the corrected proof.
The private `moduleCup_congr` is fully proved.
No sorry remains in the delivered module. No hole is added or split off.

This is a proof from existing library comparison theorems. It does not close all
upstream theory: #print axioms for the core still includes sorryAx inherited from
unfinished existing ordinary/scalar compatibility primitives. The delivery does
not claim these primitives are finished and introduces none of its own.

## No longer needed

Removed the unused plain import `Sheaf.Paper.CechCupPullbackCompat` and its direct
DAG dependency `lem-sc-picard-cech-cup-pullback-compat`. The ordinary-pairing route
does not need a direct dependency on `def-sc-field-linear-module-cohomology-operations`
for the core proof; its definitions remain needed by the statement. The outer node
now depends only on the corrected core; the core records its six actual dependencies.

The following 16 project modules leave this item's transitive import closure, with
their attached nodes listed. This prunes this branch; it does not assert that every
module becomes unreachable from all five targets:

- `Sheaf.AlgebraicGeometry.BasicPropertiesDegreeZero` (nodes: `lem-weil-pbc-module-cohomology-fmap-basic-degree-zero`)
- `Sheaf.AlgebraicGeometry.BasicPropertiesIdentity` (nodes: `lem-weil-pbc-module-cohomology-fmap-basic-identity`)
- `Sheaf.AlgebraicGeometry.BasicPropertiesLinearity` (nodes: `lem-weil-pbc-module-cohomology-fmap-basic-linearity`)
- `Sheaf.AlgebraicGeometry.BasicPropertiesRestriction` (nodes: `lem-weil-pbc-module-cohomology-fmap-basic-restriction`)
- `Sheaf.AlgebraicGeometry.EtaleTensorSections` (nodes: `lem-sc-etale-qcoherent-presheaf-functorial`)
- `Sheaf.AlgebraicGeometry.IdentityResolutionHomology` (nodes: `lem-weil-pbc-module-cohomology-fmap-identity-resolution-homology`)
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties` (nodes: `lem-weil-pbc-module-cohomology-fmap-basic-properties`)
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapCompData` (nodes: `lem-weil-pbc-module-cohomology-fmap-comp-data`)
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapComparison` (nodes: `lem-weil-pbc-module-cohomology-fmap-comparison`)
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapDataLinearity` (nodes: `lem-weil-pbc-module-cohomology-fmap-data-linearity`)
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial` (nodes: `lem-weil-pbc-module-cohomology-fmap-functorial`)
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapSemilinear` (nodes: `lem-weil-pbc-module-cohomology-fmap-semilinear-lift`)
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapZeroAugmentation` (nodes: `lem-weil-pbc-module-cohomology-fmap-zero-augmentation`)
- `Sheaf.AlgebraicGeometry.RestrictionNaturality` (nodes: `lem-weil-pbc-module-cohomology-fmap-target-iso-naturality`)
- `Sheaf.Paper.CechCupPullbackCompat` (nodes: `lem-sc-picard-cech-cup-pullback-compat`)
- `Sheaf.Paper.CechCupResolutionRepresentatives` (nodes: `lem-sc-cech-cup-resolution-representatives`)

Mathlib.CategoryTheory.Adjunction.CompositionIso also leaves this item's closure.
No PicardScalarExternalCocycleComparison module is introduced or imported; the
baseline has no live Lean use of that helper. No DAG nodes or Lean files are deleted.
The unit record sk-prop-av-cube has no realized nodes for this compatibility glue;
the unit and chapter statements and routes are unchanged.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (baseline, repaired): the core explicitly omitted cover equalities,
while its public enclosing theorem already supplied them. Arbitrary comparison
witnesses need not agree outside a noncover. The corrected P¹ skyscraper counterexample
and the invalidity of the earlier Spec(k×k) example are recorded in the change record.
No geometric counterexample is claimed formalized in Lean.

The baseline DAG describes redoing the refinement and scalar-resolution comparison
theory here. The existing ordinary pairing and scalar/module bridge supply those
steps; the supplied tested direct route compiles against this snapshot. Searches:
LeanFinder found only unrelated sheaf/group-cohomology results, Loogle found
HomologicalComplex.homologyπ_naturality, and local rg found the exact two library
comparison theorems. The source files under literature/stacks-project are absent on
this clone; the official [01FD](https://stacks.math.columbia.edu/tag/01FD),
[0FKV](https://stacks.math.columbia.edu/tag/0FKV),
[07MB](https://stacks.math.columbia.edu/tag/07MB), and
[0BED](https://stacks.math.columbia.edu/tag/0BED) pages were read instead.

Statement correction: the core gains exactly the two cover equalities, with no
change to its conclusion. The baseline DAG has no stmt_deps/proof_deps citer of the
core; the module-cup node mentions it only as blueprint provenance. Accordingly,
statement_change.citers is empty. The outer node gains the corrected core as its
actual proof dependency. The sole Lean call is adapted in the same file, and every
external caller of the public theorem remains valid.

Ownership note: the dispatcher brief assigns this item to K4, while this clone's
cached claim names XR271e7d0db684643a. Only the assigned item's Lean module is edited;
normal delivery checks will use the fetched current state.


## Second reading by K4

1. **Interfaces and statement repair — pass.** Compared the entire delivered Lean
   module with the repository, and compared both node signatures with the file.
   The only changed existing signature is `picardScalarCech_externalCup_core`:
   exactly `hUc : iSup U = ⊤` and `hVc : iSup V = ⊤` are added, as declared in
   `coord/changes/picardScalarCech_externalCup_core-cover-repair.md`. All other
   binders and its conclusion are unchanged; the public enclosing theorem has its
   original byte-for-byte signature. No definition changes. Read
   IsModuleCechComparison's all-resolutions equation: without a cover its alpha
   need not be injective on cohomology. The recorded P¹ skyscraper example exploits
   precisely that freedom: restriction keeps only the (x0,x0) component, while the
   product of the two factor extensions has zero on the other three components.
   All three global rings are k, so these extensions are module-linear. This is
   a sound informal counterexample; it is not certified in Lean. Read official
   [01FD](https://stacks.math.columbia.edu/tag/01FD),
   [0FKV](https://stacks.math.columbia.edu/tag/0FKV),
   [07MB](https://stacks.math.columbia.edu/tag/07MB), and
   [0BED](https://stacks.math.columbia.edu/tag/0BED): the first two require covers,
   and the latter's external map is pullback followed by cup. No claim of a
   Künneth isomorphism is made here. Read-only downstream analysis and `rg` find
   only the enclosing theorem calling the core; its call passes the existing
   equalities. No external consumer or target statement needs adaptation.

2. **Proof and axioms — pass relative to the existing unfinished library.**
   Independently compiled the delivered module cleanly in 12.3 seconds, then a
   scratch copy with `#print axioms` for both public theorems and the private
   helper. Both public theorems use only propext, Classical.choice, Quot.sound,
   and inherited sorryAx; the helper uses only propext and Quot.sound. Separate
   prints confirm sorryAx already occurs in picardModuleCech_externalPairing,
   scalarExternalCup_moduleComparison, and exists_unique_moduleCupProduct.
   No sorry or forbidden trust escape occurs in this module. Read the equality
   chain: cyclesMap_i proves ht, homologyπ_naturality proves hclass, heX/heY/heP
   supply the ordinary comparisons, and the two comparison theorems give the
   final equality with the correct orientation. Eliminating p+q=n makes the
   original cast reflexive, without changing the degree. The cup is obtained
   from unique existence, whose characterization determines the whole bilinear
   map; no arbitrary unproved object is put into a definition.

3. **Split-off statements — pass.** There are no new public statements, nodes,
   or holes. The proved private congruence helper is elementary equality
   substitution and has no mathematical side conditions. The repaired theorem
   handles p=q=0 without a sign, zero inputs by linearity, and empty index sets
   when they cover the empty scheme; no nonempty-index hypothesis was added.
   Read the existing ordinary-pairing and scalar-comparison signatures, including
   their expanded predicates, and verified they give exactly the classes used.
   Independently searched Loogle for HomologicalComplex.cyclesMap_i and local rg
   for the ordinary pairing and scalar/module bridge. No new restatement hides
   this item, and there is no split-off theorem to close.

4. **Top-down route, imports, and pruning — pass with report correction.**
   The proof uses the existing comparison results and Mathlib's two homological
   naturality identities directly. The two public imports supply the theorem's
   predicates and coefficient objects. All four added imports are plain and
   used only in the proof. Checked old proof_deps against the report: the direct
   pullback-compatibility node is bypassed, while field-linear operations remain
   in the statement closure. Recomputed both import closures on this snapshot:
   16 project modules and Mathlib.CategoryTheory.Adjunction.CompositionIso leave
   this branch. Eleven entries in the worker's 27-module list remain reachable
   through the newly landed comparison implementations, so I removed those
   entries and corrected the count. This is branch pruning, not a whole-target
   reachability claim. Read dag/units/sk-prop-av-cube.json: its statement and
   single cube step are unchanged, and neither item node is realized there.
   The argument remains the prescribed external pullback/cup comparison.

5. **DAG and Lean agreement — pass.** The core's three steps match the bidegree
   and cycle transport, ordinary pairing, and scalar witness substitutions in
   the proof. Its six proof_deps are exactly the union of those steps' uses.
   The outer node has the core as its single proof dependency and applies it.
   Both lean.statement fields match their source signatures verbatim; the
   statement_change records the old cover-free statement, repair, and old route.
   There were no baseline statement/proof citers of the core; the module-cup
   node's mention is blueprint provenance, not a dependency. Traversed the
   delivered proof-dependency closure and found no cycle. No new node metadata
   is required, and no node is deleted.

**Second-reader changes:** corrected only the stale branch-pruning list and its
count, and appended this reading. The correct Lean proof and node records are
left intact. One local hole is closed after the declared statement repair;
zero holes are added and zero statements are split off. The original false
cover-free assertion is not claimed proved. Final delivery validation follows.
