## What changed

Proved `AlgebraicGeometry.Scheme.Modules.FlatBaseChangeOpenChoices.targetClass_restriction`
without changing its signature, visibility, or docstring. Its only added import is the
proof-only `Sheaf.AlgebraicGeometry.RestrictedResolutionCohomology`.

The new module proves `AlgebraicGeometry.Scheme.Modules.restrictedResolution_cohomology`:
the canonical cohomology restriction, transported through the source and restricted
resolution comparisons, is the homology map of degreewise restriction of sections.
The proof uses the existing `moduleCohomologyFMap_independent`, the source-library
restriction limit-preservation instance, and the right-adjoint injective-preservation lemma.
For an open inclusion the pushed restricted resolution already has injective terms,
so the cohomology-map data uses lambda equal to the identity. No injective replacement
or newly chosen resolution is needed.

In the item module, two proved private helpers establish evaluation-homology/section-class
naturality and combine that square with the raw comparison. The public theorem then
uses naturality of the inverse derived comparison, evaluates at eta, and applies
`TopCat.Presheaf.germ_res_apply`. Both affected DAG nodes record this actual proof route.

The new statement was checked on empty and top opens, zero modules, and degree zero:
it is an equality of the same canonical morphisms, obtained by functoriality and
inverse identities. These cases need no additional hypotheses. For the original
statement an empty V has no witness hy.

Repair of the returned timeout: profiling the prior local transparency repair
showed that the final `exact hg.symm.trans ht` spent 35.2 seconds unfolding
`resolutionSectionClass`. The new repair additionally keeps that definition
`[local irreducible]` throughout this file. The private section-class calculation
now uses `unfold resolutionSectionClass` and `dsimp only` to open it explicitly;
every other comparison keeps the map named. The final exact took 0.31 seconds,
and the profiled target compiled in 28.8 seconds. Profiling options are removed
from the delivered source. The final two-module compile took 35.4 seconds for
RestrictedResolutionCohomology and 38.9 seconds for TargetSectionClassRestriction,
with no errors or warnings. The types, constructed bodies and public interfaces
are identical, and no reducibility attribute is exported.

## Proved and sorry left

Closed the item's sole original hole:
`AlgebraicGeometry.Scheme.Modules.FlatBaseChangeOpenChoices.targetClass_restriction`
(node `lem-weil-pbc-target-section-class-restriction`).

Also proved the new
`AlgebraicGeometry.Scheme.Modules.restrictedResolution_cohomology`
(node `lem-weil-pbc-restricted-resolution-cohomology`).

Holes closed: 1. Holes added: 0. No declaration in either delivered module contains
`sorry`; all private helpers are proved. This is a proof from the existing named
library declarations, including the recorded cohomology-map independence theorem;
it is not a claim that the entire transitive dependency closure is already axiom-free.

## No longer needed

Removed four direct proof imports from the original module:
`Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices`,
`Sheaf.AlgebraicGeometry.ModuleCohomologyFMap`,
`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial`, and
`Sheaf.AlgebraicGeometry.PushforwardInjectivesSectionsQuasiIso`.
Their needed declarations remain available transitively through the original public
import and the new proof-only raw-comparison import. The original public import
supplies `targetClass`, which occurs in the unchanged statement. Every new proof
import is used. No whole module is claimed pruned from the targets' import closure.

The original node no longer needs a direct proof dependency on
`lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso`
(module `Sheaf.AlgebraicGeometry.PushforwardInjectivesSectionsQuasiIso`): the explicit
restriction calculation uses lambda equal to the identity. This node/module remains
a transitive dependency through the existing definition of moduleCohomologyFMap,
so this delivery does not claim that its module can leave the queue.

`def-weil-pbc-module-cohomology-fmap` is no longer a direct proof dependency of
the item; it is used by the new raw-comparison theorem and remains transitively needed.

`lem-weil-pbc-module-cohomology-fmap-functorial` is now used by the new raw-comparison
node rather than cited directly by the item. Its module remains needed. The definitions
of the open choices, cohomology map, and section class, and the derived-resolution
comparison remain needed. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false or unusable statement was found. The DAG's extra injective replacement is
unnecessary for this open-inclusion restriction: restriction preserves finite limits,
so its right adjoint preserves injectives. The proof uses this shorter specialization.

The source equation for cohomology restriction at Tag 01E2 is numbered the project server;
the new docstring and node use that number. The existing item docstring was preserved.

Searches: LeanSearch was attempted and returned Internal Server Error; LeanFinder returned
8 naturality-related hits but no restriction/resolution comparison; Loogle returned
12 homology-comparison hits; grep returned germ-restriction lemmas and no Mathlib
resolutionSectionClass. Local searches in both library roots found no existing raw
comparison. Mathlib's `NatTrans.app_homology` and `germ_res_apply` were read and used.

## New nodes

`lem-weil-pbc-restricted-resolution-cohomology` is a proved general tool for steps 1–2
of the item's argument. It compares raw cohomology of section complexes, before theta,
the higher-direct-image comparison, or germs. Its module is
`lean/Sheaf/AlgebraicGeometry/RestrictedResolutionCohomology.lean`.
The node includes the statement, complete proof steps, dependencies, source, searches,
and verbatim Lean signature. Change record: coord/changes/sectionCohomologyTheta-transparency.md.


Repair B9/G1 (2026-10-13): performed the required whole-blueprint search in the
repository, across every node carrying `blueprint_kind`, including chapters outside
the targets' reach. Actual queries and results:

- `python3 tools/blueprint_refs.py search restriction cohomology`: 29 blueprint nodes match 'restriction cohomology'.
  Returned IDs: `def-pc-perfect-complex`, `def-sf-fullcd-class`, `def-sp-injective-resolutions`, `def-weil-completed-integral-coefficients`, `def-weil-derived-direct-image`, `def-weil-finite-torsion-constructibility`, `def-weil-full-cohomological-dimension`, `def-weil-pbc-constructible-complexes`, `def-weil-pbc-cover-cech`, `def-weil-pbc-direct-image`, `def-weil-pbc-etale-sheaves`, `def-weil-pbc-extension-by-zero`, `lem-pc-projective-space-canonical`, `lem-pur-support-restriction-triangle`, `lem-sc-zero-generic-acyclic`, `lem-sf-proetale-constructible-origin`, `lem-weil-pbc-derived-cohomology-continuity`, `lem-weil-pbc-reconstruction-uniform-tower`, `lemma-weil-pbc-h1-torsor-comparison`, `lemma-weil-pbc-injective-restriction-acyclicity`, `lemma-weil-pbc-p1-exchange-geometric-stalk`, `prop-finite-compact-support-constructibility`, `prop-pur-gm-relative-kummer`, `prop-weil-pbc-restriction-direct-image`, `prop-weil-pbc-strict-henselization-stalk-formula`, `thm-pur-affine-line-orientation`, `thm-sf-kunneth-relative`, `thm-weil-pbc-stein-inputs`, `zero-dimensional-etale-cohomology-rest`.
- `python3 tools/blueprint_refs.py search restricted resolution`: 0 blueprint nodes match 'restricted resolution'.
- `python3 tools/blueprint_refs.py search sections resolution`: 8 blueprint nodes match 'sections resolution'.
  Returned IDs: `d-real-cohom`, `def-kun-rgamma-unbounded`, `def-pur-support-triangle`, `def-pur-supported-exterior-product`, `def-sc-zariski-cohomology`, `def-weil-pbc-etale-cohomology`, `lem-weil-pbc-direct-image-preserves-injectives`, `lem-weil-pbc-hypercover-free-resolution`.
- `python3 tools/blueprint_refs.py search 01E2`: 0 blueprint nodes match '01E2'.
- `python3 tools/blueprint_refs.py search 01FB`: 2 blueprint nodes match '01FB'.
  Returned IDs: `lem-sc-structure-sheaf-cohomology-pullback-composition`, `lem-sc-structure-sheaf-cohomology-pullback-identity`.

No returned blueprint statement is the raw restriction/resolution comparison.
The cohomology definitions define the groups, `def-sp-injective-resolutions`
defines resolutions, and the other hits concern etale/pro-etale coefficients,
support triangles, or geometric-stalk comparisons. In particular, the two 01FB
hits assert identity and composition for structure-sheaf pullback; neither states
the fixed-resolution section restriction equation. Read the full statements of
`def-sc-zariski-cohomology`, `def-sp-injective-resolutions`,
`def-weil-derived-direct-image`, `def-weil-pbc-etale-cohomology`,
`lemma-weil-pbc-p1-exchange-geometric-stalk`,
`lemma-weil-pbc-injective-restriction-acyclicity`,
`prop-weil-pbc-strict-henselization-stalk-formula`, and both 01FB hits to check
these distinctions. The new node therefore records `blueprint.same_as: []`.
This repairs the omitted field and search record; no Lean source changed.

## Forced adaptations

None. The repair preserves every existing signature, visibility, definition body,
and importer-visible attribute. The new raw-comparison module and its target importer
are compiled together in the same delivery. The public target signature is unchanged;
the target's immediate importer, `LocalDirectImageStalkClassRestriction`, is checked
unchanged against the complete overlay. No signature adaptation is necessary for
return points 2 and 3.

Return point 1 is repaired by the new local irreducibility of
resolutionSectionClass and explicit unfolding only in the calculation that needs
its body. This is a repair beyond the previous local theta/fmap attributes;
it does not split the file or proof and does not raise the timeout.

Return point 2: RestrictedResolutionCohomology is compiled first, then its actual
importer TargetSectionClassRestriction is compiled against that exact sandbox
output. Both are included in the same delivery, with unchanged public signatures.

Return point 3: TargetSectionClassRestriction is rebuilt against the complete
changed-dependency overlay; the immediate importer
LocalDirectImageStalkClassRestriction compiled unchanged against that overlay in
2.9 seconds with no errors or warnings.
The local attributes have no importer-visible effect. No consumer adaptation is
required; no unheld module is changed.

## Earlier second reading (a previous round; superseded)

1. Interface preservation: PASS. Compared the delivered item with the repository
   using diff and compared the full existing theorem signature byte for byte.
   The signature, visibility and docstring are unchanged. No existing definition
   body changes. The added item import is proof-only; all three irreducibility
   attributes are local. Only the two reported Lean modules are delivered.
2. Kernel proof and compilation: PASS. Independently compiled the complete set in
   import order with lcompile.py: RestrictedResolutionCohomology 26.5 s and
   TargetSectionClassRestriction 32.4 s, no errors or warnings. Neither file has
   sorry, axiom, unsafe, opaque, implemented_by or extern. A scratch module with
   #print axioms for restrictedResolution_cohomology and targetClass_restriction
   reports exactly propext, Classical.choice and Quot.sound for both, without
   sorryAx. The immediate importer LocalDirectImageStalkClassRestriction compiled
   unchanged against this overlay in 3.1 s. The only choice newly written is in
   a proof identifying the existing canonical map with explicit map data; no
   definition or arbitrary data witness is added.
3. New statements: PASS. No unproved statement is split off. Read the new proved
   raw-cohomology theorem and its complete docstring argument, checking the
   augmentation lift, injective preservation, pinned section components and
   inverse cancellation. It is strictly the raw-comparison part of the argument,
   before theta and germs, rather than a renamed target. Empty/top opens, zero
   modules and degree zero use the same naturality and inverse identities;
   the original empty-open germ case has no hy. Independently searched with
   LeanFinder for restriction computed by sections of a restricted injective
   resolution, Loogle for app_homology, and Mathlib grep for restrict/homology
   and cohomology/restriction. Read nearby BasicPropertiesRestriction and
   HigherDirectImageOpenRestriction; neither pins this raw map. Library searches
   in both roots found no duplicate. Checked Stacks Tags 01E2 and 01FB against
   the stated restriction and augmented-lift construction.
4. Route and pruning: PASS. The raw comparison uses already proved independence
   and the source restriction-limit instance, with lambda the identity. The
   remaining proof is evaluation-homology naturality, theta naturality, derived
   comparison naturality and germ_res_apply. All imports have a statement or
   proof use; the new public import supplies RestrictedResolutionSections.
   Every old proof dependency removed from the item is listed under No longer
   needed, including its continuing transitive use. No whole module is pruned.
   Read sk-thm-p1.json realized: no removed dependency realizes a unit statement
   or step, and the unit route is preserved.
5. DAG agreement: PASS. The existing node changes only proof, proof_deps and
   proof_origin. Each dependency is used by its recorded step. The new node has
   source, complete proof steps, their dependency union, proof origin, searches,
   split status, creation/blueprint/chapter/unit records and the verbatim Lean
   signature. It records the actual identity-lambda proof. The change record
   describes the local transparency repair and the checked unchanged importer.

Second reading changed only this report: appended the independent checks and
recorded the stronger axiom result. No Lean or DAG repair was necessary.
Holes closed: targetClass_restriction (1 original hole); holes added: none.

## Second reading by Y3

1. Interface preservation: PASS. Independently diffed the item against the repository
   and compared the existing target signature byte for byte. Its type, visibility
   and docstring are unchanged. No existing definition body is changed. The new
   import is proof-only; all irreducibility attributes are local.
2. Proof integrity: PASS. Read both complete proofs, including the augmentation lift,
   identity lambda, degreewise restriction component and inverse cancellation.
   The delivered set compiled cleanly in import order (26.6 s and 32.2 s).
   Neither source contains sorry, axiom, unsafe, opaque, implemented_by or extern.
   No new definition or arbitrary data witness is added; the Classical.choice in
   the new theorem merely unfolds the existing canonical cohomology map in a proof.
3. New statements: PASS. There are no unproved split-off statements. The new proved
   comparison is strictly the raw section-complex part, before theta and germs.
   Checked empty/top opens, zero modules and degree zero: the augmentation and
   inverse identities need no nonemptiness or positive-degree assumption. The
   original empty V case has no hy. Independently ran LeanFinder with the query
   "cohomology pullback open immersion computed by restriction on sections injective
   complex" (8 restriction ingredients); Loogle "homologyMap" (12 homology
   ingredients); Mathlib grep "moduleCohomologyRestriction" (0 hits), and local
   rg across both library roots. Read BasicPropertiesRestriction and
   HigherDirectImageOpenRestriction: neither states the pinned raw comparison.
   Read Stacks 01E2 and 01FB and Mathlib app_homology and germ_res_apply.
4. Route and pruning: PASS after report repair. The actual proof uses independence
   of cohomology-map choices and injective preservation to take lambda equal to
   identity, then evaluation-homology, theta and derived-comparison naturality.
   Every import supplies a signature or proof ingredient. Checked sk-thm-p1.json
   realized: none of the removed direct dependencies realizes a unit step.
   All three old proof dependencies removed from the node are reported, including
   their continuing transitive use. Corrected the report's false assertion that
   no imports were removed by listing all four removed direct proof imports.
   No whole module is pruned from the target closure.
5. DAG agreement: PASS. The existing node changes only proof, proof_deps and
   proof_origin. Both dependency lists equal the union of their proof steps.
   The new node has the required source, searches, blueprint, creation, chapter,
   unit and Lean fields; its signature matches the new theorem verbatim.
   Its docstring describes the actual lift and section-component calculation.

Second reading changed only this report, correcting the direct-import pruning list
and recording this independent review. No Lean or DAG repair was necessary.
Holes closed: targetClass_restriction (1 original hole). Holes added: none.

Independent scratch-copy axiom checks report exactly propext, Classical.choice,
and Quot.sound for both public theorems, with no sorryAx. The unchanged immediate
importer LocalDirectImageStalkClassRestriction compiled against these exact scratch
outputs in 11.0 s, without errors or warnings. Scratch copies are not delivered.
