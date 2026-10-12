## What changed

Repaired the inherited candidate decomposition of
`AlgebraicGeometry.Etale.resolutionSection_canonical_transfer` into its global and
open components. Each remaining obligation now has a separate new module:
`Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalGlobalTransfer` and
`Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalOpenTransfer`.
The item imports them privately and combines their conclusions by conjunction introduction.
Its existing signature, docstring and public import are preserved.

Replaced circular component DAG proof dependencies on the parent theorem with the
actual inverse-image, resolution, section-transfer and cohomology definitions and
exactness result. Added complete natural-language proof descriptions, self-contained
node statements, exact Lean signatures, fresh search records and the missing audit fields.
Removed inherited review metadata, which did not review these new nodes.
Updated the parent node's proof route to the two components. No unit step is bypassed.

## Proved and sorry left

Candidate hole closed: `AlgebraicGeometry.Etale.resolutionSection_canonical_transfer`
(node `lem-weil-pbc-etale-resolution-section-canonical-transfer`), by conjunction
introduction from the two obligations below. This is a decomposition, not a completed
mathematical proof. The second reading below supersedes the earlier cache-blocked verification: all delivered modules now compile.

Two holes added, both whole named public theorem proofs:

- `AlgebraicGeometry.Etale.resolutionSection_canonical_transfer_global`, node
  `lem-weil-pbc-etale-resolution-section-global-transfer`, in the new global module.
- `AlgebraicGeometry.Etale.resolutionSection_canonical_transfer_open`, node
  `lem-weil-pbc-etale-resolution-section-open-transfer`, in the new open module.

There are no sorries in definitions or private declarations. The candidate's net
hole change is one closed minus two added. The two obligations are strictly the global
and open parts of the original conjunction, respectively; neither restates the whole.

## No longer needed

No library module is claimed pruned. No original import was removed.
The parent no longer directly uses any of its six old proof dependencies:
`def-weil-pbc-cohomology-pullback`,
`def-weil-pbc-etale-open-object-cohomology-map`,
`def-weil-pbc-etale-resolution-section-canonical-comparison`,
`def-weil-pbc-etale-resolution-section-transfer`,
`def-weil-pbc-inverse-image`, and `prop-weil-pbc-inverse-image-exact`.
These are still needed by the component statements and mathematical proof plans;
none is claimed globally pruned. The parent now directly uses the two new component
nodes. No unit statement or realized step is removed.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox attempt put both obligations in the item module, omitted complete
proof descriptions, recorded their titles instead of Lean signatures, inherited irrelevant
review metadata and used the parent theorem as a proof dependency of both obligations.
These issues are repaired in the candidate, but it remains uncompiled.

The shared published Lean cache still lacks
`Sheaf/AlgebraicGeometry/EtaleResolutionSectionCanonicalComparison.olean`.
The initial delivery dry run failed at this import. After repair, both `lcompile.py --all`
and another `deliver3.py --no-push` failed at the same import in the global component.
No Lean proof goal or preflight check was reached. Under roles/worker.md section 2.2,
missing compiled declarations must wait for a green publication; dependencies were not
copied or rebuilt to bypass that rule. No delivery was pushed.

LeanFinder and Loogle searches succeeded; LeanSearch returned Internal Server Error.
The cited local Stacks TeX files are absent on this machine. The four cited tag pages
were read at https://stacks.math.columbia.edu/tag/01F8,
https://stacks.math.columbia.edu/tag/01FB, https://stacks.math.columbia.edu/tag/03F3,
and https://stacks.math.columbia.edu/tag/0A50. They supply the resolution-functoriality
and localization arguments; the specific Lean coefficient transports still require proof.
Edge-case review found no extra hypothesis needed for degree zero, empty opens,
zero coefficients or identity morphisms. Existing signatures were checked by the
project declaration parser and Lean line lengths checked mechanically.

## New nodes

`lem-weil-pbc-etale-resolution-section-global-transfer` records only the global
component of the original theorem, with its constant-sheaf cocycle calculation.
It is stated in `EtaleResolutionSectionCanonicalGlobalTransfer.lean`.

`lem-weil-pbc-etale-resolution-section-open-transfer` records only the open component,
with its free-representable identity generator and coefficient transport.
It is stated in `EtaleResolutionSectionCanonicalOpenTransfer.lean`.

No change record is needed: no existing signature, definition or public import changes.

Retry verification (2026-10-13, following the second blocked attempt): read the preserved
three modules and the stage-3 contract. Both `lcompile.py --all` and
`deliver3.py P2 Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalTransfer --no-push`
again exited 1 before elaboration because the published cache lacks
`EtaleResolutionSectionCanonicalComparison.olean`. The dry run explicitly reported
"COMPILE FAILED (local), nothing pushed". The preserved candidate remains uncompiled;
no proof or node changes were made during this retry. The dependency was not rebuilt
or duplicated, as required by roles/worker.md section 2.2.

Retry verification (2026-10-13, following the third blocked attempt): the required
cache artifact remains absent. Both the permitted `lcompile.py --all` command and
`deliver3.py P2 Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalTransfer --no-push`
exited 1 at the global component's line 6 import, before elaborating any declaration.
The dry run reported `COMPILE FAILED (local), nothing pushed`. The three Lean modules
and three DAG node files are preserved unchanged. No dependency was rebuilt or copied
into the sandbox to bypass roles/worker.md section 2.2. A green cache publication
containing `Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison` is
required before this candidate can be compiled and assessed for READY.


## Second reading by P2

1. Interface preservation: PASS. Read `diff -u` against the repository version.
   The existing theorem signature and docstring are byte for byte unchanged;
   only two private proof imports and conjunction introduction were added.
   The unexpected sandbox copy of `EtaleResolutionSectionCanonicalComparison`
   was byte for byte identical to the repository and was removed, together with
   its sandbox-built artifacts, so verification uses the published green cache.
   No definition, target, public import or other existing declaration changes.
2. Proof and trust: all four initially present files compiled without errors or
   warnings. Rechecking the actual three-file delivery after removal of the
   redundant comparison copy is recorded below. The only two `sorry`s are the
   named public component theorems, each an entire `by sorry` proof, listed above.
   No forbidden declaration or hollow definition occurs. The parent proof is
   conjunction introduction from those strictly smaller conclusions; it remains
   dependent on `sorryAx` and is a decomposition, not a completed target proof.
3. Split statements: PASS on mathematical reading. Each has exactly the parent's
   hypotheses and only one of its two conclusions. Checked degree zero, identity
   morphisms, empty opens/schemes and zero coefficients: the cycle, adjunction and
   augmentation argument still applies, with no extra hypotheses. Read the real
   `cohomologyMap`, `openCohomologyPullback`, free-sheaf unit, object-cohomology
   map and section-transfer constructions. Each new module has a source and a
   complete cocycle/derived-category proof description and a matching new node.
   Read Stacks 01F8, 01FB, 03F3 and 0A50 on their tag pages. The first two give
   the resolution-functoriality pattern (for ringed spaces); 03F3 gives the site
   localization argument, and 0A50 uses resolution section complexes. The
   etale coefficient transports are the stated agent-written specialization.
   Neither component merely renames the full conjunction. Fresh searches with
   different wording used LeanFinder, Loogle and msearch grep; repository rg
   searched transfer and homology naturality. Mathlib's
   `Abelian.Ext.mapExactFunctor_hom` and `InjectiveResolution.extMk_hom` give
   generic derived-category expansions, but do not identify the prescribed
   etale section and coefficient maps. Neither remaining hole has a direct
   library proof found that could be substituted in a few minutes.
4. Route and pruning: PASS. Read `dag/units/sk-thm-p1.json` `realized`; the split
   is below its named steps and keeps both the global and open transfer route.
   The single public comparison import supplies every component signature;
   the two new private imports supply exactly the parent's proof. No removable
   proof import remains. Expanded `No longer needed` to enumerate every old
   direct proof dependency, distinguishing their continued use below the split
   from global pruning. Net hole change is -1 (one closed, two added).
5. DAG agreement: PASS. Parent `proof_deps` is precisely the two called theorem
   nodes; the new nodes' proof dependencies are the union of their documented
   mathematical steps, not a circular dependency on the parent. Checked their
   exact Lean signatures, source, statement dependencies, proof origin, three
   successful search kinds, status, creation, blueprint provenance, chapter,
   unit and Lean records against brief-stage3 section 3. No unit record changes.

Second-reading changes: removed the redundant unchanged comparison module and
its local compiled artifacts; corrected stale compilation status and completed
the list of old direct dependencies in this report. The Lean proof and new
component statements did not need rewriting. Earlier missing-cache reports
above are historical; the shared comparison artifact is now published.


Local verification: the declaration parser reports no changed existing statement;
the item closes exactly `AlgebraicGeometry.Etale.resolutionSection_canonical_transfer`
and adds no local theorem holes. Both new modules contain exactly their one named
hole. All delivered Lean lines satisfy the 100-character limit, and every node's
`proof_deps` equals the union of its proof steps' `uses`. A scratch copy compiled
with `#print axioms` for the parent and both components: each lists exactly
`propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; no other axiom.
The scratch copy was removed from the sandbox after this check.

Final dry run: `deliver3.py P2 Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalTransfer --no-push` printed OK (commit `9298cefd28`). It compiled the actual three-file delivery against the shared comparison cache and passed preflight. Review class is CODEX because it adds two modules, public component declarations, nodes and their named open proofs. This delivery decomposes one item hole into two; it proves no component independently and claims no completed target or globally pruned module.
