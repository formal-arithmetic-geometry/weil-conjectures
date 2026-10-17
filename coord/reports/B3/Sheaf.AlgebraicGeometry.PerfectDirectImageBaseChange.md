## What changed

Retired `Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange` as a declaration-free public
re-export of `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectBaseChange`.
Its original three public imports are preserved for existing import-only consumers.
Change record: `coord/changes/PerfectDirectImageBaseChange-source-import.md`.

Adapted every actual user in the same delivery, without changing any caller signature:

- `PerfectCohomologyFromGeometric`, `PicardDerivedFibreResidueModelData`,
  `PicardH1CommonMinimalModel`, and `ProperFlatStructureSheafStalkSurjective` use
  `properFlat_single_derivedDirectImage_perfect` for perfectness.
- `PicardDirectImageFibreCohomologyNegative` and `PicardDirectImageFibreCohomologyZero`
  use `exists_isIso_canonicalModuleBaseChange_of_isFlatOver` to obtain the comparison used
  only in their proofs, with exactly the same source and target.
- `PicardFiberDirectImageRankConstructible` uses both existing APIs.
- `PicardRankMatchDerivedTruncationData` uses the perfectness-only theorem and proves
  invertibility of the particular rank-matching comparison by the existing canonical affine
  comparison, affine locality, and detection on open restrictions. It does not substitute an
  unrelated isomorphism into the mate equation.
- `ProperFlatImageGlobalHomBaseChangeIso` imports the existing private localization-transport
  and zero-module finite-presentation helpers from their other existing modules instead of
  the retiring module. Its proof body and statement remain unchanged.

The eight caller nodes' proof routes/dependencies now name those existing APIs. The item node
keeps its statement and source-library attachment, while recording the actual derived reductions
now performed in callers. No new theorem, definition or node is introduced.

## Proved and sorry left

Holes closed: **0 of 0** in the item. Holes added: **0** anywhere. Split off: **0**.
This is the assigned duplicate/interface repair, not a new proof of a formerly holed theorem.
The removed theorem is `AlgebraicGeometry.perfect_derivedDirectImage_baseChange`; it already
had no local sorry, although it depended on imported open results. The source theorem
`AlgebraicGeometry.Scheme.Modules.perfect_and_baseChange_cechModuleComplex_of_isProper`
is re-exported, not reproved. All nine adapted consumer modules remain locally sorry-free.
The item contains no declarations and no sorry; no proof or data is replaced by a hole.
Existing imported open statements remain permitted inputs and are not claimed proved.

## No longer needed

The item removes all seven former proof-only imports:

- `Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed`
- `Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage`
- `Sheaf.AlgebraicGeometry.CanonicalModuleBaseChangeAffineLocality`
- `Sheaf.AlgebraicGeometry.AffineRelativelyFlatCanonicalModuleBaseChange`
- `Sheaf.Topology.SheafIsomorphismLocalOpenCover`
- `Mathlib.CategoryTheory.Localization.Equivalence`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`

The combined
implementation and its four private helpers are retired. Actual users replace their old item
import with the specific existing proof APIs, using plain imports. Source public imports needed
for existing interfaces remain. No whole-library pruning count is claimed for dependencies that
other modules still use.

Old item proof_deps no longer used by its current derived reduction:
`def-pc-derived-category`, `def-pc-perfect-complex`, `def-weil-proper-morphism`,
`lem-pc-proper-support-perfect-direct-image`, `lem-weil-pbc-finite-type-module-support-closed`,
`def-weil-pbc-closed-subset-proper-over-base`, and
`lem-weil-pbc-sheaf-isomorphism-local-open-cover`. The two affine canonical nodes remain.
The old top-level tool_uses entries for finite-type support and closed-subset properness
(including repeated entries) are withdrawn. All eight adapted caller nodes stop using
`lem-pc-rf-perfect-base-change` and name their actual existing dependencies instead.

## Where the brief, the DAG or earlier work was wrong

The retained review was right that the source theorem is not type-equivalent to the removed
one: it assumes an affine base and finite nonempty affine cover; its finite-free complexes have
separately existing homology isomorphisms, and its Cech-derived perfectness clause is conditional
on Noetherianity. We do not infer the old stronger result from those weaker clauses. The previous
attempt stopped before searching sufficiently for replacement interfaces already in Sheaf.
The existing perfectness-only theorem plus the existing canonical relatively flat base-change
APIs allow every actual caller to keep its conclusion. The private import-all user also had to
be included. No caller adaptation or broken build is deferred.

The source attachment of lem-pc-rf-perfect-base-change predates this delivery and still is not
an exact formalization of its full natural-language derived statement. Its lean note and proof
origin now state that limitation explicitly. This repair does not weaken that node's statement,
change any target or definition, or count the source attachment as a proof of the stronger
statement. The unit sk-thm-picard-semicon and all its realized fields remain unchanged; the
geometric perfectness/base-change inputs required by actual callers are retained through their
existing more precise declarations.

## Second reading by B3

Current verdict: repaired the previously rejected retirement by adapting all users together.

1. **Interfaces:** compared each delivered Lean module against the read-only repository.
   Only the item's explicitly retired declarations are removed. All existing declarations in
   the nine adapted consumers retain signatures and visibility. The change record quotes the
   retired public signature verbatim and lists all direct and transitive import users.
2. **Proof/trust:** every delivered module is compiled through lcompile.py in import order.
   No local sorry, forbidden declaration, hollow definition or new axiom is introduced. The
   existing source theorem and delivered public declarations are checked by the delivery axiom
   probe; imported sorryAx is recorded honestly rather than counted as a closed dependency.
3. **Split-offs:** none. No statements were added or weakened. The replacement perfectness
   and canonical-comparison declarations already have nodes. Their general statements cover
   zero modules and empty schemes; no point, nonempty fibre or positive rank assumption is
   added. Comparison witnesses are used only inside theorem proofs, never selected by a
   public data definition.
4. **Route/pruning:** the perfectness-only declaration follows the same Tag 0A1H argument.
   Canonical base change uses the particular comparison wherever the existing mate equation
   needs it. The source result is re-exported as requested, but its homology isomorphisms are
   not treated as a canonical derived isomorphism. The unit route is unchanged. All removed
   item imports and old dependencies are listed above.
5. **DAG:** the eight caller nodes name the precise existing results now used by their Lean
   proofs. The item keeps its source attachment and records the caller-side derived argument,
   with the interface mismatch expressly documented. No new node or statement change is
   hidden in the delivery.

Second reading changed the retirement, all eight theorem users, the private-helper importer,
the corresponding proof metadata and the complete change/report record. Validation through lcompile.py compiled all ten delivered modules together, without warnings
or errors (individual uncached checks up to 16.6 seconds). A source parser independently
confirmed that every signature substring and visibility in all nine consumer modules is
byte-for-byte unchanged, and all nine edited node statements are unchanged with exact
proof-step/dependency unions. Delivery validation is appended after the final dry run.

### Retained earlier second reading (superseded by the repairs above)


Verdict: REJECTED; do not land this retirement. The assigned duplicate repair is
not justified by the source theorem's actual formal statement. A compiling re-export
is not a replacement proof for its callers.

1. Signature and consumer check: FAIL. The diff deletes the public theorem
   `AlgebraicGeometry.perfect_derivedDirectImage_baseChange` and its private helpers.
   The change record declares the removal but does not quote the old signature
   verbatim and defers every consumer adaptation. Nine modules contain actual Lean
   applications of the removed theorem (some other hits are only docstrings).
   In particular `PicardH1CommonMinimalModel.invertible_directImage_isPerfect`
   applies its perfectness conclusion, while
   `PicardDirectImageFibreCohomologyZero.picard_directImage_fibre_cohomology_zero`
   uses invertibility of the particular canonical comparison. These uses cannot be
   replaced by renaming a theorem. No target or definition change is authorized by
   the duplicate-repair instruction.
2. Kernel/axiom check: The repository's original module compiles (10.2 s).
   `#print axioms AlgebraicGeometry.perfect_derivedDirectImage_baseChange` reports
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`: its proof still uses
   open imported results. The proposed source theorem reports only `propext`,
   `Classical.choice`, and `Quot.sound`, but its statement is weaker. A scratch
   copy of the retirement with `#check` of the old theorem fails with unknown
   identifier. No new prohibited declarations or hollow definitions occur in the
   proposed file, which contains no declarations at all.
3. Split-off statements: none. No holes were proved or added. Deleting this
   already locally sorry-free theorem is not a proof. New searches by LeanFinder,
   Loogle, and Mathlib grep found no theorem supplying the missing comparison.
   Source and Sheaf searches likewise found no bridge from the source theorem's
   separate homology isomorphisms to a derived isomorphism with the finite free
   complex. Existing proofs of the old conclusion use the stronger proper-support
   and canonical affine-local results rather than the proposed source result.
4. Route and pruning: FAIL. The source theorem is affine-base only, with an
   explicit finite nonempty affine cover. Its first clause gives unrelated
   `Nonempty` isomorphisms of cohomology objects, not a quasi-isomorphism to the
   direct-image object. Its third clause proves perfectness of the Cech object
   only under a Noetherian hypothesis. The source docstring explicitly records
   these limitations and explicitly disclaims canonicality of the first clause's
   isomorphisms. The old theorem gives derived perfectness over an arbitrary base
   and invertibility of every map satisfying `IsDerivedModuleBaseChangeMap`.
   Thus the deleted proof-dependency modules cannot be declared unnecessary for
   the original conclusion. The unit `sk-thm-picard-semicon` is unchanged (its
   `realized` fields are empty); this retirement does not establish its required
   geometric step.
5. DAG agreement: FAIL. The delivered node is identical to the repository node:
   its `lean` attachment already points to the weaker source result while its
   `proof` and `proof_deps` still describe the deleted derived-category proof.
   The source attachment alone does not validate that mismatch, and changing the
   natural-language statement to match the weaker result would lose the required
   canonical arbitrary-base-change conclusion.

Changes by the second reader: independently checked the original and replacement
statements, all textual callers, the unit, imports, node, source docstring, and
axioms; recorded the rejection and scratch compiler evidence. No weakening,
replacement axiom, arbitrary data selection, or deferred consumer breakage is
accepted. The proposed change record and re-export must not be delivered.

## Delivery validation

`deliver3.py B3 Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange --no-push` printed
`OK (dry run)` for commit `b59ea180dc`: all delivered files compile, the declaration axiom
probes report no forbidden axioms, and preflight passes. The review class is CODEX because
this is an interface retirement, with nine adapted modules, node proof metadata and a change
record. No new proof hole is counted as closed, no new hole is added, and no target or
consumer signature is changed. This supersedes the earlier rejected bare retirement: its
consumer repairs are now included atomically.
