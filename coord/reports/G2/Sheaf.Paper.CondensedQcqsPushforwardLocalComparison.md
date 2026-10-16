## What changed

Proved the original, unchanged declaration
`AlgebraicGeometry.ProEtale.condensed_qcqs_pushforward_local_comparison`.
The proof constructs the actual evaluated colimit cocone: good truncation gives
objectwise isomorphisms after derived localization, its termwise colimit remains
bounded below, and a natural hypercover comparison identifies the canonical
`colimit.desc` as an isomorphism.

Added eight fully proved infrastructure modules and a ninth small shared module
containing the unchanged extension-by-zero proof. Reused the existing finite-cover theorem.
Five provide abelian hypercover infrastructure:
exact colimit-preserving evaluation, the signed coproduct total, restriction
augmentation, bounded-below quasi-isomorphism preservation, and descent from exact
rows. A generic category-theoretic interface reconstructs the section-ring sheaf of
a commutative monoid in abelian sheaves and proves the equivalence between its
internal modules and ordinary sectionwise module sheaves. The injective-row module
transports injectives through this equivalence and a universe-lifted site
equivalence, then uses the existing ringed hypercover exact-sequence theorem.
The natural comparison module uses bounded-below K-injective resolutions, the
derived functor unit, and the existing bounded-below homotopy-invariance theorem
from `Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex`.

The original module's proof, proof imports and attribution change. The repair
also exposes the existing finite-cover helper in its unclaimed source module,
without changing its type or proof. The H4 repair also exposes the existing
homotopy-invariance helper in its unclaimed source module, deletes the 44-line
duplicate private declaration from `CondensedHypercoverComparison`, and uses the
qualified original theorem. Its type and proof remain unchanged. The source module
is included, with users and holder recorded in
`coord/changes/G2-bounded-below-homotopy-reuse.md`. No target, definition or
universe changes. The unit's
hypercover route is retained. Every new definition is an explicit construction.
Resolutions are chosen from the already proved bounded-below resolution theorem;
no object is chosen from an unproved existence statement.

The return about `finite_cover_refinement` is repaired in place: its duplicate
private declaration and proof have been removed from the abelian evaluation
module. A proof import supplies the original theorem, made public by removing
one `private` keyword in its existing unclaimed source module. The change record
is `coord/changes/G2-proetale-finite-cover-refinement-reuse.md`.
The independent second-reading records below predate the current H4 repair and
are preserved as history. A new second reader must review the helper visibility,
reuse, DAG attachment and recomputed pruning list.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.condensed_qcqs_pushforward_local_comparison`
(node `lem-weil-pbc-condensed-qcqs-pushforward-local-comparison`).
Added zero holes. No declaration in any delivery module contains `sorry`.
This is a proof, rather than a decomposition with outstanding obligations.

The H4 repair preserves the existing helper's type and proof byte for byte,
changing only its visibility. Its source module, the condensed hypercover
comparison and the original item compiled successfully through `lcompile.py`.
No new proof body or unresolved obligation is introduced. The required dry run
checks compilation, axioms, node metadata and imports for the complete delivery.

The new substantive proved declarations are:

- `AlgebraicGeometry.Scheme.ProEt.affine_weaklyContractible_abelian_evaluation_colimits`.
- `AlgebraicGeometry.Scheme.ProEt.abelianHypercoverTotal_preservesColimits`.
- `AlgebraicGeometry.Scheme.ProEt.abelianHypercoverTotal_map_quasiIso_of_weaklyContractible`.
- `AlgebraicGeometry.Scheme.ProEt.abelianHypercoverAugmentation_quasiIso_of_rows`.
- `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence`.
- `AlgebraicGeometry.ProEtale.condensedHypercoverInjectiveRow`.
- `AlgebraicGeometry.ProEtale.condensedHypercover_comparison`.

The total and augmentation definitions and their compatibility lemmas are also
fully proved. Explicit `#print axioms` checks of all seven substantive new results,
the total and augmentation definitions, and the original theorem show only
`propext`, `Classical.choice`, and `Quot.sound` (scratchpad/final-axioms.log).
The previous-round dependent compile passed without warnings: injective row 56.0 seconds,
natural comparison 17.3 seconds, original item 13.7 seconds. There are no split-offs
left for another worker to prove. The required dry run provides the final
whole-delivery compile and axiom probes. The first run passed these checks and
identified a global elaboration option in the item; it is now scoped to the two
proofs. The current second-reading checks and repairs are recorded below.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.ProEtaleOperations`.
- `Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian`.
- `Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits`.
- `Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution`.
- `Mathlib.Algebra.Category.ModuleCat.AB`.
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`.
- `Mathlib.Algebra.Homology.HomotopyCofiber` from `CondensedHypercoverComparison`;
  the source module retains the import needed by the reused helper.

The abelian implementation needs no inverse-image action construction, K-flat
coefficient machinery. Its total comparison uses the abelian implementation. The ringed evaluation module
is now retained solely to reuse its finite-cover geometry helper. The condensed
hypercover comparison is also retained with a proof import of the existing
`ProEtaleHypercoverComputesBoundedComplex` module; its public homotopy helper
replaces the deleted duplicate. The proved
generic bounded-below K-injective resolution API replaces
the stated resolution wrapper. The injective row uses the raw ringed exact
sequence directly. The existing ringed hypercover wrappers remain in the import
closure through the module supplying the homotopy helper.
Comparing the item's project import closure before and after this repair gives
these 16 removed project modules and their attached nodes (see
`scratchpad/closure_diff_homotopy_repair.json`). The existing ringed hypercover
comparison module and its ringed total, augmentation, injective-row and comparison
dependencies are retained by the reused homotopy helper's source import. They are
not pruned. This is pruning below this item; other parents may still need the
removed modules. No unit statement or unit proof step is bypassed.

| Removed module | Attached nodes |
| --- | --- |
| `Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution` | `lem-sc-bounded-below-injective-resolution` |
| `Sheaf.Algebra.Homology.KFlat` | `def-pc-kflat-complex` |
| `Sheaf.Algebra.Homology.KFlatCoefficientUniverse` | No attached node found |
| `Sheaf.AlgebraicGeometry.ProEtaleModelRingPresentation` | `lem-weil-pbc-proetale-model-ring-presentation` |
| `Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying` | `lem-weil-pbc-proetale-module-inverse-image-underlying` |
| `Sheaf.AlgebraicGeometry.ProEtaleOperations` | No attached node found |
| `Sheaf.CategoryTheory.ExtensionByZeroPresheaf` | `def-weil-extension-by-zero-presheaf` |
| `Sheaf.CategoryTheory.ModuleInverseImageAction` | `def-weil-pbc-module-inverse-image-action` |
| `Sheaf.CategoryTheory.ModuleInverseImageActionOfPresentations` | `lem-weil-pbc-module-inverse-image-action-of-presentations` |
| `Sheaf.CategoryTheory.ModuleInverseImageAdjunction` | `lem-weil-pbc-module-inverse-image-action-adjunction` |
| `Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian` | `lem-pur-ringed-site-grothendieck-abelian` |
| `Sheaf.CategoryTheory.SheafPullbackForgetComparison` | `lem-weil-pbc-sheaf-pullback-forget-comparison` |
| `Sheaf.CategoryTheory.SheafPullbackUnitPresentation` | `def-weil-pbc-sheaf-pullback-unit-presentation`; `lem-weil-pbc-sheaf-pullback-unit-presentation` |
| `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction` | No attached node found |
| `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated` | `lem-pc-right-derived-functor-triangulated` |
| `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian` | `lem-weil-pbc-ring-sheaves-grothendieck` |

The affine acyclic hypercover, local matching-boundary lifting, and generic ringed
injective augmentation exactness remain needed. Their free-resolution dependencies
are retained. Unused copied imports were removed from the new implementations;
the module-equivalence construction imports its monoidal sheafification API
rather than the pro-etale derived-functor framework.

The second reading also removed a duplicated private
`extension_preservesColimits`. Its existing proof was moved unchanged from
`Sheaf.AlgebraicGeometry.ProEtaleModuleCohomologyCoproducts` to
`Sheaf.Algebra.Homology.ComplexExtensionColimits`, imported privately by both
callers. This replaces the direct
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero` import in the abelian total.
The new small helper module adds no hole. The preceding 16-module pruning table
is unchanged; it was recomputed in `scratchpad/closure_diff_second_reading.json`.

For completeness, the original item's old direct `proof_deps` no longer used
as proof nodes are:

- `def-sbc-standard-tstructure-derived-category`.
- `def-weil-pbc-proetale-operations`.
- `def-weil-pbc-scheme-conventions`.
- `lem-pur-ringed-site-grothendieck-abelian`.
- `lem-sc-bounded-below-injective-resolution`.
- `lem-weil-pbc-kinjective-hom-derived`.
- `lem-weil-pbc-proetale-hypercover-computes-bounded-complex`.
- `lem-weil-pbc-proetale-wcontractible-affine-evaluation-colimits`.
- `lem-weil-pbc-qcqs-over-affine`.
- `lem-weil-pbc-ring-modules-grothendieck-abelian`.

These are removals from the item's direct DAG proof dependencies, not claims that
every corresponding module is absent from the transitive import closure. The
scheme and derived-category conventions remain in its types. Qcqs of the
pullback is obtained directly from Mathlib's base-change instances. The remaining
ringed comparison and evaluation modules are retained to reuse their generic
helpers; they are not pruned. The abelian evaluation, total and condensed
comparison nodes record the replacements actually called by the proof.

## Where the brief, the DAG or earlier work was wrong

The current second reading found a third repeated helper: the private
`extension_preservesColimits` in the abelian total was already proved with the
same general statement in `ProEtaleModuleCohomologyCoproducts`. Its unchanged proof
now lives in a small shared module, and both original and new callers import it.
The change record is `coord/changes/G2-complex-extension-colimits-reuse.md`.

The earlier delivery and its second reading also missed that the homotopy
invariance proof duplicated the existing private theorem. This repair exposes and
reuses that theorem exactly as requested. The new attachment
`lem-weil-pbc-bounded-below-homotopy-invariance` records the helper, and both its
source comparison node and the condensed comparison node cite it.

The first delivery and its second reading missed that the finite-cover helper
already existed privately in the ringed evaluation module. The duplicate checker
correctly refused it. This repair reuses the existing proof rather than retaining
a second copy. The earlier claim that its source module was pruned is withdrawn:
it and its dependencies are now retained by the private proof import.

The old proof dependencies compute sections for sectionwise ringed-module sheaves,
whereas the specified derived pushforward acts on internal modules in monoidal
abelian sheaves. Those categories are not definitionally equal. No ready
equivalence was found in Mathlib or the project. The new generic equivalence
constructs both directions and proves full faithfulness and essential
surjectivity. Its forward functor keeps the underlying abelian sheaf, section
groups and restriction maps unchanged. This justifies preservation of injectives
without assuming the ordinary forgetful functor preserves them.

The total colimit assertion needs no bounded-below hypothesis: the coproduct total
preserves all available colimits degreewise. Boundedness enters only descent and
quasi-isomorphism comparison. The canonical comparison map is handled with cocone
universal properties, so no ringed derived-functor adjunction or triangulated
comparison is needed.

Mathlib searches used leanfinder, loogle, grep and leansearch. Leansearch returned
an Internal Server Error; the other searches and local library searches were
inspected and recorded in the new nodes. No unavailable result is used.

## New nodes

`lem-weil-pbc-bounded-below-homotopy-invariance`: attachment to the existing
`AlgebraicGeometry.Scheme.ProEt.map_eq_of_boundedBelow_homotopy`. Only visibility
changes; its proof and signature are preserved, and no new obligation is added.

`lem-weil-pbc-proetale-affine-finite-cover-refinement`: DAG attachment to the
existing fully proved finite-cover helper, now public in its original module.
There is no new theorem body and no new proof obligation. The abelian evaluation
node now cites this helper explicitly.


`def-weil-pbc-internal-abelian-sheaf-module-equivalence`: Internal abelian module sheaves as sectionwise module sheaves. Explicit construction and fully proved API.

`def-weil-pbc-proetale-abelian-hypercover-augmentation`: Restriction augmentation into abelian hypercover totals. Explicit construction and fully proved API.

`def-weil-pbc-proetale-abelian-hypercover-total`: Abelian section rows and coproduct total of a pro-etale simplicial object. Explicit construction and fully proved API.

`lem-weil-pbc-condensed-hypercover-comparison`: Natural bounded-below condensed pushforward hypercover comparison. Fully proved.

`lem-weil-pbc-condensed-hypercover-injective-row`: Hypercover row descent for an injective internal condensed module. Fully proved.

`lem-weil-pbc-proetale-abelian-evaluation-colimits`: Exact colimit-preserving abelian evaluation on affine weakly contractible objects. Fully proved.

`lem-weil-pbc-proetale-abelian-hypercover-row-comparison`: Exact abelian section rows imply bounded-below total descent. Fully proved.

`lem-weil-pbc-proetale-abelian-hypercover-total-colimits`: Abelian hypercover totals preserve colimits. Fully proved.

`lem-weil-pbc-proetale-abelian-hypercover-total-quasi-iso`: Abelian hypercover totals invert bounded-below quasi-isomorphisms. Fully proved.

`lem-weil-pbc-complex-extension-preserves-colimits`: attachment to the existing
extension-by-zero proof moved unchanged into its own shared module. Both the
abelian-total node and the original ringed-coproduct node cite it. No new proof
obligation is introduced. Its change record is
`coord/changes/G2-complex-extension-colimits-reuse.md`.

The repair change records are
`coord/changes/G2-proetale-finite-cover-refinement-reuse.md` and
`coord/changes/G2-bounded-below-homotopy-reuse.md`. The latter records the
visibility change and users of the reused bounded-below homotopy helper.
No forced adaptations of modules held by other groups are needed. The original node changes
only its proof, proof dependencies and proof origin. All new nodes describe the
actual Lean argument; none represents an outstanding proof obligation.

## Earlier second reading (a previous round; superseded)

1. **Signatures and statements.** Compared every delivered module with the repository version. The existing theorem signature and all existing declarations are unchanged byte for byte; only author/import/proof text changed in the item. New declarations have the statements recorded in their DAG nodes.

2. **Proof validity and axioms.** Compiled the item and all sandbox modules with `lcompile.py`; the item compiled in 19.8 seconds and the module-equivalence file in 56.3 seconds. Searched for forbidden constructs and `sorry`; none occur in Lean sources. The recorded axiom probes show only `propext`, `Classical.choice`, and `Quot.sound`.

3. **Split statements and duplicates.** The ten added DAG nodes were checked against the declarations and their docstrings, sources, and search records. Each is a strict infrastructure statement used by the proof, with no outstanding sorry; no duplicate of an existing library declaration was found.

4. **Shortest route and pruning.** Read the proof from the target downward and checked that it uses the affine acyclic hypercover route and the unit's hypercover comparison step. The report's removed imports and 25 pruned modules are exactly the dependencies absent from the final proof; no required unit step is bypassed.

5. **DAG agreement.** Checked each node's `lean`, `proof`, `proof_deps`, and `proof_origin` against the imports and declarations. The target node records only proof and dependency changes, and the unit realization remains intact.

I changed only this report section; no Lean code, node, or statement was altered during second reading.

## Earlier second reading (a previous round; superseded)

1. **Signatures and statements.** I compared the delivered target module with the
repository version and checked every existing declaration byte for byte. The target
signature is unchanged. The exposed finite-cover helper changes only visibility, as
recorded in `coord/changes/G2-proetale-finite-cover-refinement-reuse.md`. The new
declarations have statements matching their DAG `lean.statement` fields.

2. **Proof validity and axioms.** I compiled all ten sandbox modules together with
`lcompile.py --all` and found no errors or warnings. I searched the delivered Lean
files for `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, and
`debug.skipKernelTC`; none occur. The explicit axiom probes for the target, the
comparison lemmas, the total and augmentation definitions, the evaluation theorem,
and the module equivalence report only `propext`, `Classical.choice`, and
`Quot.sound`.

3. **Split statements and duplicates.** I checked each added DAG node against its
Lean declaration, docstring, source, and proof dependencies. The split statements
are strict infrastructure results used by the target proof, and no duplicate
declaration or unresolved split-off theorem was found. The finite-cover node
attaches to the existing proved helper rather than introducing a second theorem.

4. **Shortest route and pruning.** I read the target proof downward. It uses the
affine weakly contractible hypercover route, the abelian evaluation and total
colimit lemmas, and the natural condensed hypercover comparison. The removed imports
and dependency modules listed under `## No longer needed` are absent from the final
proof. The unit’s hypercover comparison route and all required unit steps remain.

5. **DAG agreement.** I checked the target and new nodes’ `lean`, `proof`,
`proof_deps`, and `proof_origin` fields against the imports and declarations. The
target node records only proof and dependency changes; the visibility repair has a
matching change record; and the unit realization is unchanged.

I changed only this report by adding this required second-reading record. No Lean
module, statement, node, or proof was changed during this reading.

## Second reading by G2

1. **Existing interfaces.** I compared every existing delivered module against the
   read-only repository. The target signature is byte for byte unchanged. Each of
   the finite-cover and bounded-below homotopy source files differs by exactly one
   removed `private` keyword, as its change record says; their signatures, proofs
   and other declarations are unchanged. My additional repair removes the private
   extension-by-zero helper from the unclaimed coproduct source module and moves
   its signature and proof unchanged to a shared module. The source gains one
   plain proof import; all other source text, including public signatures and
   proof bodies, is byte for byte unchanged. This is declared in
   `coord/changes/G2-complex-extension-colimits-reuse.md`. No target or definition
   used by a target has changed.

2. **Proofs and constructions.** I read all delivered modules, compiled the eleven
   original delivery modules in import order with `lcompile.py --all`, and compiled
   the new shared helper and its two repaired callers together. All passed with
   no warnings. No delivered Lean file contains `sorry`, `axiom`, `unsafe`,
   `opaque`, `implemented_by`, `extern` or `debug.skipKernelTC`. The ring and module
   structures are constructed from tensor multiplication and actions; the
   equivalence's inverse is obtained from proved full faithfulness and essential
   surjectivity. Resolutions come from the proved bounded-below resolution
   theorem. There is no data chosen from an unproved existence statement. The
   existing axiom log contains only the three permitted axioms; the final dry run
   recompiles the entire repaired set and checks every declaration's axioms.

3. **New statements and reuse.** There are no outstanding split-off statements:
   one original hole closes and zero holes are added. I checked the definitions,
   theorem types, proof docstrings and DAG statements. Evaluation is on abelian
   sheaves, the total has the signed coproduct differential, row descent assumes
   exactly the represented augmentation and matching epimorphisms, and the
   natural comparison is restricted to strictly bounded-below complexes. The
   comparison itself assumes no colimit preservation; that enters separately in
   the target's cocone argument. Small-case checks cover zero coefficients, empty
   inverse images, empty colimits in the generic preservation helpers, negative
   lower bounds, and the cylinder's shifted bound n-1. I repeated semantic and
   type searches with different wording and searched Mathlib and both project
   roots. They found no ready internal/sectionwise module equivalence. The direct
   project search did find the exact private `extension_preservesColimits` in
   `ProEtaleModuleCohomologyCoproducts`; I removed the duplicate and moved that
   existing proof to the shared module. The finite-cover and homotopy helpers are
   likewise reused, with no remaining exact duplicate of those declarations.

4. **Route, imports and pruning.** I read from the target down through the generic
   colimit cocone proof, natural resolution comparison, injective row and the
   sectionwise-module equivalence. I checked the two spectral-sequence comparisons
   in [Stacks Tag 09A2](https://stacks.math.columbia.edu/tag/09A2) and exact
   weakly-contractible evaluation in
   [Tag 0946](https://stacks.math.columbia.edu/tag/0946); the algebraic-structure
   construction is expanded explicitly rather than assumed from Tag 00YV.
   The unit `sk-thm-properbasechange` and its `realized` fields are untouched; the
   hypercover route serving its continuity step remains. Imports needed solely
   for the new proofs are plain imports. I removed the abelian total's direct
   zero-functor preservation import after moving the helper, and added a plain
   import of the shared proof to both callers. Recomputing the import closure
   confirms the sixteen removed modules listed above. I completed the list of
   old direct DAG proof dependencies no longer used, distinguishing those edge
   removals from actual module pruning. The ringed helper source modules remain
   imported and are correctly excluded from the pruning claims.

5. **DAG agreement.** I checked all delivered node statements against Lean
   (verbatim for new nodes; the unchanged old ringed comparison record differs
   only by whitespace), and checked that each `proof_deps` equals the union of its
   proof steps' `uses`. The target node changes only `proof`, `proof_deps` and
   `proof_origin`. The homotopy and finite-cover attachments point to the reused
   existing declarations. The additional generic extension node has its source,
   four actual logged searches (LeanSearch unavailable), full natural-language proof, creation data,
   blueprint placement and exact Lean signature. The abelian-total and original
   ringed-coproduct nodes both cite it. No unit step is replaced or omitted.

Changes made in this second reading: removed the additional duplicated extension
helper by moving its unchanged proof to `ComplexExtensionColimits`; adapted the
original unclaimed caller with a proof import; updated the three affected DAG
nodes and added the change record; completed the old-dependency pruning list and
this report. The target proof and all existing public statement signatures are
unchanged. Final delivery validation is recorded below.

Fourteen fresh explicit `#print axioms` checks, including the unchanged target,
all seven substantive new results, the total and augmentation constructions,
the section-ring sheaf, and the three reused helpers, passed after the repaired
set was rebuilt. Each reports only `propext`, `Classical.choice` and `Quot.sound`;
none reports `sorryAx`. The scratch source is
`scratchpad/SecondReadingAxioms.lean` and the output is
`scratchpad/second-reading-axioms.log`. It is outside the delivered source set.

The first repaired-set dry run compiled all thirteen files and passed its axiom
checks, then found one metadata issue: the new extension node needed a logged
LeanSearch attempt in addition to the other search categories. I ran that query;
the service returned Internal Server Error. Its unavailability is now recorded
without claiming a negative search result. No Lean source changed in this repair.

The final repaired-set dry run returned `OK (dry run)` at temporary commit
`04f4411ded`: all thirteen delivered modules compiled and passed preflight,
including automatic axiom checks. No unresolved obligation remains.
