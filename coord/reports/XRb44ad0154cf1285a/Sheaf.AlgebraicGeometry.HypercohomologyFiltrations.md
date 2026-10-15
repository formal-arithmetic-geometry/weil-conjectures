## What changed

Repair of the landed delivery: changed the proof-only import of `Sheaf.CategoryTheory.ExactFunctorCouple` to `import all Sheaf.CategoryTheory.ExactFunctorCouple`. The landed proof destructures `BigradedExactCouple.exactFunctor_couple`, whose dependent result mentions a private proof constant; the ordinary import leaves that constant unavailable during the global rebuild. The `import all` form exposes the required declaration metadata without changing any public statement or definition. The module compiles with the allowed single-file compiler.

Proved all three original holes in
`Sheaf.AlgebraicGeometry.HypercohomologyFiltrations`. Existing public signatures,
definitions and public imports are unchanged. All added helper declarations are private
and proved; their category universes are explicit so they do not redeclare the existing
private helper statements from `Sheaf.CategoryTheory.TruncationRawExact`; no other
Lean module is changed.

Exactness now follows directly from the cohomology long exact sequence of the mapped
truncation triangles. Monotonicity follows by factoring truncation inclusions. The
specification uses explicit lower-bound arguments, `halfPlaneConvergence` and
`abutment_image_filtration` to obtain convergence with the prescribed canonical image
filtration. It also proves the three bridge equations, E2 identifications, termwise
truncation and homology comparisons, and the canonical comparisons of every page,
differential and filtration. The top-degree part of the termwise truncation comparison
is proved using the boundary-cycles-homology exact sequence.

For page transport, the proof uses the existing stated
`BigradedExactCouple.exactFunctor_couple`, then transports along the canonical
cohomology isomorphisms using `coupleMorphism` in both directions. The proof verifies
the inverse equations on all derived pages, the page-zero normalization and every
differential square. The exact-functor cohomology comparison is used with its existing
shift-compatibility lemma to verify the boundary square.

Added proof-only imports of `Sheaf.CategoryTheory.AbutmentImageFiltration`,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`.
Updated the item's
node proof, proof dependencies and proof origin to match the implemented route.

The cleaned module compiles without warnings in approximately 13 seconds through
`lcompile.py`. Generic private bridge helpers and a local irreducibility attribute
for `TruncationCouple.bridgeIso` prevent expensive unfolding of resolution choices;
no exported definition or reducibility attribute changes.

The dry run conservatively classified the scoped elaboration controls as an
interface change. The required record is
`coord/changes/hypercohomology-filtrations-local-elaboration.md`; it lists the
commands and all downstream modules, explaining why no adaptation is needed.

## Proved and sorry left

Closed the three original holes:

- `CategoryTheory.hypercohomology_maps_exact`.
- `CategoryTheory.hypercohomology_images_antitone`.
- `AlgebraicGeometry.Etale.hypercohomologyFiltrations_spec`.

Holes added: zero. Holes remaining in the delivered module: zero. No split-offs or
new public declarations. This is three proofs from existing library statements,
not a decomposition into new obligations. On the current compiled library,
independent `#print axioms` checks of all three theorems and
`CategoryTheory.BigradedExactCouple.exactFunctor_couple`
(node `lem-sp-exact-functor-couple`) show only `propext`, `Classical.choice`,
and `Quot.sound`. The earlier round's inherited-sorry description below is historical
and superseded by the current independent reading.

## No longer needed

Removed seven unused direct proof imports:

- `Sheaf.CategoryTheory.TruncationCoupleExact`:
  `lem-sp-truncation-couple-exact` is not used by this proof; exactness is obtained
  directly from the distinguished triangle and its long exact sequence.
- `Sheaf.CategoryTheory.TruncationHypercohomology`:
  `thm-sp-truncation-e2` is not used as a proof lemma; the required E2 terms and
  convergence are established directly. Its original statement dependency stays
  unchanged in the node, so this is not a claim that no other target needs it.
- `Sheaf.AlgebraicGeometry.EtaleInverseImageExact`:
  no use of `prop-weil-pbc-inverse-image-exact` as a separate proof lemma. The
  source-library exactness instances for the actual inverse-image functors suffice.
  The original statement dependency remains unchanged.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`:
  redundant direct import; the sheaf categories and torsion predicate used in the
  unchanged signatures are already available through the public source imports.
  `def-weil-pbc-etale-sheaves` is not a separate proof dependency of this route.
- `Sheaf.CategoryTheory.KInjectiveBridge`:
  redundant direct import. Its definitions and `bridgeIso` are still needed through
  `TruncationCouple`; `def-sp-kinjective-bridge` stays a proof dependency.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  redundant direct import, already available through public
  `UpperLowerStarCoherence`. The direct-image definitions remain necessary.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  redundant direct import, publicly re-exported by `UpperLowerStarCoherence`.
  Its cohomology and shift comparisons remain necessary and recorded in `proof_deps`.

The second reading also removed the first worker's added direct import of
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`:
`PlusCompatibility` publicly imports `PlusSingle`, which publicly imports it.

Also removed `def-sp-etale-dictionary` and
`def-weil-pbc-derived-inverse-image` from the node's proof dependencies: the proof
works with the already fixed source functors and their actual APIs rather than
using these dictionary nodes as lemmas. Their original statement dependencies are
unchanged. No module is withdrawn. The proper-base-change unit's realized statement
and proof steps are preserved. The general half-plane convergence and couple-morphism
results are used as tools, without bypassing the proper-base-change unit.

## Where the brief, the DAG or earlier work was wrong

The landed delivery compiled in its local environment but failed at the global tip because the ordinary proof-only import did not expose the private proof constant appearing in the dependent type of `exactFunctor_couple`. This is an import elaboration issue; no theorem statement or proof meaning needed revision.

The returned delivery correctly identified six private helper statements as textual
duplicates of declarations in `Sheaf.CategoryTheory.TruncationRawExact`. The repair
keeps the same local proofs but makes the category universes explicit in those six
private binders, removing the duplicate-statement collision while preserving their use.
No false statement or interface defect was found. The planned route through raw
truncation hypercohomology is unnecessary for the cohomological couple actually
specified here. The direct route still proves the full original specification,
including the canonical bridge, inclusion, page-zero and differential equations;
it does not replace canonical data by arbitrary isomorphisms.

The existing source library already supplies right-derived lower-bound vanishing,
bounded/unbounded compatibility, the classical single-object derived-functor
comparison, and exact-functor cohomology/shift compatibility. These APIs close the
steps that the original node packaged inside its raw truncation theorem.
No target, existing statement or public definition was changed, and no forced
adaptation was needed.


## Earlier second reading (a previous round; superseded)

1. **Interface: pass.** Read the complete repository and sandbox modules and their
   diff. Compared the raw signature slices of all public declarations and the full
   specification; they are identical. The six private helper signatures now explicitly
   bind category universes to avoid the returned duplicate-statement collision. Every
   existing definition body is byte-identical. Section variables and all five public imports
   are unchanged. The 23 added helpers are private and proved. The recorded local
   elaboration controls do not export attributes or change data. No other Lean module
   is delivered, and no target or downstream interface changes.

2. **Proof and axioms: pass.** Independently compiled the module using `lcompile.py`
   without warnings (12.4 seconds before the two redundant imports were removed).
   Read exactness via the three homology-sequence pairs, the actual truncation
   factorization proving antitonicity, and every clause of the final proof.
   A scratch copy with explicit `#print axioms` reports only `propext`,
   `Classical.choice`, `Quot.sound` for `hypercohomology_maps_exact` and
   `hypercohomology_images_antitone`; the specification additionally uses `sorryAx`
   from existing imported obligations, including `exactFunctor_couple`.
   There is no local `sorry`, forbidden declaration, or hollow definition.
   The mapped couple supplied by `exactFunctor_couple` is used inside a proof:
   its object equalities and map equations prescribe its initial data, and no
   arbitrary witness is installed as an exported definition. The termwise
   truncation comparison is explicitly constructed from truncation inclusions.

3. **Split statements and edge cases: pass.** No statements are split off and no
   holes are added. Checked the private cycles lemma using its boundary-cycles-
   homology short complex, including the required epi and mono assumptions.
   Checked zero complexes, arbitrary integer cutoffs (in particular the top degree
   and its predecessor), page zero versus actual page two, negative p, and n < a.
   In the last case lower-bound preservation forces the abutment to vanish, so the
   overlapping top/bottom filtration bounds are consistent. No hypothesis was added
   to resolve an edge case. Searched Mathlib, the source library, and lean/Sheaf for
   truncation-map, cycles-map, and page-isomorphism comparisons. Existing derived
   truncation isomorphisms do not replace the required isomorphism of complexes
   commuting with its inclusion. The existing raw top-degree comparison is only
   a homology comparison. Mathlib `truncLEXIso` does not definitionally identify
   its hom with the component of `ιTruncLE`; retained the working helper.

4. **Route and pruning: pass after import cleanup.** The proof starts at the three
   original holes and uses existing long-exact-sequence, negative-vanishing,
   bounded/unbounded compatibility, half-plane convergence and canonical image-
   filtration APIs. Reviewed all three bridge equations, all E2 identifications,
   the top-degree truncation argument, and the shift-compatible boundary square.
   The two couple morphisms are proved inverse on every page by cancellation at
   kernel inclusions and epi projections, preserving page-zero normalization and
   every differential. The image-filtration comparison uses the actual abutment
   inclusion maps. Compared every removed old proof dependency with `No longer
   needed`; all six are explained there. Read `dag/units/sk-thm-properbasechange.json`
   and its `realized` statement and steps: this node realizes none of those entries,
   and its internal replacement route does not bypass any of them.
   Removed the two redundant direct imports identified above. All added imports
   remain proof-only; no public import was changed.

5. **DAG: pass.** Compared the complete old and delivered node JSON. Only `proof`,
   `proof_deps` and `proof_origin` differ. The statement, statement dependencies,
   Lean record, chapter and unit are unchanged. The union of the proof steps'
   `uses` is exactly `proof_deps`. Read the recorded declarations for the new
   negative-vanishing, compatibility, half-plane and abutment dependencies; they
   are the APIs invoked in the proof. The bridge, exact-functor and couple-morphism
   dependencies remain recorded despite redundant direct imports being removed.
   No new nodes or change of unit realization is needed.

Changes made in this second reading: removed two redundant proof-only imports,
updated the import lists in this report, and added this independent review.
The proof terms and all public declarations were retained.

Final validation: the module compiles cleanly in 12.5 seconds after import cleanup.
`deliver3.py XRb44ad0154cf1285a Sheaf.AlgebraicGeometry.HypercohomologyFiltrations --no-push`
printed OK and passed its declaration axiom probe and preflight. Its CODEX class
reflects the changed node metadata and recorded local elaboration commands.

## Second reading by XRb44ad0154cf1285a

Independent review of the red-build repair on 2026-10-16. Read `request.json`,
`delivery.diff`, all three scoped files and this report, the stage-3 brief and
review rules, and the proper-base-change unit. The previous review text above
was not used as verification evidence.

1. **Interface and mathematics: pass.** Compared the complete Lean module with
   the repository baseline and reconstructed the delivered Lean file from
   `delivery.diff`. All 15 existing declaration signature slices are byte-identical;
   all 12 public definition/abbreviation bodies are unchanged. The only Lean change
   from that delivery is the proof-only `import all` of `ExactFunctorCouple`.
   No target, hypothesis, conclusion, public import, exported attribute or instance
   changes. The local controls match the existing change record.

2. **Compiler failures and proof integrity: pass.** The request contains one
   compiler failure, the dependent `obtain` at line 536. In an independent scratch
   directory without sandbox artifacts, restoring the ordinary import reproduces
   exactly `Tactic generalize failed: result is not type correct` at line 536,
   mentioning `ExactFunctorCouple.0._proof_58` (12.7 s). The repaired module compiles
   cleanly through `lcompile.py` (12.6 s); a separate scratch copy with explicit
   `#print axioms` compiles cleanly (12.5 s). Each of
   `hypercohomology_maps_exact`, `hypercohomology_images_antitone`,
   `hypercohomologyFiltrations_spec`, and the imported `exactFunctor_couple`
   uses only `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`.
   No local `sorry`, axiom, unsafe/opaque/extern declaration, kernel-check bypass,
   or hollow definition is present. All compilation was local, through the required
   wrapper with its 60-second per-file limit; no server compile or lake command.

3. **New statements and edge cases: pass.** There are 23 private proved helpers,
   no added public statements and no split-off holes. Read their proofs, including
   exactness transport, the mono/epi cycles argument, and the constructed termwise
   truncation comparison. Below the cutoff its components are isomorphisms; at
   the cutoff the boundary-cycles-homology exact sequence supplies the isomorphism;
   above it both terms vanish. Negative p is covered by lower-bound preservation.
   For n < a the abutment vanishes, so the overlapping top/bottom bounds agree.
   Page-couple index zero corresponds to actual E2; the all-page vanishing proof
   handles actual r >= 2 via r - 2. No arbitrary existence witness is installed in
   an exported definition.

4. **Route and pruning: pass.** Read all three original proof replacements and
   the canonical bridge, E2, convergence, differential and image-filtration clauses.
   The proof uses the homology long exact sequence, actual truncation inclusions,
   lower-bound compatibility, half-plane convergence and abutment image filtration.
   The boundary comparison uses the cohomology comparison's shift compatibility;
   inverse page maps are proved by cancellation at kernel inclusions and epi
   projections. Searched the local Sheaf and Mathlib truncation/cycles APIs for
   simpler replacements; the existing working helpers prove the required inclusion
   equations, not merely abstract isomorphism existence. The seven removed baseline
   imports and removed old proof dependencies are accounted for under
   `## No longer needed`. All added imports are proof-only, and the import repaired
   here is necessary by the counterfactual. The unit's realized statement and three
   steps are untouched and are not bypassed.

5. **DAG: pass.** The statement, statement dependencies, Lean record, chapter and
   unit are unchanged. Read the proof dependency node records and corresponding
   convergence, image-filtration and couple-transport APIs. The union of step
   `uses` is exactly `proof_deps`, and the proof and `proof_origin` describe the
   implementation. Removed the stale `reviewed_proof` field inherited from the
   failed landing; review metadata is owned by the landing tools. No new node is needed.

Changes by this reader: replaced the inherited second-reading section with this
actual independent review and corrected the current axiom status under
`## Proved and sorry left`. Reopened the change record as required by preflight,
recording the old landing and this repair, and removed stale inherited review
metadata from the sandbox node. The Lean repair and DAG proof metadata were
retained. The report's earlier second reading is explicitly historical.

Final independent validation: `deliver3.py XRb44ad0154cf1285a
Sheaf.AlgebraicGeometry.HypercohomologyFiltrations --no-push` printed OK
(commit e4dfaa47d2), passing the local compilation, full declaration axiom
probe and preflight after the record-status correction. CODEX classification
reflects the existing local controls, node proof metadata and change record.
