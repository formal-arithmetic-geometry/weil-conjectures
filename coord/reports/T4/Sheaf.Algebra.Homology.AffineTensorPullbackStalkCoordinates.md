## What changed

Repair of the X-c6c6a landing refusal: removed the duplicate private theorem
`AlgebraicGeometry.tildeStalk_naturality`. A proof-only
`import all Sheaf.AlgebraicGeometry.AffineDerivedCohomologyPresentation` makes the
existing private `AlgebraicGeometry.affineTildeStalk_naturality` available, and the
localization proof applies it directly. The existing public import remains for
the statement. No existing library module or visibility is changed. The new
localization node now records this reuse. The delivery tool rebases the repaired
sandbox on the freshly fetched `sheaf-dag` before preflight. The exact
`tools/import_prune_check.py` check for the repaired localization module passed
with exit code 0 against the library, including its duplicate-statement check.

Repair C6 replaces the pointwise helper's circular statement-dependency edge by
exactly the four declaration dependencies requested in the return. Every Lean
statement is unchanged. An overlay traversal of 394 dependencies found no path
back to the helper. See
`coord/changes/affine-tensor-stalk-statement-dependencies.md`.

Repair H10 aligns the extracted sheaf comparison's explicit functors, additive
instances and homological-complex comparison constructor with the original
consumer, removes its redundant local derived-category instance, and exposes the
coordinate's original localization/linear-equivalence projections directly. The chosen
comparison and all homology/localization maps are unchanged. No importer source
is edited and no timeout is raised.

Replaced the original hole in
`AlgebraicGeometry.affineTensorPullbackHomologyStalkIso_counit_coordinate`
by a complete Lean proof from the proved global-sections factorization and the
proved generic localization lemma. The already proved main coordinate theorem
uses the counit helper as before. All existing signatures and visibility stay
unchanged.

Proved `AlgebraicGeometry.affineTildeGlobalSectionsStalk_coordinates` for an
arbitrary morphism from tilde V to a quasi-coherent derived cohomology sheaf.
Its proof checks naturality on numerators, extends to fractions by the
localization universal property, and cancels unit and counit by the adjunction
triangle. No tensor pullback hypothesis occurs in this lemma.

Factored the existing sheaf comparison construction into the real named
`AlgebraicGeometry.affineTensorPullbackHomologySheafIso`. The coordinate definition
uses it with the original localization and linear-equivalence projections;
`AlgebraicGeometry.affineTildeLocalizationStalkIso` supplies its proved forward-map
API in the counit proof. A direct additive-equivalence API avoids expanding
scalar-compatibility proofs. These constructions use the original coordinate maps.

Added proof-only imports of the generic stalk lemma and global-sections
factorization, and a public import of the sheaf comparison construction used by
the public coordinate definition. Updated the two original proof nodes to match
this reduction and added nodes for the new declarations.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.affineTensorPullbackHomologyStalkIso_counit_coordinate`
(node `new-lem-pc-affine-tensor-pullback-stalk-coordinates-at`) by reduction.
The original `AlgebraicGeometry.affineTensorPullbackHomologyStalkIso_coordinates`
remains proved.

The first worker added one hole in
`AlgebraicGeometry.affineBaseChangeTildeCohomologyIso_globalSections_factorization`
(node `new-lem-pc-affine-base-change-global-sections-factorization`). The second
reading closed it by unfolding the two coordinate definitions and applying
`Iso.trans_hom`, `Iso.symm_hom`, `Functor.mapIso_hom`, `Functor.mapIso_inv`,
`Functor.map_comp`, and associativity. No hole is added or left in this delivery.
This is one original hole closed, zero holes added, net one hole closed.

The new `AlgebraicGeometry.affineTildeGlobalSectionsStalk_coordinates` is fully proved using the existing
`AlgebraicGeometry.affineTildeStalk_naturality`; the duplicate helper was removed. The additive-equivalence
projection and localized-stalk forward-map theorems are fully proved.
No sorry remains in the item's module, and none occurs in a definition.

## No longer needed

Removed the duplicate private `AlgebraicGeometry.tildeStalk_naturality` and its
proof; the existing private `affineTildeStalk_naturality` supplies this step.

No import removed; no module pruned. Replaced direct proof-dependency edges of the main node: `def-pc-affine-base-change-tilde-coordinates`, `lem-pc-affine-derived-cohomology-presentation`, and `lem-weil-pbc-spec-tilde-stalk-localization`; all remain needed transitively through the helper. Replaced the helper's old circular direct edge to `lem-pc-affine-tensor-pullback-stalk-coordinates`. The original public import supplies the
coordinate definitions used in the statements. The two theorem imports are used only by the proof. The new sheaf comparison
module is a public dependency of the coordinate definition. The localization and affine derived cohomology presentation nodes remain
needed through the new general lemma; they have not been pruned. The blueprint
unit's route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The previous delivery incorrectly treated the existing private naturality theorem
as unavailable and copied its statement and proof. A proof-only `import all`
provides access without changing the source module. The landing rejection is
repaired by importing and using that theorem instead.

The previous report described the main coordinate theorem as still `sorry`, but
it is already proved in the current repository. The remaining hole was the
counit-coordinate helper. The helper node's previous proof dependency pointed
back to the coordinate node instead of recording the actual localization argument.
The updated plan now records the sheaf localization lemma and the coordinate
construction it uses, without using the main coordinate theorem to prove its helper.

The initial proof attempt duplicated the complete coordinate construction in
local lets and hit the heartbeat or wall-clock limit. The large comparison term is now factored into a named definition
with forward-map APIs. The algebraic global-sections factorization
is a separately named intermediate theorem; the second reading proved it by
expansion and composition laws. The localization argument is also proved.

The local Stacks source files cited by the nodes are absent. WANTED:
`literature/stacks-project/schemes.tex`, Tags 01HV and 01I7, and
`literature/stacks-project/perfect.tex`, Tag 0DJ8. The new formal proof was written
from the existing definitions and the pinned Mathlib declarations; its proof origin
is recorded as agent-written, with those declarations named. Searches covered
LeanFinder, Loogle, source grep and the blueprint. LeanSearch returned Internal
Server Error and is recorded as unavailable, not as an absence result.

A dependency traversal encountered the pre-existing cycle between
`lem-weil-pbc-sheaf-algebraic-structures-objects` and
`lem-weil-pbc-sheaf-algebraic-structures-abelian-component`; neither node is edited.

Edge cases: the generic argument does not require an invertible presentation
morphism, applies to zero modules and arbitrary degrees, and has no point to check
for a zero ring. The original lemma adds no boundedness, flatness or cartesian-square
hypothesis.

Repair validation: the returned definition reproduced the unchanged direct
importer's 60-second timeout. After rebuilding the repaired artifacts, the original
`Sheaf.Algebra.Homology.AffineOrdinaryTensorStalkCoordinates` compiled without
errors or warnings in 58.8 seconds with aligned explicit instances, and in 59.0
seconds with the final flattened coordinate. Both used the standard 60-second
limit, after artifact regeneration finished. Its source is byte-for-byte the
repository version. The other unchanged direct importer,
`Sheaf.Algebra.Homology.AffineBaseChangeOrdinaryStalkComparison`, compiled against
the final artifacts in 29.7 seconds without errors or warnings. All three existing
item declaration signatures were checked unchanged against the repository.
No forced adaptation, timeout increase or file split is included. These repair results supersede the earlier compatibility results in the
preserved second-reading section below.

## Statement corrected

C6 corrects the helper node's dependency metadata, not the Lean theorem. Its
previous description, "the displayed equation", was not standalone after removing
the circular parent reference. The node now spells out the identical equation and
its hypotheses using the four requested statement dependencies, with a
`statement_change` record containing the old metadata and all base citers.
No mathematical claim, Lean signature or target statement changes.

## New nodes

`new-lem-pc-affine-tilde-global-sections-stalk-coordinates` is the fully proved
localization identity for any morphism from an affine tilde module to a derived
quasi-coherent cohomology sheaf, in
`Sheaf.Algebra.Homology.AffineTildeGlobalSectionsStalkCoordinates`.

`new-def-pc-affine-tensor-pullback-homology-sheaf-iso` names the real construction
of the first three sheaf-level coordinate factors, in
`Sheaf.Algebra.Homology.AffineTensorPullbackHomologySheafIso`. No data is postponed.

`new-lem-pc-affine-base-change-global-sections-factorization` is now fully proved, in `Sheaf.Algebra.Homology.AffineBaseChangeGlobalSectionsFactorization`.
It identifies the global coordinate before localization with global sections of
those sheaf factors followed by the inverse counit and representative map.
Its statement has no prime, stalk, localization or quasi-coherent
target condition. Its proof is expansion and preservation of composition.

The definition refactoring is recorded in
`coord/changes/affine-tensor-stalk-instance-proofs.md`. Existing signatures and
coordinate data are unchanged; no consumer is adapted. The definition remains
in the targets' dependency closure, so the independent reader should check that
refactoring as part of the statement review.

## Earlier second reading (a previous round; superseded)

1. I diffed the delivered coordinate module against the repository version. The existing target and helper signatures are unchanged; only imports, proofs, and the named factorization definition used by the proof were added. The new definition expands to the original exact-tilde, homology-factorization, and tensor-pullback comparison factors. I read Mathlib `Algebra/Homology/Additive.lean:212`: `Functor.mapHomologicalComplexCompIso` is precisely `NatIso.mapHomologicalComplex`, so that substitution preserves the selected comparison. `ModuleCat/Basic.lean:289` defines the old linear equivalence from the same hom and inverse; the direct additive equivalence retains both maps. The tensor comparison theorem in `Sheaf/AlgebraicGeometry/TensorPullbackTilde.lean:44` is already proved and constrains its chosen isomorphism by the canonical unit equation, which determines it by the adjunction.

2. I compiled all four delivered modules in import order with the launcher. They compile without errors or warnings. The only remaining `sorry` is `affineBaseChangeTildeCohomologyIso_globalSections_factorization`, a named public theorem with a source, a complete proof sketch in its docstring, and a matching node. No definition contains `sorry`, `axiom`, `unsafe`, or `opaque`. Explicit `#print axioms` in a scratch import shows only `propext`, `Classical.choice`, and `Quot.sound` for the general localization theorem and both coordinate constructions. The main theorem, its helper, and the split factorization additionally use `sorryAx`, as expected from the documented remaining hole.

3. The new localization theorem is strictly more general than the target's counit step: it accepts any morphism from a tilde module and does not assume the morphism is invertible. The global-sections factorization is strictly smaller than the target: it has no prime, stalk, localization, or quasi-coherence hypothesis. The named sheaf comparison is a construction, not an arbitrary witness. I checked zero modules and arbitrary degrees in the statements; zero rings have no prime cases. My additional LeanFinder query for global sections unit/stalk localization found ring-level Gamma/Spec results, not this module statement; Loogle returned `Functor.mapIso_trans` as a composition ingredient. I searched the repository and upstream modules for affine factorization and stalk naturality. The existing `affineDerivedCohomologyStalkIso_naturality` concerns morphisms of derived objects, whereas the new lemma accepts arbitrary morphisms of homology sheaves. Repair correction: its numerator helper is the existing private theorem, accessible through `import all`; the duplicate has now been removed. The factorization follows by expansion of the exact coordinate definition: it is true even for unbounded complexes, and does not move the entire geometric statement to a renamed hole. I tried its documented expansion proof locally; it timed out at 60 seconds, so I retained the named hole.

4. The proof dependencies now match the actual route: global-sections factorization, the general tilde localization identity, and the named sheaf comparison. The unit record `sk-thm-picard-semicon` has empty realization lists (`statement: []`, `steps: [[]]`). The reduction retains the blueprint affine tensor comparison and localization route; no populated realized unit node is bypassed. The old proof dependencies remain used transitively, but their direct edges have been replaced. For the main node these are `def-pc-affine-base-change-tilde-coordinates`, `lem-pc-affine-derived-cohomology-presentation`, and `lem-weil-pbc-spec-tilde-stalk-localization`. For the helper the removed direct edge is `lem-pc-affine-tensor-pullback-stalk-coordinates`, eliminating the former circular plan.

5. I checked the node records against the declarations, including the split factorization node and its proof origin. The factorization node documents the one-hole decomposition, while the main target node now records its actual direct use of the counit-coordinate helper. Its final functoriality step is elementary. The unchanged `AffineOrdinaryTensorStalkCoordinates` consumer compiled against the delivered sandbox artifacts in 54.7 seconds, without errors or warnings. The first attempt overlapped artifact regeneration; the successful retry establishes compatibility.

I made the new factorization node explicit about commutative rings and cochain complexes of A-modules, corrected the main node to cite the helper actually used by its Lean proof, corrected the report to enumerate every replaced direct proof-dependency edge, and added this second-reading section. The final dry run and delivery preflight check the corrected metadata and report.


## Earlier second reading (a previous round; superseded)

1. **Interfaces and chosen data: PASS.** I diffed the item against the repository
   and compared the complete signatures through the outer `:= by` delimiter.
   All three existing declaration signatures are byte-for-byte unchanged.
   The declared change record accounts for factoring the coordinate definition.
   The extracted sheaf isomorphism has the original explicit TA, TB and E functors,
   their additive instances, the same chosen tensor comparison, and the original
   exact homology and derived homology factors. The coordinate retains the original
   localization and `toLinearEquiv.toAddEquiv` projections. The chosen comparison
   comes from the proved `exists_tensorPullback_tilde_iso`, whose canonical unit
   compatibility determines the comparison by the adjunction; no arbitrary data
   is chosen from an unproved existence theorem. No target or importer is edited.

2. **Kernel proofs and compilation: PASS.** I compiled all four delivered modules
   with `lcompile.py` in import order, with no errors or warnings. After completing
   the factorization I rebuilt it (35.3 s) and the item (34.7 s). No `sorry` remains
   anywhere in the delivered Lean sources, and no forbidden declaration form or
   hollow definition occurs. A fresh scratch import with explicit `#print axioms`
   for all ten public declarations shows only `propext`, `Classical.choice` and
   `Quot.sound`; neither coordinate theorem nor the factorization uses `sorryAx`.
   The unchanged direct consumers `AffineOrdinaryTensorStalkCoordinates` and
   `AffineBaseChangeOrdinaryStalkComparison` compiled against the delivered
   coordinate definition in 54.4 s and 25.5 s, respectively, without warnings.
   Their temporary source copies were removed from the delivery tree.

3. **Split statements and existing results: PASS, no hole left.** The proposed
   factorization is a strictly smaller algebraic step: it has no point, stalk,
   localization or quasi-coherence hypothesis. I checked its expansion against
   the actual global coordinate definition and proved it. The general localization
   lemma applies to arbitrary sheaf morphisms, including zero morphisms, not just
   isomorphisms; arbitrary degrees and zero modules cause no exception, and a zero
   ring has no prime. Additional Loogle search for `CategoryTheory.Functor.map_comp`
   and LeanFinder search for global sections of isomorphism composites returned
   composition ingredients, not an existing coordinate theorem. Source searches
   in Mathlib, `lean/Sheaf` and `lean/WeilConjectures` confirmed that the existing
   derived-cohomology naturality theorem treats derived-object morphisms, whereas
   the new localization theorem treats arbitrary homology-sheaf morphisms.

4. **Top-down route and pruning: PASS.** The item uses the proved global-sections
   factorization and localization identity, then functoriality. The imports expose
   definitions needed by public data and signatures; the two theorem dependencies
   are plain proof-only imports. The report enumerates every replaced old direct
   proof dependency; those dependencies remain used transitively. No module is
   pruned. The unit `sk-thm-picard-semicon` has empty realized lists, and the affine
   tensor-comparison/localization route is retained. Its referenced blueprint
   source file is absent locally; I checked the unit's stored statement and steps.

5. **DAG and Lean agreement: PASS.** Each of the five delivered node Lean statement
   strings exactly matches its declaration signature. Proof steps and dependency
   unions describe the actual factorization, naturality, triangle and composition
   arguments. The helper's statement dependencies are the four requested nodes;
   an overlay traversal of 394 nodes finds no path back to the helper. I updated
   the factorization's proof origin to name the definition expansions and the
   composition lemmas actually used.

Second-reading changes: completed
`AlgebraicGeometry.affineBaseChangeTildeCohomologyIso_globalSections_factorization`
by unfolding the original and extracted definitions, simplifying the forward maps
of composite isomorphisms and functor composition, then `rfl`. The local heartbeat
option documents the elaboration cost; the standard 60-second file limit is
unchanged. Updated the factorization proof origin and the current report to record
one original hole closed, zero holes added, and no remaining split-off hole.
Existing signatures, definitions, imports and all other correct proofs were left
as received.

## Second reading by T4

1. **Interfaces: PASS.** I diffed the item against the repository and ran the
   declaration comparison: all three existing signatures are unchanged. The
   declared definition refactoring extracts exactly the original TA, TB, E,
   additive instances, chosen tensor comparison and three homology factors.
   Localization and the original linear-equivalence projections are retained.
   The change records account for the definition and statement-dependency edits;
   no target or consumer source is changed.

2. **Proofs: PASS.** The item compiled locally without errors or warnings. The
   delivery dry run rebuilds all four modules in import order and probes their
   axioms. I separately compiled a scratch import printing the axioms of all ten
   public declarations: only propext, Classical.choice and Quot.sound occur.
   The delivered sources contain no sorry or forbidden declaration form. The
   extracted construction uses the same comparison chosen from the proved
   canonical unit-compatibility theorem, not an arbitrary unproved witness.

3. **Intermediate statements: PASS.** No split-off hole remains. The factorization
   is verified by expansion and composition laws, before any localization. The
   generic stalk identity applies to arbitrary morphisms from tilde V; its proof
   uses localization naturality and the adjunction triangle. Zero modules, zero
   morphisms and arbitrary degrees introduce no exception; zero rings have no
   prime. I searched again for counit naturality and map_iso_commute in both
   library roots and queried Loogle for CategoryTheory.Adjunction.left_triangle_components. These give existing ingredients,
   not a duplicate of the general coordinate identity. The private numerator
   naturality result is reused through proof-only import all.

4. **Route and pruning: PASS.** The proof reduces the original counit hole to
   global-sections factorization and generic localization, then functoriality.
   Public imports support public signatures or definition bodies; theorem-only
   dependencies are plain imports. The report lists all replaced old direct
   dependency edges; they remain needed transitively. No module is pruned. I
   checked sk-thm-picard-semicon's stored statement, step and empty realized lists;
   no populated realization or unit argument is bypassed.

5. **DAG: PASS.** All five delivered nodes name existing delivered declarations.
   Every proof_deps set equals the union of its proof steps' uses. The proof
   origins accurately describe definition expansion, localization naturality,
   adjunction and functor composition. The new nodes include source, searches,
   blueprint origin and Lean records; the dependency correction has its change
   record.

Changes in this reading: appended this current independent review and recorded
an additional search. No Lean proof, signature, definition or node needed repair.
The closure count remains one original hole closed, zero holes added, with no
remaining split-off hole.

Fresh compatibility checks in this reading: unchanged repository copies of
AffineOrdinaryTensorStalkCoordinates and AffineBaseChangeOrdinaryStalkComparison
compiled against the final delivered artifacts in 50.4 s and 25.3 s, respectively,
with no errors or warnings and the standard 60-second limit.
