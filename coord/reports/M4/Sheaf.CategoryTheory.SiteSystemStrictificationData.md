## What changed

Proved `CategoryTheory.exists_site_system_strictification_data` completely for the corrected
finite-index output axioms. Its inputs, universes, coefficient equalities, and Arrow equation
are unchanged. The old output was already formally refuted; the correction follows Stacks
0A34 and 09YL. The pair categories, transitions, evaluations, inclusions, coefficients and
theta are concrete constructions. All categorical, covering, pullback, continuity and sheaf
exactness arguments compile, without a new deferred theorem.

Added three fully proved construction/API modules: `SiteSystemStrictificationCategory`,
`SiteSystemFiniteCoverings`, and `SiteSystemFiniteSheafTransport`. The continuity proof uses
finite pullback coverings and Mathlib's pairwise-pullback sheaf criterion. Sheaf exactness
uses inverse pushforwards for equivalences, composed adjunctions, and uniqueness of left
adjoints. This avoids the original transport lemma's unrestricted precoverage hypotheses.

`exists_site_system_strictification` has the corresponding finite output correction and
retains its complete colimit construction. In `AffineFreeEtaleModuleFamilyModels`, replaced
the sole use of `exists_affineEtaleSite_colimit` by the already stated base-change-system
and object-descent theorems. Its signature is identical. Removed six unused imports of the
same affine colimit package. All six import-only consumers compile unchanged against the changed dependencies; the additional ConstructibleLimitDescentGeneral consumer is adapted below because it calls the withdrawn theorem.

Replaced `AffineEtaleColimitPresentation` and `AffineEtaleSiteColimit` with empty withdrawal
modules. The false declarations are removed while the module names remain available to the
unadapted import-only consumer `LimitHigherDirectImageExchange`; this is necessary because the
landing tool preserves module paths and checks all importers.
The former was proved by contradiction from the false old strictification assertion; the
latter included that false conclusion. Neither is needed by the actual proofs. Their DAG
nodes remain, with null Lean attachments. This does not install weakened replacements.
The complete interface/pruning record is
`coord/changes/site-system-strictification-finite-and-prune.md`.

## Proved and sorry left

Closed the sole hole in `CategoryTheory.exists_site_system_strictification_data`, after
correcting its two false output axioms. This is a corrected statement with a complete proof,
not a proof of the original false assertion and not a decomposition.

New holes: none. Split-off holes: none. No `sorry` remains in any new module or in the item's
module. The corrected general caller `CategoryTheory.exists_site_system_strictification`
also has no holes. All new construction/API declarations are proved. The withdrawn false
affine declarations are retired, not counted as proofs.

The new proofs use only the permitted axioms; the dry run checks every declaration.
No target statement is changed. Every live adapted theorem preserves its statement, except
for the explicitly recorded finite-index conclusion of the general strictification caller.

## No longer needed

Removed the proof import `Sheaf.CategoryTheory.SiteEquivalenceMorphismTransport` from the
item. Its node `lem-weil-pbc-site-equivalence-morphism-transport` and its original route via
`SiteEquivalenceMorphismOfSites` and `SiteMorphismComposition` are unnecessary for this proof.
The finite-family sheaf transport API supplies the required argument directly from Mathlib.
These modules can still be needed by other library proofs; no global withdrawal is claimed.

The seven live consumer modules no longer import `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`.
Consequently the false formal packages `AffineEtaleSiteColimit` and
`AffineEtaleColimitPresentation`, nodes `lem-weil-pbc-affine-etale-site-colimit` and
`lem-weil-pbc-affine-etale-colimit-presentation`, are withdrawn from the active Lean route.
The only actual theorem use was object descent in `AffineFreeEtaleModuleFamilyModels`;
`AffineEtaleBaseChangeSystem` and `AffineEtaleDescentData` supply exactly that data.
The proof-dependency-only imports of `SiteSystemStrictificationRefuted`,
`SiteSystemStrictificationObstruction`, `SiteSystemStrictificationData`, and
`SiteSystemStrictification` from the removed affine branch are therefore unnecessary for
that route. The strictification modules are still proved in this delivery as requested.

Corrected the stale proof_deps of `lem-weil-pbc-etale-limit-scalar-section-continuity` to
its actual two proof steps: scalar representatives and eventual zero. Its former list
included affine colimit, colimit-site sections, colimit sites, fibre-product pasting,
qcqs permanence and topos transport which its Lean proof does not use.
All realized statement/step nodes of sk-thm-p1 are retained.

Second reading also removed these unused direct imports (all confirmed by compilation):

- `Mathlib.CategoryTheory.Limits.Preserves.Limits` from `SiteSystemFiniteCoverings`;
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`,
  `Sheaf.AlgebraicGeometry.FullAffineEtaleTopos`, `Sheaf.CategoryTheory.ColimitSiteSections`,
  `Sheaf.CategoryTheory.ColimitSites`, and
  `Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit` from
  `EtaleLimitScalarSectionContinuity`;
- `Sheaf.AlgebraicGeometry.FullAffineEtaleTopos`,
  `Sheaf.AlgebraicGeometry.LimitAffineTransition`, `Sheaf.CategoryTheory.ColimitSiteSections`,
  and `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek` from
  `EtaleLimitAffineDegreeZeroKernel`;
- `Sheaf.CategoryTheory.ColimitSites` and
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs` from both
  `AffineOpenSectionsDescent` and `AffineOpenSectionsZeroDetection`.

For completeness, the original scalar-continuity proof dependency list loses exactly
`lem-weil-pbc-scheme-over-limit`, `lem-weil-pbc-qcqs-morphism-permanence`,
`lem-weil-pbc-cartesian-square-pasting`, `lem-weil-pbc-affine-etale-site-colimit`,
`lem-weil-pbc-affine-etale-site-topos`, `lem-weil-pbc-colimit-of-sites-sections`,
`lem-weil-pbc-filtered-colimits-commute-finite-limits`, and `lem-weil-pbc-colimit-of-sites`.
The item also no longer has `def-weil-pbc-sites-and-cohomology` as a proof dependency;
it remains a statement dependency. These are removals from these proofs, not claims that
all those modules are globally unreachable.

## Where the brief, the DAG or earlier work was wrong

Repair of reviewer X-4bdd9, head 4bdd9de02 (2026-10-15):

- H2: replaced the entire `lean` attachment object with `null` in
  `lem-weil-pbc-affine-etale-colimit-presentation.json` and
  `lem-weil-pbc-affine-etale-site-colimit.json`. Both withdrawn modules contain no
  declarations, so neither node now claims a removed Lean declaration. All other
  node fields and the corrected finite-index Lean proofs are unchanged.


Repair of reviewer X-20733's return (2026-10-14):

- B3: appended `def-weil-pbc-finite-precoverage` as the final statement dependency of
  `lem-weil-pbc-affine-etale-colimit-presentation`, immediately after
  `def-weil-pbc-category-colimit`, because the corrected statement uses finite indexed axioms.
  Recorded the original list in `statement_change.old_stmt_deps`, as preflight requires.
- B9: corrected all three new nodes' blueprint provenance to
  `lemma-weil-pbc-injective-restriction-acyclicity`, with the four-node strictification and
  affine-site/cohomology path in the requested order and the requested source-place text.
  Set all three `same_as` fields to `[]`; the review's searches found no blueprint node
  stating these constructions.

The corrected finite-index Lean statements and their complete proofs are retained.
Kept the two empty withdrawal modules in the delivery instead of `deleted.txt`, so the landing
can preserve the module paths for the remaining import-only consumer. No withdrawn declaration is
reintroduced.


The old data theorem was marked STATEMENT-DISPUTED and had a complete formal refutation.
Finite covering presieves do not imply stability under arbitrary repeated indexed families.
Labels in strictification create infinitely many distinct isomorphic source objects;
arbitrary indexed base change then forces an infinite covering. The new Q uses finite
indexed composition and base change, with singleton isos and covering pullbacks intact.
The original P hypotheses remain unchanged. This correction does not touch any target.

The affine presentation's old contradiction proof was not a construction. Its site axioms
were themselves false for finite affine coverings (arbitrarily many singleton fold covers
composed with repetitions of the identity). Its only useful data were already in its
base-change/descent predecessors, so the false formal package and its unused wrapper are
withdrawn. The source mathematical nodes are retained rather than supplied another false
or merely renamed hole. No statement is weakened under the old affine names.

The main and general strictification nodes carry statement_change records, with every DAG
citer assessed. The withdrawn affine presentation node records finite indexed axioms and
withdrawal of its false attachment. All its mathematical citers continue to make sense;
its former Lean caller is withdrawn, and the remaining live proof uses descent directly.

## New nodes

`lem-weil-pbc-site-system-strictification-category`: explicit labelled categories, gamma
transitions and diagram, evaluation equivalences, delta coefficient functors, and theta.
Every construction and property is proved; no data are chosen from an unproved theorem.

`lem-weil-pbc-site-system-finite-coverings`: finite presieves detected by evaluation,
finite covering axioms, covering reflection and indexed lifts, and transition preservation.
It uses the existing finite-precoverage definition and isomorphic-family lemma.

`lem-weil-pbc-site-system-finite-sheaf-transport`: continuity from finite covering pullbacks,
exactness of evaluation/section sheaf equivalences, composition of pullback adjunctions,
and transport along natural isomorphisms. Every theorem is proved from Mathlib and the
proved finite covering construction. No new work item is left with a hole.

Change record: `coord/changes/site-system-strictification-finite-and-prune.md`.

## Earlier second reading (a previous round; superseded)

1. **Interface and accidental changes.** I diffed every delivered module against the repository
version. Existing declaration signatures are unchanged except for the two finite-index output
axioms explicitly recorded in `coord/changes/site-system-strictification-finite-and-prune.md`.
The adapted consumer theorem signatures are byte-for-byte unchanged. The withdrawn affine modules
are absent from the sandbox and have no remaining importers in the delivered set.

2. **Proof and trust basis.** I compiled all twelve delivered modules with `lcompile.py`, including
the dependency order, and added scratch `#print axioms` checks for the main theorem, its general
caller, and representative construction and transport declarations. They use only `propext`,
`Classical.choice`, and `Quot.sound`; there are no `sorry`s, axioms, unsafe or opaque declarations,
or hollow definitions.

3. **Statements and new nodes.** I checked the three new construction/API nodes against their Lean
declarations and searched the repository and Mathlib for existing strictification or equivalent
finite-site statements. The pair-category, finite-covering, and sheaf-transport statements are
strictly component lemmas used by the main proof, with explicit constructions and no deferred data.
Empty categories cause no essential-surjectivity problem, since its witness is chosen for each
existing target object. Empty covering indices give empty finite sigma indices, repeated finite
members remain finite, and singleton stages reduce to the normalized identity comparisons. The
old infinite-label counterexample is excluded only from the unrestricted output base-change
claim; the corrected theorem retains its strict coefficients and arbitrary indexed lifting clause.
The corrected finite composition/base-change clauses agree with Stacks 0A34 and 09YL.

4. **Pruning and dependencies.** I verified the proof dependency fields against the imports and
proof calls. The old site-equivalence transport import is gone from the item; the affine colimit
package imports and the five stale scalar-continuity imports are removed where compilation shows
they are unnecessary. The finite-sigma import is retained because finite composition needs its
instance. The realized route of unit `sk-thm-p1` remains intact.

5. **Verdict.** The item proves its original open declaration after the explicitly documented
mathematical correction, closes no target by weakening, and adds no split-off holes. The direct
construction, finite covering transport, continuity, and exactness arguments are all typechecked.

Changes made during second reading: retained the required finite-sigma proof import after a
compile test; removed fourteen redundant imports from the new covering API, scalar wrapper,
degree-zero kernel and two affine-open consumer modules; completed the removed-dependency list;
and recorded this review. No proof body or additional signature was changed by this reader.

## Forced adaptations

The changed finite-index strictification interface forced the following four existing
modules (and the one direct theorem consumer) to be adapted. These are the original
compiler diagnostics against the changed dependencies and the exact necessary edits.

### AffineEtaleColimitPresentation

The original file failed at line 230 with a finite-stability type mismatch: the call to
`exists_site_system_strictification_data` produced `IsStableUnderFiniteComposition` and
`IsStableUnderFiniteBaseChange`, while the old conclusion required
`IsStableUnderComposition` and `IsStableUnderBaseChange`. The module is replaced by the three-line withdrawal module, so the old line-230 call and its
false unrestricted conclusion are removed entirely.

### AffineEtaleSiteColimit

The original file failed at line 357 with `unknown identifier
exists_affineEtale_colimit_presentation`, after that false presentation module was
withdrawn. Its old theorem and line-357 call are removed entirely and replaced by the three-line
withdrawal module.

### AffineFreeEtaleModuleFamilyModels

The original file failed at line 190 with `unknown identifier
exists_affineEtaleSite_colimit`. The necessary edits are imports at lines 11--12,
replacing the withdrawn site-colimit import with `AffineEtaleBaseChangeSystem` and
`AffineEtaleDescentData`, and the proof body at lines 191--195: obtain the base-change
system, extract `h1`, `hpb`, `h7`, `h10`, `h12`, then obtain `hdesc` from
`affineEtale_descent_data` and continue with the existing finite-family argument. The
public theorem signature is unchanged.

### SiteSystemStrictification

The original file failed at line 185 with two application type mismatches: `hcomp` had
type `∀ i, (Q i).IsStableUnderFiniteComposition` where
`IsStableUnderComposition` was expected, and `hbase` had type
`∀ i, (Q i).IsStableUnderFiniteBaseChange` where `IsStableUnderBaseChange` was
expected. The necessary edit is exactly the output tuple at lines 94--95 of the
strictification statement and the matching tuple construction at line 185; both old
unrestricted fields are replaced by their finite-index fields. The theorem's other
arguments and conclusion are unchanged.

### ConstructibleLimitDescentGeneral

This consumer was not import-only: after withdrawal its original line 193 call failed
with `unknown identifier exists_affineEtaleSite_colimit`. The forced, signature-preserving
edit adds `AffineEtaleBaseChangeSystem` and `AffineEtaleDescentData` at imports 11--12,
removes the withdrawn import, and replaces lines 195--199 with the same base-change and
`affineEtale_descent_data` extraction used above. It compiles in the delivered set.

The six genuinely import-only consumer edits are `EtaleSetEventualLocalStageMatching`,
`EtaleSetFiniteLocalStageRepresentatives`, `EtaleLimitScalarSectionContinuity`,
`EtaleLimitAffineDegreeZeroKernel`, `AffineOpenSectionsDescent`, and
`AffineOpenSectionsZeroDetection`. Each compiles unchanged against the changed
 dependencies and is therefore a pruning edit, not a forced adaptation. No unnecessary
consumer edit is retained.

## Earlier second reading (a previous round; superseded)

This is an independent reading of the repaired delivery after return X-20733.

1. **Interfaces: pass.** I diffed all twelve delivered modules against the repository
   snapshot and checked the declaration tables. The only existing signatures that change
   are `CategoryTheory.exists_site_system_strictification_data` and
   `CategoryTheory.exists_site_system_strictification`: precisely the two recorded output
   replacements by `IsStableUnderFiniteComposition` and `IsStableUnderFiniteBaseChange`.
   All inputs, universes, coefficient equalities and the Arrow equation are unchanged.
   The seven live consumer modules preserve every existing signature. The change record
   covers both corrections, the two withdrawals and all seven consumers. I checked the
   original affine-presentation proof: it really eliminates the contradiction between
   the old assertion and its refutation. Withdrawing it removes an invalid proof route.
   No target declaration or definition used by a target is changed.

2. **Proofs and axioms: pass.** I compiled all twelve modules in import order with
   `lcompile.py --all`; all compiled without errors or warnings. A source scan finds no
   `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, explicit `sorryAx`
   or kernel-check bypass in the delivered modules. Fresh scratch copies with
   `#print axioms` check both main strictification declarations, `SiteSystemPairs.diagram`,
   `SiteSystemPairs.coefficients`, `finiteEquivalencePrecoverage`,
   `continuous_of_finite_pullbacks` and `continuous_transport_pullback_exact`.
   Every result uses only `propext`, `Classical.choice` and `Quot.sound`. In particular,
   the explicit category and coefficient data do not depend on an unproved existence
   theorem. The remaining equivalence choices are inverses with their unit/counit laws.

3. **New statements and edge cases: pass.** There are no split-off holes. I read all
   three new modules. The pair construction defines objects, arrows and coefficients
   explicitly; `transition_comp` uses the gamma cocycle at both endpoints and naturality,
   and `transition_coefficients` uses the delta cocycle and naturality. Normalization is
   used exactly for identities, restriction along inclusion and the theta calculation.
   Empty fibres require no chosen object: essential surjectivity is proved separately
   for each existing target object. Empty finite covering indices give empty sigma
   indices; repeated finite members remain finite. The covering lift uses the inverse
   equivalence on the entire indexed family, so its unrestricted index does not require
   an unjustified finiteness assumption on the family. The continuity proof represents
   each covering by its finite type of distinct arrows before applying finite base change.
   Sheaf exactness uses inverse continuous pushforwards and uniqueness of left adjoints.
   I checked the sources [004A](https://stacks.math.columbia.edu/tag/004A),
   [0A34](https://stacks.math.columbia.edu/tag/0A34),
   [09YL](https://stacks.math.columbia.edu/tag/09YL) and the strictification comment at
   [0EYL](https://stacks.math.columbia.edu/tag/0EYL). These support the pair construction
   and finite-index interpretation. Independent LeanFinder search for a Grothendieck
   construction returned the general pseudofunctor total categories, not this strict
   coefficient construction. Loogle and direct Mathlib inspection found
   `isContinuous_toGrothendieck_of_pullbacksPreservedBy`, whose unrestricted base-change
   assumptions prevent its use here. I also inspected `Equivalence.sheafCongr` and
   `Adjunction.leftAdjointUniq`; the proof already uses the latter and constructs the
   former's required sheaf equivalence directly from continuity. A search for split
   fibred categories and rectification found no replacement for the new construction.

4. **Pruning and unit route: pass.** The main proof uses precisely the pair-category,
   finite-covering and finite-sheaf-transport APIs recorded by its three proof steps.
   The removed unrestricted site-transport theorem cannot handle the corrected outputs.
   I checked every importer of both withdrawn affine modules: the delivered seven
   consumers and the withdrawn wrapper exhaust them. The sole actual theorem use is
   replaced by the base-change-system and object-descent declarations, with the same
   finite common-stage argument afterward. The report names the removed dependencies,
   including the stale scalar-continuity list. Proof-only imports are plain imports;
   public imports supply public statements or definitions. The `sk-thm-p1` realized
   statement and every realized step remain in the route; neither withdrawn node is a
   realized statement or step of that unit.

5. **DAG and return repairs: pass.** I compared the nine delivered node records with
   the Lean proof calls and the original records. The item's three proof steps and
   `proof_deps` agree with the construction, covering and transport modules. The general
   caller still uses strictification data, colimit sites and filtered functor descent.
   The affine-family node now names the two declarations actually used; the scalar
   wrapper names exactly its representatives and eventual-zero dependencies. The two
   withdrawn attachments are null, without renaming a false statement as a new hole.
   All three new records contain source, proof, searches, created, chapter, unit and Lean
   fields. For X-20733 B3, `def-weil-pbc-finite-precoverage` is the final affine-presentation
   statement dependency and `old_stmt_deps` records the original list. For B9, all three
   new nodes have exactly the requested blueprint ancestor, ordered four-node path,
   source-place text and `same_as: []`. Existing statement corrections record their
   old statements and assess their citers.

Changes made in this second reading: appended this independent review and refreshed scratch
axiom checks and search evidence. No further Lean or node repair was necessary. The single
original item hole is closed for the explicitly corrected statement; no new hole is added.
This is a correction with a complete proof, not a proof of the refuted old statement.

## Earlier second reading (a previous round; superseded)

1. **Interfaces and accidental changes.** I compared every delivered Lean module with the
repository snapshot. Existing declaration signatures are unchanged except for the explicitly
recorded finite-index output changes to `exists_site_system_strictification_data` and
`exists_site_system_strictification`; consumer theorem signatures are preserved. The withdrawn affine modules are empty withdrawal modules, and their former declarations are not
replaced by weaker statements. No target declaration is changed.

2. **Proof and trust basis.** I compiled all thirteen sandbox modules with `lcompile.py --all`.
The first check exposed two failed applications in `SiteSystemStrictificationCategory`: its
local backward definitional-equality transparency options prevented the explicit comparison
components from reducing. I removed those two options and recompiled successfully. A source
scan finds no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, explicit
`sorryAx`, or kernel-check bypass. The explicit pair construction, finite covering transport,
and sheaf transport use only the permitted construction and Mathlib lemmas; no definition
chooses data from an unproved existence theorem.

3. **Statements and new nodes.** The corrected finite-index output is the statement supported
by the finite-family site axioms: arbitrary indexed composition and base change would contradict
the required finiteness. The three new nodes are strict component APIs used by the item proof,
with explicit constructions and no split-off holes. I checked empty and repeated finite families,
singleton identity covers, equivalence transport, and the Arrow endpoint equality. Repository and
Mathlib searches recorded in `searches.jsonl` found no duplicate strictification construction;
one Lean search service was unavailable and is recorded as such.

4. **Pruning and route.** The item's proof uses the pair-category, finite-covering, and finite
sheaf-transport nodes exactly as recorded. The old site-equivalence transport import is removed.
The affine colimit branch is withdrawn because its formal unrestricted site package was false;
the live consumers use the proved base-change and object-descent declarations directly. Removed
consumer imports were checked by recompilation. The realized statement and steps of unit
`sk-thm-p1` remain in the route.

5. **DAG consistency and verdict.** The node proof steps and `proof_deps` match the declarations
called by the Lean proof, and new node records contain source, searches, blueprint, chapter,
unit, and Lean fields. The finite-index statement changes and withdrawn attachments are covered
by the change record with citer assessments. Verdict: the corrected item statement is fully
proved, no new hole is added, and the delivery is ready for the stage-3 tool checks.

Changes made during this reading: removed the two transparency options that caused the category
module's natural-isomorphism elaboration to fail, and appended this review. No proof body or
public statement was otherwise changed.

## Earlier second reading (a previous round; superseded)

1. **Interfaces and accidental changes.** I compared every delivered module with the repository
version. Existing declarations are byte-for-byte unchanged except for the finite-index output
corrections to `exists_site_system_strictification_data` and
`exists_site_system_strictification`, which are declared in the change record; adapted consumer
signatures are unchanged. Verdict: pass.

2. **Proof and trust basis.** I compiled the complete sandbox with `lcompile.py --all` and the
delivery probes. The item and all new construction modules contain no `sorry`, axiom, unsafe,
opaque, extern, implemented_by, or kernel-check bypass. Axiom checks use only the permitted
axioms. Verdict: pass.

3. **Statements and new nodes.** I checked the three new node statements against their Lean
declarations, their docstrings, and the finite-family edge cases (empty and repeated families,
singleton identity covers, and empty categories). They are strictly component lemmas used by the
item, with no duplicate declaration found in the repository or Mathlib. Verdict: pass.

4. **Pruning and route.** The proof dependencies and imports match the pair-category,
finite-covering, and finite-sheaf-transport calls. Removed imports compile without their former
affine-colimit branch, and the realized route of `sk-thm-p1` remains. Verdict: pass.

5. **DAG consistency and verdict.** Node `proof`, `proof_deps`, and `proof_origin` match the
Lean proof; statement corrections and withdrawals have change records and citer assessments.
The item hole is closed for the corrected statement and no hole is added. Verdict: pass.

Changes made: added this required exact-heading review section only; no Lean proof or public
statement was changed.

## Second reading by M4

1. **Interface and accidental changes.** I compared every delivered Lean module with the
repository version. Existing theorem signatures are byte-for-byte unchanged except for the two
finite-index output corrections recorded in the change record. The two false affine packages are
represented by empty withdrawal modules, so their declarations are removed deliberately; the
remaining import-only module `LimitHigherDirectImageExchange` is left unchanged. Verdict: pass.

2. **Proof and trust basis.** I compiled the complete sandbox with `lcompile.py --all` and ran the
delivery checks. The strictification item, its three construction modules, and all adapted modules
have no `sorry`, axiom, unsafe, opaque, extern, or implemented_by declarations. The probe reports
only the permitted axioms for declarations it can inspect. Verdict: pass.

3. **Statements and new nodes.** I checked the three new node statements against their Lean
signatures and uses, including empty and repeated finite families and singleton identity covers.
They are proper component lemmas of the strictification construction, with concrete data and no
new deferred theorem. Repository and Mathlib searches found no duplicate declarations. Verdict:
pass.

4. **Pruning and route.** I checked every changed import against the proof calls. The removed
site-equivalence and affine-colimit proof imports are unused; `SiteSystemStrictificationData`
retains the finite-precoverage import needed by its public statement. The realized route of
`sk-thm-p1` remains represented in the DAG. Verdict: pass.

5. **DAG consistency and verdict.** The changed nodes' `proof`, `proof_deps`, and `proof_origin`
match the Lean proof, and the finite-index statement changes have complete change records and
citer assessments. The item hole is closed for the corrected statement; no split-off hole is
added. Verdict: pass.

Changes made by this second reading: removed the accidental adapted copy of
`LimitHigherDirectImageExchange` because its import still compiles unchanged; replaced the
`deleted.txt` withdrawal mechanism with empty withdrawal modules so all repository importers are
accounted for; corrected the report to describe that landing constraint; and added this exact
review section. No proof body or public theorem signature was changed.
