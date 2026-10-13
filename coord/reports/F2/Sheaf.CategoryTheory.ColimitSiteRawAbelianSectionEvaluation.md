## What changed

Proved `CategoryTheory.colimit_site_raw_abelian_section_evaluation` with its original
signature, visibility and docstring unchanged. The proof constructs the section cocone,
descends from the chosen colimit of D, proves the resulting additive map bijective,
uses `asIso`, and proves the requested evaluation formula by naturality and `ha`.
Added four proved helper modules, imported only by proofs:

- `Sheaf.CategoryTheory.ColimitSiteRawAbelianSectionGenerators`: lifts an individual
  abelian Kan generator; the union of the compatible section images is an additive
  subgroup; the Kan universal property shows this subgroup contains every section.
- `Sheaf.CategoryTheory.ColimitSiteRawAbelianSectionRelations`: normalizes the stage
  maps, uses the outer filtered-colimit equality criterion, and reduces to a
  pointwise Kan-unit equality before cancelling E and the endpoint transport.
- `Sheaf.CategoryTheory.ColimitSiteAbelianKanUnitRelations`: identifies equality in
  the abelian Kan colimit with a finite integer linear combination of single-arrow
  relations using Mathlib's quotient of direct sums, then evaluates that finite
  expression at one stage.
- `Sheaf.CategoryTheory.ColimitSiteFiniteRestrictionFamilyLift`: explicitly lifts
  finitely many arrows with prescribed endpoints and makes all requested triangles
  and the base identity hold after one refinement. Its arrow lifting, finite-stage equality and Arrow composition helpers are
  reused from existing proved modules via proof-only `import all`.

The target module adds proof imports of the first two modules, filtered-colimit
set tools, the filteredness of Under i, and the concrete bijectivity criterion.
The item node and four new nodes record this actual route. No existing definition
or statement was changed, and no downstream adaptation is needed.

All five modules compile without warnings through `lcompile.py --all` (each takes
under ten seconds). The same-stage and two-stage object/arrow equality criteria,
wideSpan, pointwise Kan cocones, abelian quotient presentation, and finite-support
closure results were read in Mathlib. LeanSearch was unavailable; LeanFinder,
Loogle, repository search, and Mathlib grep were also run. No exact existing
abelian theorem was found. The set-valued generator, relation and evaluation
proofs supplied the transport calculations; their Type-valued statements are
not applied to abelian Kan colimits.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.colimit_site_raw_abelian_section_evaluation`
(node `lem-weil-pbc-colimit-site-raw-abelian-section-evaluation`).

Also proved every new public theorem:
`CategoryTheory.raw_abelian_section_generators`,
`CategoryTheory.raw_abelian_section_relations`,
`CategoryTheory.raw_abelian_section_kan_unit_relations`, and
`CategoryTheory.colimit_site_finite_restriction_family_lift`.
Every private helper is proved. There are no sorries in any delivered module;
zero holes are added or split off. This is a proof, not a decomposition.

The finite lifting proof includes an empty edge family: its finite comparison
family still includes the base identity. An empty object family is excluded by
the distinguished base object in that helper's own statement. The representative
proof handles zero by the identity object of Under i, and sums by a common
refinement, so neither nonzero groups nor a nonempty sum of Kan generators is
assumed. The relation proof works with empty support (the unit object remains
in the selected finite set), repeated objects, loops, and zero integer
coefficients. No stage category is assumed finite, and theta maps in the
pointwise relation theorem need not form a diagram. No sheaf or finite-cover
condition is imposed on the raw colimit or the presheaf T.

## No longer needed

Removed the proof-dependency edge to
`lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction`: its adjunction is
present in the unchanged signature but no adjunction property is invoked in
this proof. The original `hθ` hypothesis is not needed by the proof; it is
explicitly acknowledged without changing the item's signature. The direct
proof edge to `def-weil-pbc-sites-and-cohomology` is also removed from the item:
it remains a statement dependency of the new sheaf-based helpers and is not
globally pruned. The new helper
statements omit it, the topology Q, and continuity of the cocone legs.

No original import is removed: the public imports supply the unchanged
statement's category, sheaf pullbacks and abelian (co)limit instances. No
existing module can be declared globally unreachable by this delivery. The
set-valued modules `ColimitSiteRawSectionPresentation`,
`ColimitSiteRawSectionCompatibility`, `ColimitSiteRawSectionRelations`, and
`ColimitSiteKanUnitRelations` are not imported as proof dependencies.
`ColimitSiteRawSectionGenerators` is imported proof-only with `import all` to
reuse its proved private arrow lifts; `FilteredColimitFiniteIsoLift` similarly
supplies its proved finite-equality and Arrow-composition helpers. The
Type-valued section theorem is not used for an abelian Kan colimit.
The planned arbitrary inverse construction is replaced by a proved bijective
additive comparison map and its canonical isomorphism.

## Where the brief, the DAG or earlier work was wrong

Repair of the landing refusal at a3fda992c: removed the three duplicated
private statements identified in `ColimitSiteFiniteRestrictionFamilyLift`.
The existing statements are private, so proof-only `import all` accesses them
without changing their visibility. Also removed both duplicated arrow-lift
helpers in the new abelian generator module and reused the existing ones.
Compilation confirms all references resolve. Updated the two new node proof
plans and dependencies to record this reuse. No existing module is adapted,
and all public signatures are unchanged. The previous second-reading section
below predates this repair and is left for the independent reader to update.

No false statement was found. The original plan leaves the finite abelian
relation calculation implicit; this delivery supplies it with the actual
Mathlib quotient presentation and a finite support witness. A set-valued Kan
representative theorem would be insufficient for abelian colimits, since the
forgetful functor need not preserve the inner, unfiltered Kan colimit. The
subgroup argument for existence and the finite linear relation proof avoid
that mistake. Forgetting to sets is used only for the outer filtered colimits.

The clone has no `literature/stacks-project/sites.tex`. Read the source online:
[Tag 0A35](https://stacks.math.columbia.edu/tag/0A35),
[Tag 03CO](https://stacks.math.columbia.edu/tag/03CO), and
[Tag 09YL](https://stacks.math.columbia.edu/tag/09YL).
The raw abelian argument expands the independence checks omitted in 0A35;
proof_origin is marked as written by an agent. No unit statement or realized
unit step is bypassed; all new nodes remain in `sk-thm-p1`.

`blueprint_refs.py ancestor` returns None for the assigned node and its parent:
the inherited stage-3 ancestry chain already terminates at a null reference.
The new nodes are therefore explicitly anchored to the assigned raw-abelian
evaluation node and its numbered proof steps, as its own node is anchored to
its stage-3 parent. This delivery does not alter that inherited metadata.

## New nodes

`lem-weil-pbc-colimit-site-raw-abelian-section-generators`, in
`ColimitSiteRawAbelianSectionGenerators.lean`, states joint stage representative
existence for the canonical compatible additive section maps. It is proved,
including the finite-sum content by an additive subgroup universal-property
argument, and is the existence half of the item comparison.

`lem-weil-pbc-colimit-site-raw-abelian-section-relations`, in
`ColimitSiteRawAbelianSectionRelations.lean`, states eventual equality of two
D representatives having equal raw images. It is proved from the outer
filtered equality criterion and the following pointwise relation theorem.

`lem-weil-pbc-colimit-site-abelian-kan-unit-relations`, in
`ColimitSiteAbelianKanUnitRelations.lean`, states eventual equality of two
unit images in one abelian pointwise Kan extension. It is proved for arbitrary
stage presheaves and natural theta maps, without sheaf/topology data, outer
B diagram, section diagram D, or compatibility between theta maps.

`lem-weil-pbc-colimit-site-finite-restriction-family-lift`, in
`ColimitSiteFiniteRestrictionFamilyLift.lean`, states simultaneous lifting of
finitely many restriction arrows, their selected triangles, and a base
identity above a fixed stage. It is proved using the existing private arrow-lifting,
finite-equality and composition helpers, followed by the local same-stage
refinement and finite-family construction. It involves no abelian groups or sheaves.

All four new nodes have source, complete proof steps, actual three-kind search
records, the exact Lean statement, and the same chapter/unit as the item.
No change record is required: existing interfaces remain identical.

## Earlier second reading (a previous round; superseded)

1. I compared the delivered item module with the repository version. The target
   theorem signature, visibility, and docstring are byte-for-byte unchanged; the
   delivery only fills its proof and adds proof imports.

2. I compiled all five delivered modules with `lcompile.py --all`. They compile
   without errors or warnings. I found no `sorry`, `axiom`, `unsafe`, `opaque`,
   `extern`, or `implemented_by`; the only public declarations are the target
   and the four documented helper theorems.

3. I checked each split-off helper against its node and searched the existing
   Sheaf and Mathlib sources for duplicate declarations. The four statements
   are strictly smaller than the target, true in the stated edge cases, and
   have matching source, proof, dependencies, and Lean records.

4. The proof follows the unit route: it builds the canonical cocone, proves
   surjectivity and injectivity using the generator and relation lemmas, and
   obtains the isomorphism with `asIso`. The helper imports are proof-only where
   possible, and the report's no-longer-needed dependencies agree with the
   actual proof. No definition or existing statement was changed.

5. The DAG nodes record the exact declarations and proof dependencies used by
   the modules. The realized unit and chapter are unchanged, and no new hole is
   left in the delivery.

I changed only this report section; no Lean source or node content required
   repair after the second reading.


## Second reading by F2

1. Compared every delivered module with its repository counterpart. Only the
   item module exists in the baseline; its existing theorem signature, visibility,
   and docstring are byte-for-byte unchanged. The four other modules introduce
   proved helper statements. No existing definition is changed, no new hypothesis
   is added to the item, and no change record or forced adaptation is required.
   Verdict: pass.

2. Independently compiled all five modules using `lcompile.py --all`, without
   warnings. Scanned the delivered sources for sorry and forbidden declarations;
   none occur. Checked the target and four public helpers with `#print axioms`
   in a scratch copy; the delivery tool additionally probes every constant.
   The cocone and isomorphism are constructed from the chosen colimit and a
   proved bijective comparison; no arbitrary data witness is chosen from an
   unproved existence theorem. All five printed exactly propext, Classical.choice, and Quot.sound.
   Verdict: pass.

3. Read each of the four new statements and its complete proof. None is left
   sorry or merely restates the item. The generator theorem proves existence;
   the relation theorem proves eventual equality; the Kan theorem treats only
   one stage's unit kernel; finite lifting has no abelian or sheaf data. Checked
   zero sections, empty relation support and edge families, repeated objects,
   and identity edges. The base object rules out an empty object family where
   appropriate. The finite relation proof requires no coherence between theta
   maps, because it uses naturality of one selected theta map. Independent
   LeanFinder, Loogle, Mathlib grep, and repository searches found supporting
   quotient/finite-support lemmas and the existing private arrow lifts, which
   are reused, but no exact existing abelian theorem. Verdict: pass.

4. Read the target downward through both section helpers, the pointwise Kan
   relation proof, and finite lifting. The subgroup argument handles finite sums
   of inner Kan generators without falsely claiming that forgetting to sets
   preserves an unfiltered abelian colimit. Only the outer filtered colimits
   use set representatives and eventual equality. The proof retains the unit's
   realized route. Both removed old proof dependencies are recorded above;
   no module is claimed globally pruned. The added helper imports are proof-only.
   Tested privatizing the filtered-colimit import in the new sheaf-based helper:
   its public signature then fails to synthesize HasWeakSheafify, so restored
   that necessary public import. Verdict: pass.

5. Checked all five node Lean records against the parsed declarations, the
   union of each proof step's uses against proof_deps, the existing node's
   removed dependencies, and the new nodes' source, search, creation, chapter,
   unit, and blueprint records. The existing private helpers referenced by the
   repaired proof are proved and their module nodes are recorded. The realized
   unit record is unchanged. Verdict: pass.

Changed the pruning report to acknowledge the proof-only imports of
ColimitSiteRawSectionGenerators and FilteredColimitFiniteIsoLift introduced by
this repair. No Lean proof or node repair was needed. Independent search logs
were added only to the sandbox's search record; they are not delivered files.
