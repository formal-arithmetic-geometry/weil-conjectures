## What changed

Replaced the sole sorry in
`AlgebraicGeometry.formalComparison_completed_affine_restriction_isIso` by a complete
Lean assembly from an algebraized adjunction model and two proved general lemmas.
The original signature, public imports, and existing docstring are unchanged.

Added three modules, one public statement in each:

- `Sheaf.AlgebraicGeometry.FormalComparisonCompletedAffineAdjunctionModel` supplies
  a proper completed-base morphism, its isomorphism locus, an algebraized pullback
  isomorphism, coherent pushforward, and the two limit/section comparison maps.
  Its conclusion asserts no invertibility of the module comparison.
- `Sheaf.AlgebraicGeometry.TensorPullbackUnitRestrictionIso` proves local
  invertibility of any tensor-pullback adjunction unit where the scheme morphism
  is an isomorphism. The proof uses source-library `Modules.PullbackUnit` section
  formulas and adjunction uniqueness; no coherence or properness is needed.
- `Sheaf.AlgebraicGeometry.CompletedAffineCoherentIsoLift` proves lifting of any
  B-linear section isomorphism of coherent modules over the I-adic completion.
  A proved private density lemma upgrades B-linearity to completion-linearity
  using a Hausdorff target. The finite-module-completeness theorem supplies this
  Hausdorff property. Mathlib's affine quasi-coherent equivalence lifts the map.

The main proof constructs the algebraized comparison, proves its restriction is
invertible, lifts the two section isomorphisms, cancels the commuting squares, and
uses tilde-counit naturality to obtain conjugacy of sheaf maps. Restriction and
cancellation transfer invertibility to the supplied map. This combination is
written in the item's module, with no anonymous or private sorry.

Repair of the return at head 4c00b33c9: removed the duplicate private theorem
`AlgebraicGeometry.finite_spec_sections` from `CompletedAffineCoherentIsoLift`.
Its existing declaration in `CoherentAffineMapSupportRadical` is private, so the
lifting module now uses the proof-only
`import all Sheaf.AlgebraicGeometry.CoherentAffineMapSupportRadical` and applies
that original theorem directly. Replaced the direct `CoherentAffineSectionsFinite`
import with this import; the existing theorem retains that dependency transitively.
Updated the lifting node's first step and dependency to record the reused helper.
No existing library module, public signature, or visibility was changed.

Updated the item's DAG proof and added matching nodes for the three statements.
Only proof imports were added. No existing definitions or statements changed,
and no forced adaptations were needed.

Validation: the four sandbox modules compile in import order through lcompile.py.
The zero-completion case, zero ideal, empty open, and zero section modules require
no exclusions in the new statements or proofs. The unit result holds for arbitrary
adjunctions, by uniqueness of left adjoints. No global build or push was run.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.formalComparison_completed_affine_restriction_isIso`
(node `lem-weil-pbc-formal-comparison-completed-affine-restriction-iso`).

Proved both new auxiliary declarations without sorry:
`AlgebraicGeometry.Scheme.Modules.tensorPullback_unit_restriction_isIso`
(node `lem-weil-pbc-tensor-pullback-unit-restriction-iso`) and
`AlgebraicGeometry.completedAffine_coherent_iso_lift`
(node `lem-weil-pbc-completed-affine-coherent-iso-lift`). All private helpers are proved.

One new hole remains, in a new module:
`AlgebraicGeometry.formalComparison_completed_affine_adjunction_model`
(node `lem-weil-pbc-formal-comparison-completed-affine-adjunction-model`).
Its proof is exactly `by sorry`; its source and complete proof in words appear in
its docstring and node. It groups the original plan's flat completed-base change,
formal-functions comparison, and coherent algebraization steps. It has no
hypothesis about the restriction of the comparison map being invertible and does
not conclude that property. The two proved auxiliary lemmas and the real Lean
conjugacy argument establish the remaining parts of the original theorem.

This is a decomposition: one upper hole closed and one lower hole added, net zero
before accounting for pre-existing imported dependencies. The whole theorem is
not claimed to be axiom-free while the algebraization lemma remains sorry.

## No longer needed

Removed the new lifting module's direct proof import
`Sheaf.AlgebraicGeometry.CoherentAffineSectionsFinite`, replacing it with reuse
of the private finite-section helper in `CoherentAffineMapSupportRadical`.
The finite-section node remains needed transitively; no additional node is pruned.
The duplicate helper is deleted, rather than renamed or reproved.

No original import was removed; all six public imports support the unchanged
statement. No unused proof import remains in the four delivered modules.

The old direct dependency on
`lem-weil-pbc-quasi-coherent-finite-type-affine`
(`Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`) is not used by the new
section-isomorphism/conjugacy argument: finite sections come from
`lem-weil-pbc-coherent-affine-sections-finite`, and quasi-coherence comes from
`pqf-lem-coherent-ft-locnoeth`. This records a route replacement, not a claim that
that module is unreachable from every other target or dependency.

The remaining original flat-base-change, formal-functions, formal-system-pullback,
affine formal equivalence, proper fully faithful completion, proper coherent
pushforward, and completion Noetherianity nodes are still needed by the remaining
algebraization lemma's proof plan. Finite-module completeness is used by the proved
completed-base isomorphism lifting lemma. These nodes are not claimed pruned.
`FormalComparisonCompletedAffineModel` and `FormalAffineMorphismRealization` are
not imported: the former already depends on this item, and the latter supplies no
algebraized adjunction structure. Neither is globally claimed pruned.

### Complete accounting of old direct proof dependencies

The following old direct edges are now below the adjunction model and are
retained in its proof plan, rather than pruned:

- lem-pc-coherent-hi;
- lem-weil-pbc-adic-completion-mod-power;
- lem-weil-pbc-coherent-formal-modules-affine;
- lem-weil-pbc-flat-base-change-map-sections;
- lem-weil-pbc-flat-base-change-resolution-iso;
- lem-weil-pbc-formal-completion-fully-faithful-proper;
- lem-weil-pbc-formal-systems-pullback;
- lem-weil-pbc-noetherian-completion-flat;
- lem-weil-pbc-theorem-formal-functions.

The old direct edge lem-weil-pbc-finite-module-complete-over-complete-noetherian
is now used below CompletedAffineCoherentIsoLift. The old direct
def-pc-module-pullback edge is used below TensorPullbackUnitRestrictionIso
(and the corresponding public statement import remains). The old direct
lem-weil-pbc-quasi-coherent-finite-type-affine edge is not used by this route,
as already explained under No longer needed. These twelve entries are every
old proof_deps edge removed from the item; the two retained old direct edges
are completion Noetherianity and coherence/quasi-coherence on a locally
Noetherian scheme. No original module import was removed.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated the already existing private
`AlgebraicGeometry.finite_spec_sections`. This was an error in the earlier work:
it is repaired by importing and using that exact existing theorem, without
copying its proof. The prior second-reading text below predates this repair and
must be rechecked by the second reader.

No statement was found false. The unit's realized blueprint route is unchanged.
The existing DAG's first two geometric steps hide the completed-base adjunction
model and its natural square; these are now one explicit takeover item.
The supplied module had only statement imports, rather than the proof-dependency
imports described in the standing brief. This caused no compiler blockage.

LeanSearch returned Internal Server Error for all three new statements; the
attempts are recorded as unavailable. LeanFinder and direct source searches were
successful. Searches of the imported blueprint found no matching Zariski module
statement. Local literature payloads are absent in this read-only clone; the cited
Stacks pages were read online. The completed-base geometric argument agrees with
Tag 088B's completed-base-change and algebraization paragraphs.

## New nodes

`lem-weil-pbc-formal-comparison-completed-affine-adjunction-model`, module
`Sheaf.AlgebraicGeometry.FormalComparisonCompletedAffineAdjunctionModel`: the only
new sorry, namely the geometric algebraization and its canonical section square.
This statement is a part of the argument, not a renamed restriction-isomorphism
assertion. Its proof plan retains the original dependencies of those steps.

`lem-weil-pbc-tensor-pullback-unit-restriction-iso`, module
`Sheaf.AlgebraicGeometry.TensorPullbackUnitRestrictionIso`: proved generic local
unit theorem, applicable without the formal-module data.

`lem-weil-pbc-completed-affine-coherent-iso-lift`, module
`Sheaf.AlgebraicGeometry.CompletedAffineCoherentIsoLift`: proved completion-linearity
and affine lifting of section isomorphisms, independent of proper morphisms,
formal comparisons, exceptional ideals, or limit squares.

All nodes inherit `sec-proper-base-change` and `sk-thm-p1`. No change record is needed.


## Earlier second reading (a previous round; superseded)

1. **Interfaces: pass.** Compared every delivered module with the repository.
   Only the item's module already exists; its sole declaration's signature is
   byte for byte unchanged, including every hypothesis and the conclusion. The
   existing docstring and six public imports are unchanged. The extra imports
   are plain proof imports. All three new modules have one public theorem each,
   and their signatures exactly match their nodes. No definitions or target
   interfaces changed; no change record or forced adaptation is needed.

2. **Kernel checks: pass, with the reported model hole.** Compiled all four
   modules in import order using lcompile.py, without errors or warnings.
   Separate scratch copies with #print axioms show exactly propext,
   Classical.choice and Quot.sound for tensorPullback_unit_restriction_isIso
   and completedAffine_coherent_iso_lift. The model and the item's theorem
   additionally use sorryAx, so this is a decomposition, not an axiom-free
   proof of the item. A direct source scan finds precisely the single named
   model theorem's `by sorry`, with its source, full proof docstring and node;
   no forbidden declarations or hollow definitions. The existential model is
   eliminated locally in a theorem proof. It supplies no public definition or
   arbitrary witness used as persistent library data.

3. **New statements and search: pass.** Read the geometric model against Stacks
   Tag 088B, especially its completed-base-change and algebraization paragraphs,
   and the existing affine formal equivalence, proper full faithfulness and
   formal-system pullback statements. The model isolates the first two
   geometric steps and concludes a section square, not the restriction-isIso
   assertion. The item still proves local invertibility and conjugacy by a real
   argument. The unit lemma is independent of completion, coherence and
   properness. The lifting lemma proves completion-linearity by congruence
   modulo every ideal power and Hausdorffness, then uses tildeEquiv. Checked
   I=0, I=B (zero completion), zero modules and the empty isomorphism locus:
   none requires a missing proper-ideal or nonempty hypothesis. Repeated
   LeanFinder searches with new wording for each of the three statements,
   Loogle's unit/IsIso search, msearch grep and direct library/source rg
   searches found useful existing ingredients, but no replacement theorem.
   The remaining geometric model cannot be closed by a few-minute application
   of an existing declaration: its base-change and algebraization identifications
   still need assembly.

4. **Route and pruning: pass after completing the accounting under No longer needed.** Read the
   main proof top down: algebraized model, standard unit section formulas plus
   adjunction uniqueness, completion-linearity and affine lifting, then counit
   naturality and cancellation. Each proof import supplies declarations used in
   that argument; each public import supplies statement data or instances.
   No imported proof-only module is made public. The sk-thm-p1 realized record
   does not name this intermediate item, and no realized unit step is bypassed
   or modified. No module is claimed globally unreachable or globally pruned.

5. **DAG: pass.** Compared the existing node against its repository version:
   only proof, proof_deps and proof_origin changed. Read all three new nodes,
   checked their required fields, statement text against Lean, proof steps,
   dependency unions, sources and provenance. Their descriptions distinguish
   the model hole from the two kernel-checked auxiliary lemmas. The node's
   restriction and conjugacy steps match the Lean proof.

Changes made in this second reading: restored the one extra space before the
item's proof delimiter to make the existing signature byte-identical; corrected
CompletedAffineCoherentIsoLift's source labels to cite 00MA for finite-module
completion (031B alone presupposes separatedness); completed the dependency
accounting here; added this review. No proof term, hypothesis, conclusion,
definition or dependency edge was changed. Holes remain one closed, one added.

Validation after second reading: deliver3.py --no-push printed OK; all four
modules compiled and the preflight passed. The delivery is classified CODEX
because it adds three modules/nodes and leaves the reported model theorem open.

## Second reading by B3

1. **Interfaces: pass.** Repeated the repository/sandbox diff. The original
   declaration's signature is byte-identical through the proof delimiter, with
   the same hypotheses and conclusion. Its docstring and public imports are
   unchanged. Added imports in the existing module are proof-only. The other
   three modules are new; their public signatures match their node records.
   No definition or target statement changes and no forced adaptations occur.

2. **Proof and axioms: pass as a decomposition.** Recompiled all four modules
   in import order using lcompile.py (8.6, 3.1, 2.8 and 31.4 seconds), without
   errors or warnings. Compiled scratch copies with #print axioms for every
   delivered theorem, including both private lifting helpers. Both auxiliary
   public theorems and the private helpers use only propext, Classical.choice,
   Quot.sound. The model and original theorem additionally use sorryAx. Source
   inspection finds exactly the reported named model hole and no forbidden
   declarations, hollow definitions or hidden proof holes. Model witnesses
   are eliminated inside a proposition proof; no library data definition
   chooses an arbitrary witness from that hole. Removed all scratch probes.

3. **Statements and existing ingredients: pass.** Read the remaining geometric
   model against Stacks 088B, especially the flat completed-base-change and
   algebraization paragraphs, and read the existing affine formal equivalence,
   proper completion full-faithfulness and formal pullback statements. The
   model does not assert local invertibility; the main proof establishes it
   using the independently proved local-unit lemma and sheaf conjugacy.
   Checked zero ideal, unit ideal/zero completed ring, zero modules and empty
   open: no extra hypothesis is needed. The lifting density argument uses
   target separatedness rather than assuming continuity of an arbitrary map.
   Repeated searches with new wording using LeanFinder (local extension of
   scalars unit and proper formal existence), Loogle (IsAdicComplete.lift), and
   direct rg across the library and Mathlib. The hits provide ingredients,
   not replacements for these statements. The sole model hole still requires
   substantial geometric comparison assembly, not a short application.

4. **Route and pruning: pass.** Read the main argument top down: model, local
   unit, lifting of section isomorphisms, cancellation, counit naturality,
   restriction. Its imports supply the statement data or these proof steps.
   Rechecked the returned repair: finite_spec_sections is the original private
   helper in CoherentAffineMapSupportRadical; proof-only import all exposes it
   locally and the duplicate is absent. That helper's section-finiteness
   dependency remains transitively imported. The report accounts for every
   removed old direct dependency edge. The sk-thm-p1 realized record is
   unchanged and none of its realized steps is bypassed. No global pruning is
   claimed. Hole accounting remains one original hole closed, one new model
   hole added, hence a decomposition with net zero new-hole reduction.

5. **DAG: pass.** Checked all four node records against Lean. New Lean statement
   records match exactly after trimming trailing whitespace; every proof_deps
   set equals the union of its proof steps' uses. Only proof, proof_deps and
   proof_origin differ in the existing node. New nodes contain provenance,
   source, search records, creation and Lean records. The repaired lifting
   node now records reuse of the existing private helper through its module's
   node, consistently with the Lean import and proof.

Changes in this reading: appended this fresh review after independently
rechecking the returned repair; no Lean, signature, definition or node changes
were needed. The previous round's review is retained as explicitly superseded
history. Source checked: https://stacks.math.columbia.edu/tag/088B.
