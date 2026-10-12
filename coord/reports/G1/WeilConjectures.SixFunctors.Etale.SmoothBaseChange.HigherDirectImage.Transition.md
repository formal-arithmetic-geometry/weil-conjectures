## What changed

Replaced the sorry in `AlgebraicGeometry.Etale.higherDirectImage_limit` by a complete Lean
assembly. Canonical coherence constructs the contravariant diagram and its comparison
cocone. Affine continuity and the proved affine-basis detection theorem make this a sheaf
colimit. Geometric sheafFiber preserves it. Mathlib's concrete filtered-colimit lemmas
then give element lifting and eventual vanishing, with the opposite arrows converted back
to `j ⟶ i`.

Moved the three existing transition definitions, with their parsed signatures and bodies
identical, into `Sheaf.AlgebraicGeometry.HigherDirectImageTransitions`. The original module
publicly imports them; their full names, visibility, and meaning are unchanged. This avoids
an import cycle between the original module and its new proof dependencies. The initial
expanded-formula presentation exceeded kernel checking's 60-second limit; the relocation
makes the complete source module compile in about 13 seconds. The change record is
`coord/changes/higher-image-transition-relocation.md`.

Added independent coherence and affine-continuity modules, and proved the general affine
etale colimit detection module using Mathlib's dense-subsite equivalence, objectwise
presheaf colimits, and two applications of `isColimitOfReflects`. This last theorem works
for arbitrary small index categories, without filteredness.

All five delivery modules compile locally with no warnings. The existing downstream module
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition` also
compiles against the sandbox, including its unfolding of the relocated definitions.
The prescribed `deliver3.py --no-push` dry run printed OK: compilation and preflight pass,
with the second reading left for the second reader. Nothing was pushed.

## Proved and sorry left

Proved, from the two named geometric statements:
`AlgebraicGeometry.Etale.higherDirectImage_limit`
(node `sbc-lem-higher-image-pulledback-stalk-continuity`). No sorry remains in the item's
module or in the relocated transition definitions.

Proved entirely using Mathlib:
`AlgebraicGeometry.Etale.nonempty_isColimit_of_affine_etale`
(node `sbc-lem-small-etale-affine-colimit-detection`).

Exactly two sorries are added, each the whole proof of a named public theorem:

- `AlgebraicGeometry.Etale.higher_image_over_transition_coherence`
  (`sbc-lem-higher-image-over-transition-coherence`), in
  `Sheaf.AlgebraicGeometry.HigherDirectImageOverCoherence`.
- `AlgebraicGeometry.Etale.nonempty_isColimit_higher_image_affine`
  (`sbc-lem-higher-image-affine-continuity`), in
  `Sheaf.AlgebraicGeometry.HigherDirectImageAffineContinuity`.

These are parts of the argument: the first has no limit assumptions or colimit conclusion;
the second is evaluation on a single affine etale object. The item's proof supplies actual
functor and cocone constructions, assembles the affine universal properties, preserves the
result through the geometric stalk, and proves both elementwise conclusions.

Edge cases checked mathematically: zero ring and zero sheaf; identity transitions; the
empty affine object; empty schemes; negative q (higher images of degree-zero sheaves vanish);
arbitrary cofiltered categories, not merely preorders. Cofilteredness supplies nonemptiness
and connectedness. The geometric assumptions are morphism qcqs, not absolute qcqs on W or S.
The affine base change supplies absolute qcqs where continuity needs it. No flatness over
integers is assumed for Λ: the coefficient comparison uses abelian-section acyclicity of
injective module sheaves (03FD), not preservation of injectives by forgetting scalars.

## No longer needed

No mathematical node of the prescribed presheaf/cohomology-continuity route is pruned.
Those steps remain in the proof of the new affine-continuity statement. Its sheafification
and finite-cover steps are explicit in the DAG and its docstring.

The original module's three public imports were moved to the relocated definitions module:
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`, and
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs`. They remain publicly visible through
the original module, so this is a relocation rather than pruning their exports.

Removed redundant candidate proof imports after compilation:
`Mathlib.Algebra.Category.ModuleCat.FilteredColimits`,
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`, and
`Mathlib.CategoryTheory.Sites.Point.Skyscraper`; the existing public imports already export
the APIs and instances used. The second reader made `Mathlib.AlgebraicGeometry.Sites.AffineEtale` a proof-only
import in the affine-basis module. Its public imports now supply only the module category
and small etale site used by its statement (ModuleCat.Basic and Sites.Etale).

The directed-preorder/AddCommGrp presentation in
`Sheaf.AlgebraicGeometry.HigherDirectImageLimitSystem` is not used as an intermediary for
this fixed pulled-back ModuleCat source theorem. This does not claim its general statement
is globally unnecessary, nor does it remove the shared blueprint node.

## Where the brief, the DAG or earlier work was wrong

No node's `lean.module` matched the assigned source module. Its docstring's blueprint node
`sbc-lem-higher-direct-image-limit` records instead the distinct general declaration
`AlgebraicGeometry.Etale.isIso_higherDirectImage_limit_system` in
`Sheaf.AlgebraicGeometry.HigherDirectImageLimitSystem`. That statement has abelian sheaves,
a directed preorder, compatible varying coefficients, and nonnegative degrees; it cannot
be directly applied to the assigned ModuleCat/cofiltered/stalk statement. Its general
record and proof are preserved. The new source-specialization node records the exact
existing source theorem and the reduction actually compiled, rather than overwriting the
general theorem's record.

The shared unit's route is preserved: higher images as restricted-cohomology
sheafifications, cohomology continuity after affine base change, and affine-basis assembly.
No statement, binder, universe, or conclusion of the assigned theorem changes.

LeanSearch was attempted for all new nodes and returned Internal Server Error. LeanFinder,
Loogle, and Mathlib/source/DAG text searches were performed; their results are recorded.
Mathlib supplied the affine-basis assembly and filtered-colimit element criteria, but no
higher-image continuity or transition-coherence theorem with these signatures was found.
The checked Stacks references are Tags 09Z1, 03Q8, and 0738; the local literature payload
is absent on this machine, so the official Stacks pages were read.

## New nodes

`def-sbc-module-higher-image-transitions` records the existing canonical definitions moved
verbatim into the acyclic definitions module. It introduces no new mathematical notion.

`sbc-lem-higher-image-over-transition-coherence` is identity and contravariant composition
for these canonical maps, from adjunction triangle identities and inverse-image coherence.

`sbc-lem-higher-image-affine-continuity` states the module colimit universal property on
one affine etale object, with the diagrams and maps explicitly tied to the source maps.
Its proof retains 03Q8 and complex continuity, then uses 0738 for affine sections.

`sbc-lem-small-etale-affine-colimit-detection` is proved in Lean from Mathlib; it reflects
objectwise affine-site colimits back to the original sheaf category.

`sbc-lem-higher-image-pulledback-stalk-continuity` records the exact assigned source theorem
that previously had no matching module record. Its proof is the compiled assembly.

The sole change record is `coord/changes/higher-image-transition-relocation.md`.

## Earlier second reading (a previous round; superseded)

1. Interface preservation: PASS. Read the repository/source diff for the assigned
   module. A byte comparison confirms that the entire `section Transition` block
   (all three signatures, bodies, and declaration docstrings) is identical in its
   new module. The existing `higherDirectImage_limit` signature is byte-identical.
   The relocation is declared in the change record; the original public exports
   remain available transitively. No target or definition meaning changes.
2. Proof and axioms: PASS as a reduction with two open geometric lemmas, not a
   completed axiom-free continuity theorem. Independently compiled all five
   delivery modules with lcompile.py --all: no errors or warnings. A scratch module
   printed axioms for all seven declarations. The three definitions and
   `nonempty_isColimit_of_affine_etale` use only propext, Classical.choice, Quot.sound.
   The assigned theorem and the two named open lemmas additionally use sorryAx.
   Exactly the two reported public theorem bodies contain sorry; none occurs in
   data. No forbidden trust extension is present in a delivered module.
3. Split statements: PASS. Read both signatures and their complete docstring
   arguments, and checked Stacks [09Z1](https://stacks.math.columbia.edu/tag/09Z1),
   [0738](https://stacks.math.columbia.edu/tag/0738), and
   [03FD](https://stacks.math.columbia.edu/tag/03FD).
   Coherence is a distinct adjunction/composition identity with no limit hypotheses;
   affine continuity is the local module universal property, before sheaf assembly
   and stalk passage. Identity systems, zero coefficients/sheaves, the empty affine
   object, negative degrees, and cofiltered categories with parallel arrows cause
   no failure. In particular qcqs over affine V supplies qcqs schemes even when
   W and S are not absolutely qcqs. Constant pulled-back diagrams have the intended
   colimit because the index is nonempty and connected. No scalar-flatness premise
   is used: 03FD supplies acyclicity, rather than injectivity after forgetting.
   Repeated searches with different wording using LeanFinder, Loogle, msearch grep,
   and rg on lean/. No exact existing theorem closes either split. Read the proved
   source CohomologyPresheaf comparisons, derived unit/composition coherence,
   the general abelian HigherDirectImageLimitSystem, and cohomology-limit APIs:
   these are ingredients, not direct specializations of either displayed signature.
   Closing either geometric bridge is not a few-minute repair.
4. Route and pruning: PASS after import correction. Read the proof downward:
   coherence constructs K and B, affine colimits assemble through the dense affine
   subsite, sheafFiber preserves the colimit, and Concrete filtered-colimit lemmas
   give representatives and eventual zero. The two opposite arrows in the zero
   argument need not agree; the second sends zero to zero, giving exactly the
   required arrow j to i. All three proof dependencies are actually used.
   The original general higher-image-limit node retains its presheaf and complex
   continuity route through the affine split; none of its old mathematical
   dependencies is pruned. Read dag/units/sk-lem-failure-field.json: its realized
   fields are currently empty and remain untouched; no realized unit step or
   chapter route is bypassed. Corrected the affine detection module's AffineEtale
   import to plain import; public ModuleCat.Basic and Sites.Etale provide its
   statement vocabulary. No proof-only public import remains in that module.
5. DAG agreement: PASS after dependency cleanup. Read all five new records and
   checked their recorded Lean statements against the files, created/item/group,
   source, proof sketches, proof_deps unions, proof_origin, blueprint ancestor,
   chapter and unit. The new stalk node describes the actual compiled reduction;
   the unrelated general abelian node is preserved. Removed inverse/direct-image
   definition nodes from the affine detection node's stmt_deps, since its statement
   uses neither operation. This changes no mathematical statement or proof route.

Second-reading changes: corrected the affine detection import visibility and its
public prerequisites, removed two unused statement dependencies from its new node,
and updated the import account in No longer needed. No proof body or signature
needed repair. Added the independent scratch axiom check and this review.

## Second reading by G1

1. Interface preservation: PASS. The assigned theorem and transition definitions match the
repository signatures byte-for-byte; the relocation is covered by the change record and
preserves the original public exports.
2. Proof and axioms: PASS. All five delivered modules compile with `lcompile.py --all`.
There are no forbidden declarations or hollow definitions; the only remaining `sorry`s are
the two named split theorems, with their `sorryAx` use recorded above.
3. Split statements: PASS. The coherence and affine evaluation theorems are strict,
source-backed intermediate results with matching DAG nodes; searches found no duplicates.
4. Route and pruning: PASS. The proof follows the unit route through coherence, affine
continuity, affine-basis detection, sheafFiber, and filtered-colimit criteria. Imports and
proof dependencies are pruned consistently, with no unit step bypassed.
5. DAG agreement: PASS. Declarations, dependencies, origins, and node records agree with the
compiled proof and assigned unit; no target statement changed.

Second reading changes: no further code or statement changes were needed; this section records
the independent review and successful local compilation.
