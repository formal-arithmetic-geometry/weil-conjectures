## What changed

`Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineClassVanishing` now proves its original
statement from the existing complex-cohomology continuity theorem and two new obligations.
Its signature, universe, hypotheses, conclusion, public imports, and existing docstrings
are unchanged. Its proof imports `HigherDirectImageRawComplexPresentation` and Mathlib's
abelian-group filtered colimits.

`HigherDirectImageRawDiagram` constructs the additive raw transition maps, the
contravariant functor on Over W, its inverse-system diagram, and the cocone obtained by
mapping the opposite scheme cone. The maps' data are exactly the existing explicit raw
pullback function; only their additive and functorial laws remain postponed.

`HigherDirectImageRawComplexPresentation` defines an existential proposition containing
all inputs and canonical-map equations of the existing complex-continuity theorem.
The presentation does not assert that the raw cohomology cocone is colimiting. Its proved
`isColimit` theorem eliminates its witnesses locally and applies that existing theorem.
No definition selects data from an unproved existence statement. The geometric and
module-to-abelian comparison that supplies this presentation is the second obligation.

The final proof obtains this presentation, applies complex continuity, forgets to types,
and applies `Types.FilteredColimit.isColimit_eq_iff'` to z and zero. It unops the resulting
single arrow and uses the additive map's zero law. This is a decomposition, not a
sorry-free proof of the mathematical continuity/comparison results.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.exists_higher_image_raw_affine_class_eq_zero`
(node `sbc-lem-higher-image-raw-affine-class-vanishing`). There are no sorries in the
item's module.

Added exactly two holes, both whole public theorem proofs:

- `AlgebraicGeometry.Etale.higherDirectImageRawOverPullback_functorial`
  (`lem-sbc-higher-image-raw-pullback-functorial`): additive, identity and composition
  laws, without any geometric limit hypotheses or vanishing conclusion.
- `AlgebraicGeometry.Etale.nonempty_higherDirectImageRaw_complex_presentation`
  (`lem-sbc-higher-image-raw-complex-presentation`): the raw-to-abelian-complex
  identification with all transition and coprojection equations. It does not invoke
  complex continuity and has no eventual-vanishing conclusion.

Thus this delivery is one hole closed and two holes added, a decomposition with net -1.
The constructions, the bundled-map application lemma, and the presentation-to-colimit
proof compile without internal holes. All three delivered modules compile cleanly using
lcompile.py. Existing dependencies may still use sorry, as intended in this stage.

Edge cases checked mathematically: arbitrary integer q, including negative degrees;
the zero coefficient sheaf and the zero ring; the empty affine etale object; a singleton
index category; and parallel arrows in a cofiltered category. The presentation works
with degree-zero complexes and lower bound zero for every q. Empty I is excluded by
IsCofiltered. The same-stage Mathlib criterion already handles parallel-arrow
equalization, and produces one arrow rather than two incomparable witnesses.

## No longer needed

Removed direct imports from the item:
`Sheaf.AlgebraicGeometry.EtaleComplexCohomologyLimit` and
`Sheaf.AlgebraicGeometry.InjectiveModuleAbelianAcyclic`.
The former is retained under the new presentation module and actually applied.
The latter is not imported: it is only a planned mathematical input to the unproved bridge.
They are not claimed to be pruned from the targets' entire import closure.

The proof no longer needs
`lem-weil-pbc-filtered-category-exists-directed-final` or passage to a directed preorder.
The existing complex continuity statement already accepts a small cofiltered category;
Mathlib's filtered type-colimit criterion handles equality in that category directly.
No separate negative-degree lemma is imported or introduced. No unit statement or
realized unit step is bypassed.

The original direct dependencies on inverse-image composition, constant connected
colimits, and injective-module abelian acyclicity are assigned to the new comparison
bridge. Their mathematical work remains needed; they are not globally pruned.

## Where the brief, the DAG or earlier work was wrong

The raw-interface module stated sheafification naturality but did not state identity,
composition, or additive laws for its explicit raw maps. Those laws are distinct from
sheafification naturality; they are now a named obligation and are used to construct
real maps and diagrams.

The original plan's complex-continuity application omitted its sizeable interface
bridge. The existing continuity declaration uses abelian complexes on varying sites,
with prescribed derived-adjunction maps, whereas the item uses module-valued derived
Hom groups. The new presentation records every required canonical-map equation, not
merely objectwise group isomorphisms. The existing `InjectiveModuleAbelianAcyclic`
declaration has coefficients `ULift R` for `R : Type u`, while this item allows arbitrary
`Λ : Type (u + 1)`. Its recorded mathematical node states the general all-object
acyclicity result, but the present Lean signature is not a direct specialization for
arbitrary Λ. The future comparison worker must address that universe/interface gap;
this delivery changes neither the coefficient hypothesis nor that dependency.

The final categorical step did not require a directed presentation. Its removal follows
from the already-general signatures of complex continuity and Mathlib's equality
criterion. The parent node's unit record has empty realized lists; no unit file is edited.
The parent already records `sbc-lem-higher-direct-image-limit` as its blueprint ancestor;
new nodes retain that ancestry, even though blueprint_refs.py ancestor printed None for
this recently created module-based item.

The public data definitions have no sorry. Compiler timeouts in early drafts came from
eta-expansion of bundled groups and a hand-written cocone naturality proof. Using
ConcreteCategory.ofHom and mapping the opposite cone resolved those within the new
module, without adapting any existing module or changing a public interface.

Mathlib search used the prescribed msearch.py for semantic, type/name, and source
searches. LeanSearch was unavailable (HTTP internal server error), recorded as such.
LeanFinder and source searches found no raw comparison or raw functoriality theorem.
The Stacks pages 09Z1, 0EZM and 03FD were read directly; their roles are respectively
the affine-object reduction, complex continuity, and module/abelian comparison.

A read-only DAG traversal found an existing baseline cycle between
`lem-weil-pbc-sheaf-algebraic-structures-abelian-component` and
`lem-weil-pbc-sheaf-algebraic-structures-objects`. The original item already reaches it
through complex continuity and cohomology pullback. None of the five delivered node
records belongs to this cycle, and no existing edge in the cycle is edited. This is
reported upward here rather than changing unrelated nodes. Delivered references all
exist, and each proof_deps list equals its proof-step uses.

The prescribed delivery dry run printed OK, with only the reserved second-reading
section pending; nothing was pushed.

## New nodes

`lem-sbc-higher-image-raw-pullback-functorial` records the additive and functorial laws
for the existing explicit raw pullback, with a complete natural-language coherence
proof and the named remaining theorem in `HigherDirectImageRawDiagram`.

`def-sbc-higher-image-raw-diagram` records the explicitly constructed raw functor,
diagram, and cocone. Its data come from existing raw groups and maps; only proof fields
use the named functoriality theorem.

`def-sbc-etale-complex-cohomology-presentation` records the existential proposition
of continuity input data. It includes the canonical P equation and all coefficient,
cohomology-transition, and cocone compatibility equations. It selects no objects.

`lem-sbc-higher-image-raw-complex-presentation` records the remaining geometric and
coefficient comparison, including base change to affine U, lower bound zero, the
constant coefficient cocone on the limit, and the natural derived-Hom identification.
The existing complex-continuity theorem is applied after this lemma, not assumed in it.

No change record is needed: there is no alteration of any existing signature, definition,
visibility, or public import, and no forced adaptation.

## Second reading by F1

1. Interface: PASS. Read the diff against the repository and compared declaration
signatures with the stage-3 declaration parser: `statement_changed` is empty. The
original theorem's full signature and docstring are byte-for-byte unchanged, including
arbitrary Λ : Type (u + 1), integer q, cofiltered category, both stage qcqs hypotheses,
the underlying-scheme limit, limit qcqs hypotheses, affine U, and the raw-zero premise.
The only existing module delivered is this item; no forced adaptation or change record.

2. Proof and trust: PASS, conditional on the two explicitly named open obligations and
existing open imports. Compiled all three modules with lcompile.py. Inspected every
construction: maps are the fixed raw formula, functor objects are fixed groups, and
cocone data are obtained by mapping c.op. Only law proofs use the functoriality theorem.
The presentation is a Prop with existential witnesses; these are eliminated inside the
isColimit proof, never selected to define public data. The only textual sorries are the
two named public theorem proofs. No axiom, unsafe, opaque, extern, implemented_by, or
kernel-check bypass is present. A scratch axiom check and delivery's all-constant probe
check the standard axioms plus sorryAx, as expected for this decomposition.

3. Split statements: PASS. Read both full docstrings and nodes against Stacks Tags
09Z1, 0EZM, and 03FD. Raw functoriality makes no geometric assumptions and follows from
the additive derived functor and coherent single/shift comparisons. The presentation
lemma supplies base-changed qcqs stages, degree-zero coefficient complexes, and all
canonical-map equations; it assumes no cohomology colimit and no eventual vanishing.
It is a proper comparison step, separate from the already-stated complex continuity.
Checked zero coefficients/ring, empty affine U, singleton I, negative q, and parallel
arrows: zero complexes handle the zero/empty cases, negative single-complex cohomology
vanishes, and the filtered equality criterion returns one arrow after equalization.
Repeated searches with different wording using msearch LeanFinder, Loogle, and grep,
and rg over both source roots. No theorem supplies either complete new obligation.
Existing `nonempty_freeSheafDerivedSectionsIso` and
`nonempty_etaleModuleCohomology_forgetIso` provide useful nonnegative-degree component
comparisons for the remaining worker; they do not give the base-change and scheme-map
coherence equations required here. The existing RawCohomologyComplexPresentation is
for directed preorders, abelian coefficients and natural degrees and does not encode
compatibility with this fixed module-valued raw diagram's transitions. Thus it is not
a replacement for this presentation. No new holes were closed in this second reading.

4. Route and pruning: PASS after import/report repairs. The top theorem first applies
the comparison, then the existing complex continuity theorem, then Mathlib's filtered
colimit equality criterion. The direction of f.unop is j -> i and map_zero converts
the equality to the exact required conclusion. The presentation copies every canonical
hypothesis of the continuity theorem, including hP, hH, and hB. Read the unit record:
its realized statement and step lists are empty; the affine raw-cohomology reduction
retains the higher-direct-image continuity route and bypasses no realized unit step.
Removed unused public imports AffineTransitionLimit and HomologicalComplexLimits from
the new presentation module (the needed declarations are already available through its
other public imports), and its unused proof import InjectiveModuleAbelianAcyclic.
The remaining public imports support exposed statement/definition expressions.

For completeness, every old proof dependency absent from the new parent proof_deps is:
`lem-weil-pbc-filtered-category-exists-directed-final` (unneeded directed replacement),
`def-weil-pbc-derived-categories` and `def-weil-pbc-etale-site` (signature vocabulary,
not independent proof steps), `lem-weil-pbc-inverse-image-composition`,
`lem-weil-pbc-colimit-constant-connected-diagram`, and
`lem-weil-pbc-injective-module-abelian-acyclic` (remaining comparison's planned inputs).
The old direct proof imports DerivedCategories and UpperLowerStar.Defs are also removed
from the item: raw-interface and presentation imports already expose what is needed.
No module is claimed globally pruned; directed-final is the retired dependency route.

5. Records: PASS. Read all five JSON records. Only proof, proof_deps and proof_origin
change in the existing node. Every new node has its source, searches, blueprint ancestry,
chapter/unit, creation fields and Lean attachment; both remaining theorem signatures
match their attachments. Each proof_deps is exactly the union of its steps' uses and
all referenced ids exist. Definition nodes have empty proof plans, as required.
The parent explicitly records the comparison, continuity application, and categorical
zero step, matching the compiled proof. Net holes remain one closed, two added (-1),
a decomposition rather than a sorry-free proof. The pre-existing DAG cycle described
above is unrelated and is not changed.

Second-reading changes: pruned the three unused presentation imports, completed the
removed-import/dependency inventory, corrected the report's claim that the unused
acyclicity import was retained, and recorded existing component comparisons for the
next worker. The proof bodies and signatures were preserved.

Validation note: the second-reader dry run printed OK (CODEX). Its appended all-constant
probe timed out at 60 seconds for HigherDirectImageRawComplexPresentation; ordinary
compilation passed in 50.8 seconds. The independent scratch #print axioms check passed
for all ten named delivered declarations (including the presentation definition,
isColimit theorem, and bridge theorem), with only propext, Classical.choice, Quot.sound
and the expected sorryAx. The presentation definition itself has no sorryAx.
The delivery tool permits this probe timeout and the merge repeats its probe.
