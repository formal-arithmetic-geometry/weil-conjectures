## What changed

Repaired return X-c85ad, head c85ad868c, in the sandbox.

D1/D2 and C6: deleted AffineTorsorSingleStabilizerComponentExistence.lean,
its duplicate existence node and affine-torsor-single-stabilizer-component-import.md.
Removed its import and the unused-variable linter suppression. First restored the
open theorem to its original hole, then replaced that hole by the genuine reduction below.

E2: replaced the false universal section statement with existence of a descended
map s:U->Y and its base and section-factorization equations. It makes no openness
assertion. A dispute notice immediately precedes the corrected declaration and
records why the former statement is false. The change record is
coord/changes/affine-torsor-single-stabilizer-component-section.md.

Added the proof-only import AffineTorsorStabilizerSectionOpen. Its one theorem
asserts openness for a given map f from the exact stabilizer quotient, conditional
on the base equation and the selected-section equation; it asserts no existence.
This differs from the deleted existence duplicate: it proves a geometric property
of an already given compatible map, while the repaired section lemma supplies
only a descended map into Y.

In both the open and parent proofs, construct f by pullback.lift s b hsbase.
pullback.lift_snd proves its base equation; pullback.lift_fst and hssection prove
its selected-section equation. Apply the separate openness criterion and package
the equations. The parent signature is identical. The open conclusion is identical;
its unused let-bound q is alpha-renamed _q to compile without a linter suppression.
Updated all three existing nodes and the new node to record this actual route.
No other module, definition or Challenge target changes.

## Proved and sorry left

Closed the existing hole affine_torsor_single_stabilizer_component_open by a
complete Lean proof from two strictly separate geometric steps. This is a
decomposition, not a sorry-free geometric proof. The previously proved
 affine_torsor_single_stabilizer_component now has a sound reduction to the same
steps, with its exact signature preserved.

The remaining holes, each a public named theorem proved exactly by sorry, are:

- affine_torsor_single_stabilizer_component_section, node
  lem-sbc-affine-torsor-single-stabilizer-component-section: corrected descent
  existence, not a proof of the former false universal identity.
- affine_torsor_stabilizer_section_open, new node
  lem-sbc-affine-torsor-stabilizer-section-open: conditional openness only.

Relative to the repository baseline: one original hole closed, one existing
holed statement corrected, one lower hole added. Net hole reduction is zero;
this delivery is a repair and decomposition. Relative to the returned sandbox,
the duplicate existence hole was deleted and the false section hole replaced.
No hole occurs in a definition and no arbitrary object is chosen in a definition.

## No longer needed

Removed import and module
Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorSingleStabilizerComponentExistence
and node lem-sbc-affine-torsor-single-stabilizer-component-existence.
Its proposed circular proof route is entirely deleted. The parent proof no longer
uses the open theorem as an intermediate: it constructs the compatible pullback
map itself. The exported open theorem remains useful and is proved separately.
The SplitAction import is retained for statements and definitions. The second
reader removed the redundant public imports Mathlib.AlgebraicGeometry.Limits and
Mathlib.AlgebraicGeometry.Restrict from both delivered modules; the remaining
public imports already provide their declarations. These removals do not prune
any module from the target import closure. The old proof dependency
lem-sbc-affine-torsor-split-label-laws is no longer directly used by the open and
parent proofs, but remains required by their statements and by the two lower
steps, so its module is retained. The unit record has no realized node here, and no
unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the former affine_torsor_single_stabilizer_component_section
quantified over arbitrary F and f, with no openness or projection hypotheses.
Counterexample: R=H=C=Q, g=1, ι=id, G trivial, T=Spec Q, Y the disjoint
union of two copies of T, d=2, delta the canonical splitting, x=0, K=G,
F=Q, and f the inclusion of component 1. The hypotheses hold, but the conclusion
equates the two distinct component inclusions. Even an open-immersion hypothesis
and the base equation would not select x. The repaired existential statement
chooses a map by descending x itself.

The deleted existence module merely renamed the open theorem modulo its unused
let q, so it was not a reduction. Its new node used the parent theorem as
justification, making the previous proof circular. Both are removed.

The old DAG open node was not updated to record the added existence dependency.
This repair explicitly updates the open, section and parent proof records. The
new openness node depends only on the split-label laws, never on the parent,
open theorem or repaired section theorem; the corrected section node depends
only on the split-label laws. Hence the repaired graph has no such cycle.

Edge cases checked mathematically: for the trivial group the descent assertion
selects the x-th section, and the conditional openness criterion applies to that
summand. For d=0 there is no x. For K=G the criterion applies to a fixed section;
for K=1 it identifies a transitive component. The domain/nonzero hypotheses
ensure the puncture is nonempty and localization is injective. The two-point
counterexample fails the new criterion's selected-section hypothesis for f from
component 1 when x=0.

The downstream declaration-use filter and whole-library search find only this
module using the changed section declaration. No forced adaptation is needed.
Mathlib searches found only general etale and open-immersion ingredients, and
LeanSearch returned an Internal Server Error. The two remaining geometric
obligations are not claimed proved.

## Earlier second reading (a previous round; superseded)

Historical second-reading corrections requested by X-c85ad; these correct the
returned report, and are not a new independent reading of this repair.

The section statement is unchanged but has no open-immersion or projection
hypotheses and quantifies over arbitrary F and f; it is false by the two-point
split-cover counterexample. This sentence describes the returned delivery;
in this repair that statement has been replaced through the change-record process.

The previous claim that the existence statement was strictly smaller than the
open theorem was wrong: they are duplicates modulo an unused let q.
The existing open node was not updated to record the added existence dependency,
so the previous claim that DAG records agreed with the Lean proof was wrong.
The reported compile relied on suppressing unused-variable warnings; the
suppression has now been removed. A fresh independent second reading remains
for the dispatcher-appointed reader after this repair's dry run.

## New nodes

lem-sbc-affine-torsor-stabilizer-section-open, in
AffineTorsorStabilizerSectionOpen.lean, is the conditional geometric openness
step. Given f with the two compatibility equations, exactness of its stabilizer
makes the map G/K to the split labels injective, hence identifies an open-and-closed
finite etale subcover. It contains no existence assertion and is independent of
the repaired section-descent theorem. Its source is Stacks Project Tag 03SF.

The section node is existing, not new; it carries the statement_change record.
Change record: coord/changes/affine-torsor-single-stabilizer-component-section.md.

## Second reading by C3

1. Compared both delivered modules with the repository. The new criterion module
   is absent there. The parent signature is byte-for-byte identical; the open
   signature differs only by the declared unused-let alpha-renaming q to _q.
   The section signature change is explicit in the report and change record;
   its Old and New blocks are verbatim signatures. No definitions or Challenge
   statements changed. A whole-library declaration search confirms that only
   this module uses the changed section lemma. Verdict: pass.
2. Compiled both modules locally in import order, with no errors or warnings.
   Appended #print axioms for all four declarations to a scratch copy: each
   uses only propext, Classical.choice, Quot.sound and sorryAx. There are exactly
   two named sorry theorems, both reported; no definition, private helper, axiom,
   unsafe declaration, opaque declaration, extern, implemented_by or kernel-check
   override is present. The pullback map is constructed in the proof from the
   descended section; no data definition chooses an arbitrary unproved witness.
   Verdict: pass, conditional on the two stated geometric obligations.
3. Read both remaining obligations, their docstring arguments and nodes.
   Verified Stacks Project Tag 03SF and its finite-etale permutation-set route.
   On V=D(h), finite faithful flatness gives a surjective finite etale cover of
   B=D(ι g); the domain gives connectedness, and unique rotations on geometric
   fibres give the G-torsor identification. K-invariance descends the section;
   exactness of K makes the associated coset-to-label map injective, hence open
   and closed. The fixed denominator and injective localization identify the
   invariant ring with the localization of F. Checked G trivial, K=G, K=1,
   d=0 and the two-point counterexample. Neither obligation restates the parent: one
   gives only descent existence, the other only conditional openness of a given
   compatible map. Repeated LeanFinder, Loogle and Mathlib grep with different
   queries, and searched lean/Sheaf and the upstream torsor modules. Results were
   field-theoretic or abstract Galois-category facts and general morphism facts,
   not these scheme/invariant-ring statements. Upstream torsor descent does not
   identify this concrete stabilizer quotient; downstream orbit-component descent
   uses this parent and cannot replace it without a cycle. No obligation closes
   in a few minutes with the available declarations. Verdict: pass.
4. Read the reduction from the top: pullback.lift combines section descent with
   the supplied base map; lift_fst and lift_snd establish the exact equations;
   the criterion proves openness. No circular dependency or deleted existence
   duplicate remains. The new criterion import is proof-only. The other retained
   imports supply statement notation, types, instances and definitions. Removed
   redundant Limits and Restrict imports from both files and compiled the reduced
   set. Listed all discarded old proof dependencies above, distinguishing those
   retained for statements. sk-prop-input-spreading.realized has no node here,
   so no unit statement or step is bypassed. Verdict: pass.
5. Checked every Lean signature against its node verbatim, every proof_deps
   against the union of proof-step uses, and the actual reduction against proof
   and proof_origin. Existing node edits stay within stage-3 owned fields and
   the recorded section correction. The new node has the required creation,
   source, search, blueprint, chapter, unit and Lean records. The section
   correction has no citers on the repository DAG baseline (its old proof
   metadata omitted the actual parent use); both actual Lean users in this
   module are repaired together. Verdict: pass.

Second-reading changes: removed two redundant public Mathlib imports from each
module and clarified the pruning report. The mathematical proofs and statements
are retained. This remains a repair/decomposition: one of the two original holes
is closed, the false holed section statement is corrected, and one new lower
hole is added; the two geometric holes remain and the net hole reduction is zero.
