## What changed

Proved `Algebra.exists_popescu_translated_presentation` with its existing signature and public
imports unchanged. Its two new proof-only imports are
`Sheaf.RingTheory.PopescuTranslatedPresentationData` and
`Sheaf.RingTheory.PopescuTranslatedPresentationProperties`.

The first intermediate theorem explicitly constructs a translated presentation retaining its
strict-standard minor witness and ideal-square containment, and whose generators vanish under
the given quotient section. The second intermediate theorem, also fully proved, evaluates that
witness under the section, extracts relation constant coefficients, lifts the finite coefficient
family, and rearranges the resulting congruence to the required constant-minor identity.
The target extracts generator divisibility from compatibility with alpha and assembles the results.
The section and the translated presentation are shared throughout this argument.

## Proved and sorry left

Baseline hole closed (one): `Algebra.exists_popescu_translated_presentation`.
Holes added: none. Sorry left: none in any delivered module.

The two proposed lower holes were repaired and closed as well:
`Algebra.exists_popescu_translated_presentation_data` and
`Algebra.exists_popescu_translated_presentation_properties`. Both are new, fully proved auxiliary
results; neither is counted as a baseline hole closed. The original proposed delivery was a
one-hole-to-two-holes decomposition; the final delivery is a proof, closing one baseline hole
and adding zero holes.

All three files compile without errors or warnings through the required local compiler.
Independent `#print axioms` checks on all three declarations show only `propext`,
`Classical.choice`, and `Quot.sound`. No definition selects data from an unproved theorem:
the substitutions are explicit, the presentation is a local structure with all fields proved,
and scalar choices use the proved surjectivity of quotient maps.

## No longer needed

No existing module import was removed and no module is claimed pruned. The original public
`StrictlyStandardElement` import is necessary for the target signature and for the translation
lemma. The constant-evaluation lemma imports only its four Mathlib statement dependencies and
uses a plain, proof-only `Mathlib.Tactic.Ring` import.

Every old direct `proof_deps` entry of the target is now supplied transitively by the new lemmas:
`def-weil-pbc-finitely-presented-algebra`, `def-weil-pbc-mv-polynomial-ring`,
`def-weil-pbc-polynomial-partial-derivative`, and `def-weil-pbc-strictly-standard-element`.
They are removed from the target's direct proof dependency list, but remain needed and are
not pruned. The target's new direct dependencies are exactly the two new proved lemmas.

## Where the brief, the DAG or earlier work was wrong

The first worker's properties theorem was false: it asserted the strict-standard conditions
for an arbitrary presentation satisfying just generator/constant divisibility. Strict standardness
supplies these conditions for an existentially chosen presentation, not every such presentation.
For example take R=A=Lambda=Q, pi=1, alpha=id, and the presentation Q[X]/(X), with n=m=1 and
c=0. The quotient section is the map between zero rings, and both divisibility clauses hold
with lambda=a=0. The image of pi is strictly standard (use the empty presentation of Q over Q).
But the asserted ideal-square condition would say X belongs to (X)^2 in Q[X], which is false.
The proposed data lemma did not retain the strict-standard witness, so it could not justify
that application.

The repaired data lemma retains the witnessed minor identity and ideal-square condition of
the actual translated presentation. The properties lemma now requires this particular minor
identity and the section killing its generators; it makes no unsupported assertion about an
arbitrary presentation and does not assert ideal-square containment at all.

Source read: https://stacks.math.columbia.edu/tag/07CR, the opening presentation/translation
paragraph and the constant-minor equations before Tag 07DQ. This is exactly the original route.
The local source path recorded in the DAG was not present on this machine, so the primary-source
page was read directly. No Noetherian or annihilator hypothesis is used in this initial part
of the source proof, and none was added to the target.

## New nodes

`lem-weil-pbc-popescu-translated-presentation-data` records the translation construction and
retention of the strict-standard witness, in `PopescuTranslatedPresentationData.lean`.
It is fully proved, has a source and a complete natural-language proof, and records the inverse
substitutions, new kernel calculation, derivative calculation, and ideal transport separately.

`lem-weil-pbc-popescu-translated-presentation-properties` records the quotient-section evaluation
and scalar extraction, in `PopescuTranslatedPresentationProperties.lean`. It is fully proved,
independent of Lambda and alpha, and needs only the displayed minor identity and vanishing
of generator images. It has no dependency on the data lemma: its hypotheses are explicit.

Both nodes retain the item's chapter and unit and have verbatim Lean signatures. No existing
statement or definition was changed, so no interface change record or forced adaptation is needed.

## Second reading by J2

1. Compared the complete target module with the repository using diff, and separately compared
   the theorem signature byte for byte. The existing theorem statement, visibility, universe
   parameters, hypotheses, conclusion and original public import are unchanged. The only target
   changes are two plain imports and its proof. The other modules and nodes are new.
2. Read every proof and compiled all three modules locally in import order. No sorry, axiom,
   unsafe, opaque, implemented_by, extern, or skipped kernel check is present. Checked the axioms
   of all three declarations independently: only the three allowed axioms occur. The translated
   presentation has explicit values, relations, and polynomial lift; all its structure laws
   are proved. Verdict: fully proved with no hollow data or remaining holes.
3. Found and rejected the false arbitrary-presentation properties statement using the Q[X]/(X)
   example above. Replaced both proposed statements by actual steps of the argument and proved
   both. Tested their reasoning at pi=0, pi a unit, empty generators/relations, c=0 (the empty
   determinant is 1), and zero rings: the construction uses quotient surjectivity and ideal
   membership only, never division or cancellation. Repeated searches with LeanFinder for
   additive polynomial translation, Loogle for `MvPolynomial.aeval_zero`, and grep through
   Mathlib and both local library roots. Candidates concern reindexing, base algebra equivalences,
   disjoint-variable elimination or rescaling, not this translation; the generic upstream chain
   rule gives no shorter proof than the local polynomial induction. The exact Mathlib constant
   evaluation lemma is used. Verdict: no duplicate and no split-off holes remain.
4. Read the original plan and the `sk-thm-p1` unit's realized statement/steps. Neither this item
   nor either auxiliary node is a realized unit step; the proof implements the same translation
   and constant-minor calculations below that level, and changes no unit route. Both proof-only
   imports are used; all public imports support signatures. Listed all four old direct proof
   dependencies above and explained their continuing transitive necessity. Verdict: route kept,
   no module pruned.
5. Rewrote the new nodes to state the repaired theorems, recorded their signatures verbatim,
   and expanded their proof steps to follow the actual Lean constructions and quotient argument.
   The properties node no longer spuriously depends on the data node. Updated the target proof
   steps and direct dependency union to the two new lemmas. Sources, origin, searches, creation,
   blueprint ancestry, chapter, unit and Lean records are present. Existing non-owned node fields
   and existing interfaces are unchanged. Verdict: node records agree with the proved code.

Second reading changed: repaired the false decomposition; explicitly constructed the translated
presentation; proved both lower theorems; minimized the properties module's imports; corrected
all three proof records and both new statement records; replaced the inaccurate progress report.

Validation: the required delivery dry run passed with review class CODEX (new proved modules
and nodes). All three independent axiom checks passed; no compilation warnings remain.
