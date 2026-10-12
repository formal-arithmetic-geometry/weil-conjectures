## What changed

Replaced the sorry in
`AlgebraicGeometry.Etale.survivesBaseChange_comp_iff_of_surjective` with a complete
Lean reduction of the thickening step of `sbc-lem-bc-failure-field`.
The proof constructs the induced cartesian square between the two chosen pullbacks.
It combines transition compatibility and coefficient naturality to obtain a commuting
square, identifies the composite transport by the target-transition composition law,
and proves both implications using surjectivity of the source stalk comparison and
injectivity of the target stalk comparison.

Added three proof-only imports and three new statement modules:
`Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp`,
`Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening`, and
`Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening`.
They isolate composition of transitions and the two geometric isomorphism assertions;
none mentions a chosen element or the survival predicate. They are strictly parts of
the original argument, not restatements of survival invariance.

A proved private helper, `baseChangeHomologyMap_range_congr`, handles the change of
parenthesization of the bottom morphism without unfolding derived functor definitions.
Existing public statements, definitions, and docstrings are unchanged.
Updated only the proof and its dependency/origin fields of `sbc-lem-bc-failure-field`.
The unit's thickening, limit, closed-open, and empty-scheme route is preserved.

## Proved and sorry left

Closed one of the three original direct sorries:
`AlgebraicGeometry.Etale.survivesBaseChange_comp_iff_of_surjective`.
This is a reduction, not an axiom-free closure: its proof uses the three named
intermediate statements below. The already-proved identity and empty-scheme lemmas
and the assembly of the qcqs local property retain their original proofs.

The two untouched direct sorries in the item are:
- `AlgebraicGeometry.Etale.survivesBaseChange_of_isLimit`, condition (2) of
  `sbc-lem-bc-failure-field`.
- `AlgebraicGeometry.Etale.survivesBaseChange_or_of_isClosedImmersion`, condition (3)
  of `sbc-lem-bc-failure-field`.

The delivery adds precisely these direct sorries, each as the entire proof of a
public theorem in its own module, with a source and proof in words:
- `AlgebraicGeometry.Etale.baseChangeTargetTransition_comp`
  (`lem-sbc-target-transition-comp`).
- `AlgebraicGeometry.Etale.baseChangeSourceTransition_isIso_of_thickening`
  (`lem-sbc-source-transition-thickening`).
- `AlgebraicGeometry.Etale.baseChangeTargetTransition_isIso_of_thickening`
  (`lem-sbc-target-transition-thickening`).

The new statements have no qcqs, positive-degree, or torsion assumptions: composition
is formal for all integer degrees, and the thickening comparisons are induced by an
étale-site equivalence. For an identity thickening their conclusions agree with the
existing identity-transition argument. For empty schemes their transitions compare
zero objects. The target statement explicitly requires the cartesian square needed
for the covering morphism to be a thickening.

Local compilation of all four modules and the completed reduction succeeds without
warnings. The final dry run performs the axiom probes and server validation.

## No longer needed

None. No original import is removed. The two original public imports supply the
module's statements and the already-proved identity and empty-scheme arguments.
The three added imports are all used in the thickening proof. The thickening-site,
higher-direct-image-limit, injectivity, and minimal-counterexample nodes remain
needed by the unit; the delivery prunes none of them. No new proof dependencies for
the untouched limit or closed-open arguments were imported.

## Where the brief, the DAG or earlier work was wrong

The requested module is not attached to any node's `lean.module` record in this
checkout. Its declaration docstrings identify the three gaps as conditions (1)-(3)
of `sbc-lem-bc-failure-field`; that node has no `lean` record. The unit record's
`realized` lists are empty. This delivery follows those explicit docstring references
and updates the parent proof without claiming that this partial module realizes the
whole field-detection statement.

The thickening paragraph correctly identifies the mathematical input, but the
library does not yet state the required isomorphism consequences for the derived
source and target transitions, nor their target-composition identity. The three new
nodes make those missing formal steps explicit. The existing transition compatibility
and coefficient naturality are already proved and are used directly.

LeanSearch returned an Internal Server Error. Its searches are recorded as unavailable,
not as negative results. LeanFinder, Loogle, the Mathlib grep, local source searches,
and blueprint searches found no existing statement that closes these transition gaps.
No statement is disputed and no public interface or target statement was changed.

## New nodes

`lem-sbc-target-transition-comp` in
`dag/nodes/sec-smooth-base-change/lem-sbc-target-transition-comp.json`, realized by
`lean/Sheaf/AlgebraicGeometry/BaseChangeTargetTransitionComp.lean`, states composition
of target transitions with the coefficient pullback comparison. Its proof follows
the pasting law for the two degenerate squares and the pullback associativity law.

`lem-sbc-source-transition-thickening` in
`dag/nodes/sec-smooth-base-change/lem-sbc-source-transition-thickening.json`, realized by
`lean/Sheaf/AlgebraicGeometry/BaseChangeSourceTransitionThickening.lean`, states that
the canonical source transition along a thickening is invertible. The remaining task
is the derived unit and direct-image composition comparison for the site equivalence.

`lem-sbc-target-transition-thickening` in
`dag/nodes/sec-smooth-base-change/lem-sbc-target-transition-thickening.json`, realized by
`lean/Sheaf/AlgebraicGeometry/BaseChangeTargetTransitionThickening.lean`, states that
the target transition above a thickening is invertible when the covering square is
cartesian. The covering morphism is itself a thickening, and the remaining task is
the same derived unit comparison together with the coefficient identifications.

No change record is required: the existing module's new helpers and imports are private
to proofs, and no existing statement or definition changes.

## Second reading by X2

1. Compared the Survival module with the repository by `diff` and the project's
   declaration parser: no existing signature, definition, or docstring changed.
   The additions are three plain proof imports, the private equality-transport
   helper, and the proof of `survivesBaseChange_comp_iff_of_surjective`. The helper
   substitutes equality of the bottom morphisms and uses proof irrelevance; it
   introduces no geometric assumption. No statement change record is needed.
2. Compiled all four modules with `lcompile.py --all`, without errors or warnings.
   A scratch copy with `#print axioms` for all six public Survival theorems and the
   three new theorems showed only `propext`, `Classical.choice`, `Quot.sound`, and
   `sorryAx` for the open statements and their users. Identity survival and empty
   failure have no `sorryAx`. The item has precisely the two reported untouched
   direct sorries; the new modules have exactly their named whole-theorem sorries.
   Read the commuting-square proof: `hb` comes from transition compatibility and
   coefficient naturality, `ht` identifies composite transport using pullback-lift
   uniqueness, and the reverse implication uses source surjectivity and target
   injectivity. There is no forbidden declaration or hollow definition.
3. Read Stacks Tags 03SI and 0F07, condition (1), and matched each new statement:
   source invertibility needs a surjective closed immersion, target invertibility
   also needs its covering square cartesian, and composition needs just the two
   commutative triangles. No qcqs, torsion, or degree restriction is used by these
   categorical arguments. Identity thickenings reduce to the existing identity
   calculation; an empty thickening has both schemes empty; q = 0 and negative q
   still follow because homology preserves isomorphisms. The composition formula
   also allows noncartesian covering squares, and its coefficient comparison has
   the direction from iterated pullback to composite pullback. None restates the
   survival predicate. Independently searched LeanFinder for derived restriction
   under equivalences, Loogle for an adjunction-unit isomorphism, and Mathlib grep
   for `unit_isIso_of_L_fully_faithful`; also searched local Lean for thickening and
   transition/composition results. The generic unit instance is an ingredient,
   not any of the three statements. Closing these gaps requires the remaining
   comparison calculations, rather than a one-line application of that instance.
4. Read the unit `sk-lem-failure-field` and the parent node's old dependencies:
   the thickening, limit, closed-open, and empty route is preserved. The unit's
   `realized` lists are empty in this checkout; this delivery does not alter them
   or claim a realization of the entire field-detection lemma. Both original
   public imports are used by existing statements or arguments; all three new
   imports are proof-only and used. Every original parent dependency is retained,
   so `No longer needed: None` is complete.
5. Checked every delivered node, its Lean declaration, source, blueprint ancestry,
   searches, and union of proof-step dependencies. The parent changes only proof,
   proof_deps, and proof_origin. Found a faulty citation in the composition node:
   `sbc-lem-base-change-composition` only asserts preservation of invertibility for
   cartesian squares; it does not give the equality needed for arbitrary triangles.
   Replaced it by the generic mate-pasting law and inverse-image coherence.
   Clarified the source/target node proofs using the existing composite-adjunction
   and adjunction-conjugate definitions, including the triangle cancellation that
   identifies the chosen transition with the direct image of the invertible unit.

Second-reading changes: corrected that DAG citation and dependency list; expanded
all three new docstring proofs to state the absence of a cartesian requirement in
mate pasting and explain localization of an exact equivalence and the defining
unit-counit comparison. No Lean proof, statement, definition, or import was changed.
The kernel-checked reduction is retained; one of three original gaps is reduced,
with three strict intermediate statements split off, and no pruning.
