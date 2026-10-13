## What changed

Proved `AlgebraicGeometry.exists_derivedBaseChange_top_iso` with its original signature,
visibility, public import and definitions unchanged. The two natural isomorphisms are
constructed explicitly from the existing selected pullback comparisons and pinned
adjunctions. Pullback along the scheme isomorphism is shown fully faithful using
its two inverse-composition isomorphisms; Mathlib then makes its adjunction unit
invertible. The proof applies the pasting law and cancels this unit.

Added `Sheaf.AlgebraicGeometry.DerivedBaseChangePasting`, containing the proved theorem
`AlgebraicGeometry.schemeDerivedBaseChange_pasting` and a proved private helper for
conjugate adjunction Hom equivalences. The pasting theorem is valid for any morphism
at the upper-left vertex. It follows directly from the pinned counit description,
Hom-equivalence naturality, the selected pullback associativity laws and equality
transport. Its proof introduces no new geometric hypotheses or unresolved statements.
The item imports this module and `Mathlib.CategoryTheory.Adjunction.FullyFaithful`
only for its proof. The new module publicly imports Mates because its statement
specifies the conjugate isomorphism.

Updated the existing node's proof, proof dependencies and proof origin; added the
pasting node. No definition or existing statement changed, so no forced adaptations
or change records are needed. The unit record has empty realized statement/steps;
the prescribed unit route is preserved, and both original proof dependencies remain.

Validation: both sandbox modules compile in import order without errors or warnings,
within the 60-second per-file limit. The delivery dry run also passes the
preflight and the axiom probes; nothing was pushed. The complete proof includes identity morphisms,
empty schemes and zero objects without exclusions. The formulas are categorical
identities; neither theorem assumes a cartesian square.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.exists_derivedBaseChange_top_iso`
(node `lem-pc-derived-base-change-top-iso`).

Also proved the new helper theorem
`AlgebraicGeometry.schemeDerivedBaseChange_pasting`
(node `lem-pc-derived-base-change-pasting`). Its private conjugation helper is proved.

No `sorry` remains in either delivered module. Holes closed: 1; holes added: 0;
holes split off: 0. The final explicit axiom checks of both public theorems report only propext,
Classical.choice and Quot.sound, with no sorryAx.

## No longer needed

None. No original import, node or module was pruned. Both original dependencies,
`def-pc-derived-base-change-map` and
`lem-pc-ringed-spaces-derived-pullback-composition`, are used. The suggested
right-adjoint uniqueness argument is replaced by Mathlib's direct conjugation and
full-faithfulness APIs, but there was no separate import or node for it to remove.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error was found. The DAG's transposition argument is
implemented as a proved arbitrary-morphism pasting law, followed by explicit
isomorphism construction and cancellation. The short-route searches found generic
mate calculus rather than a scheme-derived transport theorem. LeanSearch returned
HTTP 500 and is recorded as unavailable; it is not claimed to give no match.

The literature sources used are Stacks [08HY](https://stacks.math.columbia.edu/tag/08HY)
(the counit construction) and [0D5S](https://stacks.math.columbia.edu/tag/0D5S)
(pullback composition). Local library and DAG searches found no existing declaration
of the specific pinned pasting law. The blueprint reference search
`base.change.*pasting|pasting.*base.change` returned zero matching blueprint nodes. Mathlib Mates and FullyFaithful supply the
conjugation, naturality and invertibility steps.

## New nodes

`lem-pc-derived-base-change-pasting`, in
`dag/nodes/sec-picard-framework/lem-pc-derived-base-change-pasting.json`, records
`AlgebraicGeometry.schemeDerivedBaseChange_pasting` in
`lean/Sheaf/AlgebraicGeometry/DerivedBaseChangePasting.lean`. This is a proved
intermediate identity for arbitrary upper-left morphisms, before unit cancellation.
It neither asserts the original existence conclusion nor repackages its hypotheses.
The node records the actual searches, source, complete proof route and unchanged
unit ancestry. There are no new holes and no change records.

## Second reading by B2

1. **Interfaces: PASS.** Diffed the existing module against the repository and
   compared the complete theorem signature byte for byte. All binders, hypotheses,
   conclusions, visibility, the existing public import, and the existing docstring
   are unchanged. The only existing-node changes are `proof`, `proof_deps`, and
   `proof_origin`. No definitions or target interfaces change; no change record or
   forced adaptation is required.
2. **Proof and trust: PASS.** Read both proofs line by line and compiled both files
   in import order (47.5 s and 16.4 s), without errors or warnings. Both delivered
   files contain no `sorry`, axiom, unsafe declaration, opaque declaration, extern,
   implemented_by, or kernel-check bypass. The inverse-composition comparisons
   imply faithfulness of both pullbacks and fullness of the pullback along e;
   Mathlib's fully-faithful adjunction instance makes its unit invertible. The
   witnesses j and k are actual composites of natural isomorphisms. The choices
   reuse the canonical comparisons and pinned adjunctions already used by
   schemeDerivedBaseChangeMap; no arbitrary new witness is taken from an unproved
   mere-existence assertion. Explicit axiom probes and the delivery's probe check
   the remaining upstream dependencies; their results are recorded below.
3. **New intermediate statement: PASS.** There are zero split-off holes. The new
   proved pasting statement supplies only the mate identity before unit
   cancellation, for arbitrary t; it does not restate the item's existence of j
   and k. Its docstring explains transposition, conjugation, naturality,
   associativity, equality transport, and cancellation, and its node records that
   argument. Checked identity t, identity e, zero E, and empty schemes: the unit
   remains on the pasting law's right side until the item proves it invertible;
   no cartesian or nonempty assumption is introduced. Read the counit construction
   in [Stacks 08HY](https://stacks.math.columbia.edu/tag/08HY) and composition in
   [Stacks 0D5S](https://stacks.math.columbia.edu/tag/0D5S); these support the
   categorical calculation, rather than claiming an independent geometric theorem.
   Repeated searches with different terms: LeanFinder "adjunction transposition
   composite right adjoint natural isomorphism compatibility" returned generic
   Adjunction.CompositionIso declarations; Loogle `CategoryTheory.conjugateEquiv`
   returned the conjugation APIs; grep `homEquiv.*conjugate|conjugate.*homEquiv|
   baseChange.*paste` returned a bicategorical mate declaration. Also searched
   lean/Sheaf and lean/WeilConjectures and read the generic conjugation and existing
   etale pasting candidates: none identifies these selected unbounded O-module
   pullback comparisons without the calculation supplied here.
4. **Route and pruning: PASS.** The target first reduces to the proved pasting
   identity and then cancels the unit, using Mathlib for conjugation and full
   faithfulness. The generic private Hom-equivalence identity is proved directly
   from unit_conjugateEquiv and naturality. All imports are used: FullyFaithful
   supplies the invertible-unit instance, Pasting supplies the reduction, and the
   public SchemeDerivedBaseChangeMap supplies the statement's vocabulary. In the
   new module Mates must be public because conjugateIsoEquiv occurs in its public
   signature. Both old proof dependencies remain used, so `No longer needed` is
   complete. Read the unit record sk-thm-picard-f-representable, including its
   representability step and empty realized lists; this categorical subargument
   replaces no unit step and changes neither the unit nor chapter route.
5. **DAG agreement: PASS.** Checked the original node diff, both Lean statements
   against the node records, and each proof_deps against the union of its proof
   steps' uses. The new node has source, searches, creation metadata, ancestry,
   chapter/unit, and its exact Lean signature. The item node describes precisely
   the inverse-comparison construction, full faithfulness, and unit cancellation;
   the new node describes precisely the transpose/coherence calculation.

Second reading changed only the doubled space before the existing theorem's
`:= by`, restoring exact signature-separator spacing, and added this independent
review. No mathematical repair, added hole, or pruning was needed.

Final explicit scratch-copy `#print axioms` checks:
- `AlgebraicGeometry.schemeDerivedBaseChange_pasting`: propext, Classical.choice,
  Quot.sound.
- `AlgebraicGeometry.exists_derivedBaseChange_top_iso`: propext, Classical.choice,
  Quot.sound.
The first concurrent top-iso probe reported sorryAx, but two subsequent probes
against the current compiled snapshot report none; the cause of the transient
snapshot discrepancy was not established.
independent probes of the selected pullback comparisons, pinned adjunction,
base-change definition, derived functors, and full-faithfulness APIs also report
only the three permitted axioms. No new hole was hidden by the delivery probe.
