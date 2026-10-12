## What changed

`Sheaf.RingTheory.PopescuDesingularizationSubstitution` now proves
`Algebra.exists_desingularization_substitution` from the existing scalar-left-inverse
lemma and one new translated-presentation lemma. Its signature, universes, public imports,
and existing docstring are unchanged. The new proof-only import is
`Sheaf.RingTheory.PopescuTranslatedPresentation`; the proof also imports
`Mathlib.Tactic.LinearCombination` for polynomial identities.

The proof supplies the substantive substitution argument: a private polynomial-induction
proof of first-order expansion with remainder in the square of the variable ideal;
construction of the scalar inverse from constant minors; divisibility of the mapped
remainder by pi to the fourth power; the explicit formulas for e and g; divisibility of
all F by pi squared; and transport of the ideal-square condition. The lift correction
`C pi - P.sigma(pi)` is proved to belong to the relation ideal and its product with a
relation to the square. All this compiles without holes and uses no cancellation.

One new module, `Sheaf.RingTheory.PopescuTranslatedPresentation`, states the earlier
presentation-translation and constant-minor step. Its documented theorem is a strict part
of the source argument: it constructs neither the scalar inverse nor any substituted
polynomial or final ideal containment. The existing node's proof and proof dependencies
are updated to match the Lean proof. There are no interface changes or adaptations.

## Proved and sorry left

Closed the sole original hole in `Algebra.exists_desingularization_substitution`
(node `lem-weil-pbc-popescu-desingularization-substitution`). The item module has no
remaining `sorry`. Its private helper `Algebra.first_order_expansion` is proved as well.

Added one hole, `Algebra.exists_popescu_translated_presentation`, in
`Sheaf.RingTheory.PopescuTranslatedPresentation`
(node `lem-weil-pbc-popescu-translated-presentation`). This is the only `sorry` in the
delivery. It has its source and complete translation/constant-minor proof in the
module docstring and node. This delivery is a decomposition: one hole closed and one
strictly earlier hole added, net zero holes, with the substitution and ideal transport
now proved. The original matrix theorem is used as provided; this report does not claim
to close its transitive dependencies.

Compilation of both modules in import order passes; the delivery dry run performs the
axiom probe. There are no new definitions with postponed data.

## No longer needed

No original import or module is pruned. The old direct proof dependency
`def-weil-pbc-strictly-standard-element` is no longer unpacked in the item proof and
was removed from its `proof_deps`; it remains needed by the new translated-presentation
lemma and by the existing public signature, so its module is not globally prunable.
The scalar-left-inverse module is genuinely used and retained. Trial imports `Mathlib.RingTheory.Ideal.Maps` and `Mathlib.Tactic.Ring`
were removed after compilation confirmed that the existing public presentation imports
and `Mathlib.Tactic.LinearCombination` already supply their declarations/tactics.

The original elimination argument with a larger polynomial ring and the auxiliary
h_i is unnecessary here: substitution is evaluated directly in the required ULift
polynomial ring, so no new elimination or variable-renaming module is imported or added.
Strict standardness is used through the new translated-presentation node rather than
unpacked in the item's proof; it remains necessary and is not globally prunable.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The proof-plan definition nodes do not themselves
provide a translated presentation: the translation and constant-Jacobian comparison must
be stated as an intermediate theorem. That missing interface is the single new node.
The unit route `sk-thm-p1` is preserved: neither this item nor its helper replaces any
node in the unit's `realized` statement or steps.

The local literature checkout lacks `literature/stacks-project/smoothing.tex`. I read
the proof of Stacks Tag 07CR directly at https://stacks.math.columbia.edu/tag/07CR;
the cited source is the opening presentation/translation paragraphs through the
constant-minor identity, and the substitution computation plus ideal-square observation.
The extra Noetherian and annihilator-stability hypotheses in the full source lemma
are unused by these steps. The source's scalar-inverse lemma is the already imported
Tag 07DQ statement.

The new lemma was checked on pi=0 (relations have zero constants, minors need only
contain zero), on unit pi (the principal-ideal quotient conditions are vacuous), on the
zero ring, and on c=0 or m=0 (empty minors have determinant one, all initial-index
assertions are empty). None requires nontriviality or cancellation. The main proof
handles empty sums and zero divisors uniformly. The first-order expansion was also
checked by polynomial induction on constants, sums, and multiplication by a variable.

Mathlib searches ran via `msearch.py`: LeanSearch was unavailable with HTTP 500;
LeanFinder returned SubmersivePresentation coefficient/Jacobian results with incompatible
data; targeted grep found no translated-presentation theorem. Loogle did not recognize
`MvPolynomial.coeff`. Searches for desingularization, translation and constant minors
across the imported blueprint found no duplicate of the new statement.
The ancestor tool returns no ancestor because `created.item` in this stage is a module;
the new node retains the existing item's recorded blueprint ancestor and via chain.

## New nodes

`lem-weil-pbc-popescu-translated-presentation` is realized by
`Algebra.exists_popescu_translated_presentation` in
`lean/Sheaf/RingTheory/PopescuTranslatedPresentation.lean`. It states exactly the
presentation normalization and constant Jacobian minor identity needed before applying
the scalar-left-inverse lemma. It leaves all polynomial substitution and ideal transport
to the proved item module. Its proof follows the opening paragraphs of Tag 07CR,
with explicit polynomial-automorphism, derivative, quotient-kernel and determinant
arguments. No change record is needed because no existing statement, definition,
visibility or public import changes.

## Second reading by M2

1. **Interfaces: pass.** Read both delivered modules and the repository diff. The sole
   existing theorem's signature, universes, visibility and docstring are byte for byte
   unchanged. Only a proved private helper, proof-only imports and the proof body were
   added. The existing node differs only in `proof`, `proof_deps` and `proof_origin`.
   No definition, target statement or change affecting another module was altered.
2. **Proof and axioms: pass as a decomposition.** Compiled both files in import order
   with `lcompile.py`, without errors or warnings. Scanned for forbidden declarations
   and hidden holes: the new public translated-presentation theorem is the only direct
   `sorry`. Scratch-copy `#print axioms` reports only `propext`, `Classical.choice`,
   `Quot.sound` for `Algebra.first_order_expansion`; the main theorem additionally
   reports `sorryAx` through open dependencies. No public or private definition chooses
   data from an unproved existence theorem. Existential elimination within this
   existential theorem's proof introduces no library object or hollow definition.
3. **Split statement: pass.** Checked translation signs, transport of the chosen lift,
   quotient kernels, differentiation under translation, determinant transpose and
   the sign in `(1-π³t)π`. Read the opening argument of
   [Stacks Tag 07CR](https://stacks.math.columbia.edu/tag/07CR). Its translation and
   constant-minor step does not use Noetherianity or annihilator stability. For π=0
   the quotient section forces zero constants; for unit π the quotient conditions
   are vacuous and `t=π⁻³` makes the minor scalar zero. Empty generator or relation
   sets force c=0, with determinant one and empty initial assertions. The zero ring
   and zero divisors cause no cancellation. The lemma omits all scalar-inverse and
   substitution conclusions, so it is a strict reduction, not a restatement.
   An independent `msearch.py` LeanFinder query about shifting presentation generators
   to zero under a quotient section returned only presentation/coefficient ingredients;
   a grep query about shifted evaluation and constant derivatives, plus `rg` on both
   source roots and Mathlib polynomial/presentation files, found no replacement.
   Closing the remaining translation theorem requires the full presentation transport,
   not a short application of an available lemma.
4. **Route and pruning: pass after report correction.** Reviewed the polynomial induction,
   mapped remainder square, scalar inverse entries, explicit e/g formulas, lift correction
   and ideal maps. All retained imports are used; the new helper's public import is
   needed in its signature. Direct ULift substitution avoids the larger elimination
   ring. Checked `dag/units/sk-thm-p1.json`: no realized statement or step is bypassed.
   Corrected `## No longer needed` to name the removed direct strict-standardness node
   dependency and explain why its module remains needed transitively.
5. **DAG: pass.** The two nodes' `proof_deps` equal the unions of their proof-step `uses`.
   Their proof origins, declarations and signatures match the Lean. The new node has
   its source, full natural-language proof, searches, creation record, blueprint chain,
   chapter, unit and Lean record; its docstring also contains the proof and node id.

Second reading changed only the pruning explanation in this report and added this
review. The Lean and node files required no repair. One original hole is closed and
one strictly earlier hole is added: net zero, a decomposition rather than a completed
axiom-free proof of the target.
