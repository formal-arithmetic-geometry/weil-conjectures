## What changed

Proved the body of
`AdicCompletion.isNoetherianRing_and_isAdicComplete_of_quotient` without changing its
signature or public imports. For `A = AdicCompletion I R` and
`J = I.map (algebraMap R A)`, Lean proves `J.FG`, `J`-adic completeness, and
Noetherianity of `A/J` by the surjective `evalOneₐ` map and its kernel calculation.
It then proves Noetherianity of the associated graded using finite type, applies the
complete-ideal lifting theorem to every ideal, and pairs Noetherianity with completeness.

Added three modules, each with its own node:
`AssociatedGradedFiniteType`, `AssociatedGradedIdealApproximation`, and
`CompleteIdealFiniteOfAssociatedGraded`. The first proves finite type by ideal-span,
ideal-product and direct-sum induction. The last proves the iteration, coefficient
Cauchy estimates, convergence, separatedness and finite spanning argument. The middle
states the remaining homogeneous-generator/one-step-approximation theorem.

Sources read: Stacks Project Tag 05GH, `lemma-completion-Noetherian`, proof, in the
local copy at `/home/ubuntu/weil-launcher/maint/bp/work/literature/stacks-project/algebra.tex`,
lines 23022–23063, and the tag page. The repository's canonical literature path is
absent on this machine. Mathlib completeness, quotient-kernel and finite-type theorem
signatures were read directly in the pinned source. The unit `sk-thm-p1` realized
statements and steps were checked; this split remains below its fixed route.

## Proved and sorry left

Closed the one original hole:
`AdicCompletion.isNoetherianRing_and_isAdicComplete_of_quotient`
(node `lem-weil-pbc-completion-noetherian-quotient-noetherian`).

Also proved, with no direct holes:
`Ideal.associatedGraded_finiteType`
(node `lem-weil-pbc-associated-graded-finite-type`) and
`Ideal.fg_of_isAdicComplete_of_associatedGraded`
(node `lem-weil-pbc-complete-ideal-finite-associated-graded`).

Added exactly one hole:
`Ideal.exists_associatedGraded_ideal_approximation`
(node `lem-weil-pbc-associated-graded-ideal-approximation`), in its own module with
proof exactly `:= by sorry`. It covers original steps 3–4 and requires neither
completeness nor Noetherianity of the quotient. The top theorem and the complete-ideal
lifting proof are complete from this statement and existing declarations.

This is a decomposition: one upper hole closed, one lower hole added, net zero direct
holes. Existing holes in `Sheaf.RingTheory.AssociatedGradedRing` remain dependencies;
none were altered or duplicated. No definition or data construction contains a hole.

All four delivered modules compiled without errors or warnings with `lcompile.py --all`.
Edge cases checked against the argument: empty generating families use `Fin 0` and
`Finset.univ.sup = 0`; the convergence proof also works with no generators; `J = 0`
reduces approximation to degree-zero ideal generation; `J = A` is harmless in the
lifting theorem because completeness forces the ring to be the zero ring. The
approximation statement is valid for `n = 0` and for `n < d i`, taking coefficients
zero in the latter case. No nontrivial-ring hypothesis was introduced.

## No longer needed

Removed the direct proof import `Sheaf.RingTheory.AssociatedGradedRing` from the item;
it remains required through the new proof modules, so its module and nodes are not
pruned. The replacement proof imports are
`Mathlib.RingTheory.AdicCompletion.Completeness`,
`Sheaf.RingTheory.AssociatedGradedFiniteType`, and
`Sheaf.RingTheory.CompleteIdealFiniteOfAssociatedGraded`.

Removed trial redundant imports `Mathlib.RingTheory.FiniteType` from the item and
`Mathlib.Algebra.BigOperators.Ring.Finset` from the complete-ideal module, then
recompiled successfully. Neither was an import of the original item. No whole module
or mathematical dependency is pruned. Original associated-graded and polynomial
notions move below the new nodes or remain behind the existing finite-type theorem;
the proof's direct dependencies are updated accordingly.

The old `proof_deps` entries removed from the item's direct proof plan are
`def-weil-pbc-associated-graded-ring` and `def-weil-pbc-mv-polynomial-ring`.
The associated-graded definition is still reached through the finite-type and lifting
nodes. The explicit polynomial-ring construction is replaced by finite algebraic
generation; polynomial machinery remains behind Mathlib's finite-type Noetherianity
theorem. These are removals from the direct plan, not claims of globally pruned modules.

## Where the brief, the DAG or earlier work was wrong

The original plan had no usable theorem for homogeneous initial-ideal generation or
its one-step approximation, and the associated-graded definition alone does not prove
those steps. The new approximation node makes that precise. No mathematical statement
was found false, and no signature or definition was changed.

LeanSearch returned HTTP Internal Server Error for the three new-node searches; the
node records say unavailable, not no match. Loogle/LeanFinder and Mathlib grep were
run and recorded. Repository and blueprint searches found no existing statement of
these general results; the projective-line graded-submodule theorem assumes a field
and a particular polynomial ring and cannot supply this general ideal statement.

## New nodes

`lem-weil-pbc-associated-graded-finite-type`: finite type of `gr_J(A)` over `A/J`
for finitely generated `J`. Its proof is complete by finite algebraic generation.
It uses the existing associated-graded multiplication and scalar formulas.

`lem-weil-pbc-associated-graded-ideal-approximation`: finite homogeneous lifts giving
one-step approximation in every filtered degree for an arbitrary ideal `K`.
This is the sole new remaining hole, strictly the initial-form part of the source proof.

`lem-weil-pbc-complete-ideal-finite-associated-graded`: lifts the preceding approximation
to finite generation of each ideal in a complete ring with Noetherian associated graded.
Its Lean proof explicitly constructs recursive remainders, takes coefficient limits,
and uses separatedness. No change records or forced adaptations were needed.

## Second reading by M3

1. **Unchanged interface: PASS.** Compared the item's entire file with the repository
   using `diff -u` and checked the existing declaration's signature byte for byte.
   Hypotheses, conclusion, universes, visibility and the two public imports are unchanged.
   The three additional modules are new; there are no adaptations or definition changes.
   Restored the existing theorem's original docstring to avoid an unnecessary API edit.
   Existing-node differences are exactly `proof`, `proof_deps` and `proof_origin`.

2. **Proof and axioms: PASS as a decomposition.** Independently compiled all four
   modules using `lcompile.py --all`, without errors or warnings. Scratch copies with
   `#print axioms` checked all four public theorems: each reports only `propext`,
   `Classical.choice`, `Quot.sound` and `sorryAx`. The latter is accounted for by the
   existing associated-graded structure holes and the one new approximation theorem.
   The only textual hole in the delivery is the whole proof of
   `Ideal.exists_associatedGraded_ideal_approximation`. No forbidden declaration,
   persistent data construction, or holed definition is added. The choices of generators,
   approximation coefficients and limits occur only inside proofs of propositions.
   This does not establish axiom-clean Noetherianity yet: one upper hole is replaced
   by one lower hole, with net zero direct holes.

3. **Split statement: PASS.** Read the complete approximation docstring, its node and
   the local Stacks 05GH proof. The homogeneous ideal is the degreewise image of
   `K ∩ J^n`; replacing generators by their components stays inside it, and projection
   to degree `n` yields the displayed coefficient powers. Natural subtraction includes
   `n < d i`; those coefficients can be zero. For `J = 0`, degree zero is generation
   of `K` in the Noetherian ring `A`; positive degrees have `x = 0`. For `J = A`,
   `gr_J(A) = 0` and the empty family satisfies the approximation statement for every
   `K`, even in a non-Noetherian `A`. For `K = 0` and the zero ring the empty family
   also works. These cases show that the hole asserts a finite initial-form step,
   not the completion theorem under another name. It is exactly the input needed for
   the convergent iteration. Independent LeanFinder and Mathlib grep searches used
   filtered-ring, consecutive-filtration and homogeneous-span terminology. The returned
   filtration results require stability or finite-generation assumptions not available
   here; homogeneous-ideal span lemmas do not construct this initial ideal or prove
   the representative approximation. Read `ReesAlgebra.bounded_generators` and
   `AdicCompletion.completedModule_associatedGraded_generators`: both require a
   Noetherian base, so neither replaces the split. The projective-line homogeneous
   generator results require a field and a particular polynomial ring. Closing the
   remaining hole requires the actual initial-ideal and projection construction,
   rather than a short application of an existing result.

4. **Route, imports and pruning: PASS after reporting repair.** Read the finite-type
   proof's span, ideal-product and direct-sum inductions, and the lifting proof's
   remainder recursion, telescoping identity, coefficient decay, completeness and
   separatedness argument. In the latter, the shift `D = sup d` works for an empty
   family and ensures every coefficient sequence is Cauchy in each power. The item's
   quotient-kernel equivalence and completeness transport use the existing Mathlib
   declarations directly. Each proof-only dependency is a plain import; public imports
   supply notions in the new theorem signatures. No shorter applicable route was found.
   Added the two removed old direct `proof_deps` entries explicitly under
   `## No longer needed`. No whole module is claimed pruned. Checked the unit
   `sk-thm-p1` record: this item and the new nodes are below its `realized` statements
   and steps, all of which retain their route.

5. **DAG agreement: PASS.** Checked every delivered node against its Lean signature,
   source, proof steps and imports. For each node, `proof_deps` equals the union of
   the steps' `uses`. New nodes have their own module, complete source-based proof,
   creation record, blueprint ancestry, chapter, unit, Lean record and three search
   kinds; the unavailable LeanSearch service is accurately recorded. The existing
   node's statement and `stmt_deps` are unchanged. No new persistent object is selected
   from a mere unproved existence theorem.

Second reading changed only the unnecessary existing-docstring edit and the report's
explicit direct-dependency pruning inventory; the checked Lean proof bodies are retained.
