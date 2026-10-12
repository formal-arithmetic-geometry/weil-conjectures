## What changed

Reduced `RingHom.exists_fs_adic_closed_fiber_model` to the closed-fibre quotient construction,
explicit restriction of residue scalars, and a compatible residue-smooth model.
The existing declaration signature and docstring are unchanged. The two new intermediate
statements live in their own modules, `ResidueFormallySmoothTransport` and
`ModelOfResidueSmooth`; their proof-only imports are private imports.
Removed the initial worker's combined helper module. Constructed the residue algebra explicitly
instead of extracting an arbitrary algebra structure from a holed existence theorem.
Proved the scalar tower for the explicit composite A₀ action on the quotient.

## Proved and sorry left

Hole closed: `RingHom.exists_fs_adic_closed_fiber_model` (one original item hole).
Holes added and left:
- `RingHom.residue_formallySmooth_transport`, node
  `lem-weil-pbc-residue-formally-smooth-transport`.
- `RingHom.model_of_residue_smooth`, node `lem-weil-pbc-model-of-residue-smooth`.

This is a decomposition, not a completed sorry-free proof: one hole closed, two added,
net -1 locally. The ledger determines the targets' closure counts. Both helpers are proper
parts of the original argument, separating residue-scalar transport from model construction.
The model plan reuses the already stated `Algebra.exists_formallySmoothAdic_lift_residue_field`;
its remaining glue includes quotient maps and enlargement to the required carrier universe.
Compilation of all three modules is clean. Explicit `#print axioms` checks of all three
declarations show only permitted axioms and `sorryAx` from the two open helpers.
No new definition, arbitrary witness-defined data, or forbidden declaration is introduced.

## No longer needed

Removed the direct proof import `Sheaf.RingTheory.FormallySmoothAdicLift` from the item;
it remains a proof-only import of `ModelOfResidueSmooth` and is still needed transitively.
The original direct proof dependency `lem-weil-pbc-fs-adic-lift-from-residue-field` is now a
proof dependency of the model node. No old dependency is eliminated from the transitive route.
No library module is claimed pruned. The new nodes replace the direct lift step in the item DAG.
The initial worker's undelivered `FsAdicClosedFiberModelHelpers` module is removed.

## Where the brief, the DAG or earlier work was wrong

The initial worker's `model_of_residue_smooth` allowed unrelated A₀ and k₀ algebra actions;
the missing scalar tower invalidates its conclusion. For example take A₀ = Q[[t]],
E = Q((t)), its ordinary Q-action and the inclusion A₀ → E: the supposed quotient model
would force the image of t to be zero, whereas the inclusion makes it invertible.
The repaired new statement requires precisely the scalar tower demanded by the existing
residue-lift theorem. The transport helper originally returned an unspecified algebra action;
it now states formal smoothness for the concrete action composed with the residue map.
The original report incorrectly described this decomposition simply as a proved target.
The two new nodes originally lacked proof steps, search records and verbatim Lean signatures,
and the helper theorems lacked docstring proofs. These are supplied in this delivery.

## New nodes

`lem-weil-pbc-residue-formally-smooth-transport` states restriction along the bijective
residue map for the explicit algebra action, including independent universes.
Its proof transports test scalars and restricts oversized tests to a small generated subalgebra.

`lem-weil-pbc-model-of-residue-smooth` states the model step for a compatible residue-field
algebra, including the extra carrier universe. Its proof uses the existing residue-field lift,
composes the quotient with its algebra isomorphism, and transports along ULift with the small
test-algebra argument. No change record is needed: existing statements and definitions do not
change, and all changed imports of the item are proof-only.

## Second reading by R1

1. Compared every delivered existing declaration with the repository version using `diff`.
   The sole existing theorem's signature is byte for byte identical and its docstring is
   untouched. Public imports are identical; only proof imports and its proof body change.
2. Compiled the three files in dependency order with lcompile.py: no errors or warnings.
   Scanned for sorry and forbidden declarations: only the two public named helper theorems
   contain whole-proof sorries. Printed axioms for the item and both helpers in a scratch copy:
   only propext, Classical.choice, Quot.sound and the expected sorryAx occur.
3. Rejected and repaired the missing scalar compatibility as described above. Checked identity
   residue maps, field bases, field fibres (zero maximal ideals), and independent universes.
   These cases respect the repaired hypotheses and conclusions. New statements have complete
   natural-language docstring proofs and matching nodes. Searched Mathlib using LeanFinder,
   Loogle and grep with different queries; LeanSearch was unavailable and no negative verdict
   was inferred. Searched both library roots and read the existing residue-lift theorem and
   the existing private same-universe algebra-equivalence transport proof. The latter does
   not cover scalar equivalences and independent test universes. No duplicate public result
   with either repaired interface was found. Both remaining holes require substantial universe
   transport glue, so neither was closed in a few minutes.
4. Read top-down through the quotient construction and the two steps of the original plan.
   The model helper's plan uses the existing residue-field lift rather than restating the item.
   Removed unused direct imports; retained all statement imports and needed transitive route.
   Checked dag/units/sk-thm-p1.json realized: this item is below its realization level; neither
   the unit's statement nor its steps or realization records are bypassed or altered.
5. Rebuilt both new node records with self-contained statements, sources, proof steps and
   exact proof-dependency unions, blueprint ancestry, searches and verbatim Lean signatures.
   Updated the item node's proof, proof_deps and proof_origin to the written reduction.
   Existing statement, statement dependencies, target meanings and unit records are unchanged.

Changes by the second reader: explicit residue algebra construction and scalar-tower proof;
added the missing scalar-tower hypothesis to the new model statement; split the combined
helper file into one new module per statement; supplied docstring proofs and complete DAG
records; corrected decomposition accounting; removed the unused direct lift import and all
compiler warnings. The item signature remains unchanged.
