## What changed

`Sheaf.FieldTheory.IntersectionSubfieldsDifferentialsPowers` now proves
`FieldTheory.intersection_subfields_differentials_powers`, with its signature and
visibility unchanged, from the existing subspace-intersection theorem and one new
family-free compositum-span theorem. The original extension-degree induction and
simple-extension case split are unnecessary. The unit's realized statements and steps
are untouched; this change is below the unit level.

The proof constructs a finite K-basis using Mathlib, takes its p-th powers, and proves
both independence over K^p and the exact K^p-coefficient description of L^p directly.
For a common compositum element x, it applies the existing subspace-intersection theorem
to the homogeneous equation sum a_i b_i = t*x. Independence makes t nonzero; dividing
by t gives coefficients in K^p. The empty index type is handled separately using
perfect fields and preservation of perfection by algebraic extensions.

Added proof imports: `Sheaf.FieldTheory.IntersectionSubfieldsSubspace`,
`Sheaf.FieldTheory.FrobeniusBasisCompositum`, `Mathlib.FieldTheory.Perfect`,
and `Mathlib.Algebra.CharP.Algebra`.
`Module.finBasis` and Frobenius injectivity are available through the other imports.
All original public imports remain unchanged.

Validation: both delivered modules compile individually via lcompile.py; the importing
module takes about four seconds. A pointwise proof of directedness avoids a kernel
comparison between two entire intermediate-field lattice structures, which had timed
out. No timeout increase or file splitting was used. The main docstring and delivered DAG both record the actual shorter argument.

## Proved and sorry left

Closed the one original hole:
`FieldTheory.intersection_subfields_differentials_powers`
(node `lem-weil-pbc-intersection-subfields-differentials-powers`). No sorry remains in
the item's module. Its coefficient independence and Frobenius expansion are proved in
Lean, as is the whole empty-index branch.

Added one lower hole:
`FieldTheory.frobenius_basis_compositum`
(node `lem-weil-pbc-frobenius-basis-compositum`), in its own module. It states only that
the S-span of a finite Frobenius basis is the corresponding compositum. It has no
indexed family, intersection equality, or directedness assumptions. Its complete
natural-language proof constructs a finite-dimensional subring and obtains inverses
by injective/surjective multiplication. This delivery is a decomposition, not a claim
that the target is now axiom-free: one original hole closed and one lower hole added.

The existing imported theorem
`IntermediateField.exists_ne_zero_mem_base_iff_forall_mem_intermediateField`
(node `lem-weil-pbc-intersection-subfields-subspace`) still has its pre-existing sorry;
this delivery neither changes nor duplicates it.

## No longer needed

Removed original proof imports `Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`
and `Mathlib.LinearAlgebra.Dimension.Free`. The second reading also removed the
redundant added import `Mathlib.Algebra.CharP.Reduced`; Frobenius injectivity and
`Module.finBasis` remain available transitively. Neither removal changes public imports.

Removed from this item's proof dependencies:
`lem-weil-pbc-field-degree-multiplicativity` (`Module.finrank_mul_finrank`),
`lem-weil-pbc-simple-algebraic-extension-power-basis`
(`IntermediateField.adjoin.powerBasis`), and `def-weil-algebraic-element`.
Neither an intermediate-field tower nor a primitive-element/power-basis argument is
used. These are Mathlib-backed dependencies, so this is route pruning, not a claim
that a whole Sheaf module has become globally unreachable. No public import removed.

## Where the brief, the DAG or earlier work was wrong

The existing proof plan is valid but substantially longer than necessary: homogeneous
coefficient descent through the already stated Tag 07P3 theorem handles arbitrary
finite bases and avoids both simple-extension cases.

The Stacks source's assertion of a direct span in the purely inseparable case is false
when the chosen p-th power generator belongs to one of the larger subfields. This was
already corrected in the supplied DAG. The new span theorem deliberately asserts no
independence over S; independence is used only over K^p, where it is proved in Lean.
Checks of its edge cases include S=K^p, S=K, degree one, inseparable extensions, and
possible dependence of the Frobenius vectors over S. An empty index family never enters
the nonempty subspace theorem.

Read the actual proofs of Stacks Tags 07P3 and 07P4 on the Stacks website because the
local .tex source is absent. The generalized finite-basis argument is marked as written
by an agent, with the exact source motivation recorded. No statement or definition was
changed and no adaptation of another holder's module is needed.

## New nodes

`lem-weil-pbc-frobenius-basis-compositum`:
`lean/Sheaf/FieldTheory/FrobeniusBasisCompositum.lean`, declaration
`FieldTheory.frobenius_basis_compositum`. This is the finite-dimensional subfield-span
step of Tag 07P4, generalized to any finite K-basis. Searches used LeanFinder, grep,
and LeanSearch (the latter returned Internal Server Error, recorded as unavailable).
Blueprint searches for finite spans and Frobenius images found no equivalent node.
The lemma is strictly a part of the argument; it says nothing about intersections.
No change record is required because existing signatures, definitions and public
imports are unchanged.


## Second reading by A3

1. **Visible declarations: pass.** Compared both delivered modules with the repository.
   The existing theorem's signature is byte for byte unchanged; the local ZMod algebra
   instance is unchanged. There are no existing definition or statement changes, no
   forced adaptations, and no change records are needed. The compositum lemma is new.

2. **Proof and axioms: pass as a decomposition.** Compiled both files in import order
   with lcompile.py and audited scratch copies with #print axioms. The main theorem
   uses only propext, Classical.choice, Quot.sound and sorryAx; the new lemma has the
   same list, and zmodAlgebraPowers uses only propext and Quot.sound. There is exactly
   one delivered sorry, the entire proof of FieldTheory.frobenius_basis_compositum.
   No forbidden declarations, hollow definitions, or arbitrary data selected from
   an unproved existence theorem occur. The existing subspace lemma remains open.

3. **Split statement: pass.** Read its docstring and node and independently checked
   the finite-dimensional subring argument: Frobenius expansions give 1 and product
   closure; injective multiplication on a finite-dimensional space gives inverses.
   S=K^p, S=K, degree one, and purely inseparable extensions all satisfy the assertion.
   For n=0 the basis hypothesis is impossible for a field. Dependence over S is allowed.
   This is only a compositum coefficient description, without a family or intersection,
   so it is strictly smaller than the original item. Independent LeanFinder, Loogle
   and grep searches for finite-dimensional subalgebras, inverse closure and field
   spans found useful generic tools (Subalgebra.toIntermediateField' and
   Subalgebra.isField_of_algebraic), but no matching compositum coefficient theorem.
   Searches of lean/Sheaf and lean/WeilConjectures found no duplicate. Formalizing
   the remaining Frobenius-span construction is not a one-line use of these tools;
   the truthful split is retained. Checked Stacks Tags 07P3 and 07P4 directly.

4. **Route and pruning: pass after repair.** Followed the main proof from the equality
   down to Frobenius coefficient independence, the compositum span, and homogeneous
   subspace descent. The empty family uses perfection, independently of Tag 07P3's
   nonempty-index hypothesis. No simpler already-proved library result was found.
   The old proof dependencies removed are exactly field-degree multiplicativity,
   simple-algebraic-extension power basis, and the algebraic-element definition;
   all appear in No longer needed. Read dag/units/sk-thm-p1.json: this item lies below
   its realized unit steps, none of which is bypassed or changed. Import-removal
   compiles identified Dimension.Free and CharP.Reduced as redundant; removed both.
   Perfect and CharP.Algebra are needed (their removal gives unknown identifiers).
   Both Sheaf proof imports are used by name. All proof-only imports are plain import.

5. **DAG agreement: pass.** The updated main node records the actual empty-family
   and coefficient-descent proof and its dependencies, with proof_origin.by=agent.
   The new node's Lean signature agrees modulo whitespace with its declaration;
   its source, complete proof, dependency union, searches, creation, blueprint,
   chapter, unit and Lean records are present. Existing node statement fields stay
   unchanged. No new statement merely restates the original item.

Changed the main docstring to describe the proof actually written, wrapped its one
long line to meet the 100-character convention, removed two redundant proof imports,
and corrected the report's import claims. No proof or statement was rewritten.
