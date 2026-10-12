## What changed

Replaced the sole hole in `Sheaf.FieldTheory.CrossedProductForCocycle`,
`Field.exists_crossedProduct_data_for_cocycle`, by a complete Lean proof of its unchanged
statement from two independent smaller results. The proof imports
`Sheaf.FieldTheory.CocycleMonomialCoefficients` and
`Sheaf.FieldTheory.ProjectiveMatrixDescent` privately.

The regular coefficient construction is proved in `CocycleMonomialCoefficients` from
`FiniteGaloisCocycleData`: construct the regular permutation homomorphism with the supplied
finite quotient group law, compose it with the quotient map, and use its coefficients.
In the original module, `monomialLift` explicitly constructs both a matrix and its inverse.
Both inverse identities are proved by evaluating the finite matrix sums. The proof then
computes the mapped product of two such matrices, derives the exact prescribed scalar
defect, and derives the identity and composition laws for the semilinear conjugation action
by cancelling scalar matrices. Finally the descent result supplies a splitting for the same
matrix lift. No definition chooses unspecified data from a holed existence theorem.

The original theorem's named existential binder `hn` caused an unused-variable warning once
its proof was filled. A theorem-local `set_option linter.unusedVariables false in` suppresses
that existing signature's warning while preserving the signature verbatim. Every other
warning was removed. The node's proof and proof dependencies now describe the actual route.
The unit and chapter routes are unchanged; `sk-thm-br` has no realized node that is bypassed.

## Proved and sorry left

Closed original hole: `Field.exists_crossedProduct_data_for_cocycle`
(`new-crossed-product-for-cocycle`). No sorry remains in the original module.

Added holes, each the entire proof of a public theorem in its own new module:

- `Field.exists_finite_galois_cocycle_data`
  (`lem-sc-finite-galois-cocycle-data`, `Sheaf.FieldTheory.FiniteGaloisCocycleData`).
  This is only the finite quotient factorization and the twisted coefficient identity.
  It asserts no matrix lift, algebra, or splitting.
- `Field.exists_CSA_of_matrix_descent_action`
  (`lem-sc-projective-matrix-descent`, `Sheaf.FieldTheory.ProjectiveMatrixDescent`).
  This is descent of an already supplied locally constant genuine conjugation action.
  It assumes the action laws and neither constructs a prescribed cocycle lift nor asserts
  any scalar-defect equation.

Also proved `Field.exists_cocycle_monomial_coefficients`
(`lem-sc-cocycle-monomial-coefficients`), from the finite quotient lemma, with no direct sorry.
The private `monomialLift`, `monomialLift_mul_map`, `monomialLift_scalar_mul`,
`scalar_conjugation`, and `scalar_mul_conjugation` have complete proofs from Mathlib.

This is a decomposition: one original hole closed, two lower holes added, net -1 holes.
It is not a sorry-free proof of the original theorem. The two remaining holes are strictly
separate parts of the original argument; the coefficient construction and all matrix
calculations combining them are proved. All four delivered modules compiled cleanly via
`lcompile.py --all`.

Edge cases checked against the new statements: n = 0 is excluded exactly as in the original
conclusion; a trivial quotient gives n = 1; nonnormalized cocycles allow c(1,1) different
from 1 and the proved cancellation still gives T_1 = id. The descent argument uses sums
weighted by field elements and independence of automorphisms, with no division by the group
order, so positive characteristic dividing that order is allowed. For n = 1 and a scalar
lift, the invariant algebra is K and the descent orientation is the displayed equation.

## No longer needed

No existing imports, nodes, or modules are pruned. The original sole public import
`Sheaf.FieldTheory.BrauerScalarDefect` is still needed for the unchanged statement and the
prescribed cocycle evaluation. The two added proof imports are both used. The finite quotient
lemma is used by the proved coefficient module, and all its supplied clauses are used.
The generic descent module imports only Mathlib modules needed by its statement.

The first finite quotient reduction does not need to shrink its subgroup to fix cocycle
values or construct a finite fixed field: its equation retains the full Galois action on
coefficients. Fixing entries and constructing a finite fixed field remain in the separate
descent argument, where they are needed. This removes no existing module and is not counted
as module pruning.

## Where the brief, the DAG or earlier work was wrong

The original node's proof dependencies were empty; its prose plan contained the entire
finite quotient reduction and Galois descent. Thus those steps could not simply be imported
from named declarations. The new statements isolate them, and the intervening regular
coefficient and matrix constructions are written and compiled in Lean.

A new statement indexed by `Fin n` must distinguish the transported finite quotient group
multiplication from `Fin`'s built-in multiplication. Compilation exposed this during drafting.
The finite quotient statement now uses `@Mul.mul (Fin n) grp.toMul` explicitly, and the
proved coefficient construction passes that exact group and regular action explicitly to
`MulAction.toPermHom`. No erroneous version is delivered.

Searches used LeanFinder, Loogle, source rg, and blueprint searches. LeanSearch returned
Internal Server Error and is recorded as unavailable. Hits included degree-one Hilbert 90,
discrete H2 induction, and fixed-field automorphisms; none gives finite continuous cocycle
factorization or matrix-algebra descent. Existing realization modules above this item would
introduce circular imports. Stacks Tags 03R7 and 0DVG were read online, and the Brauer-group
section of the available Stacks source was read locally. The detailed constructions and
finite Galois descent proof are explicitly marked as expansions by an agent.

## New nodes

`lem-sc-finite-galois-cocycle-data` records the finite quotient factorization of the prescribed
cocycle and its twisted equation. It is the first remaining hole, in
`lean/Sheaf/FieldTheory/FiniteGaloisCocycleData.lean`.

`lem-sc-cocycle-monomial-coefficients` records the regular permutation homomorphism and unit
coefficients. Its construction is proved from the finite quotient result, in
`lean/Sheaf/FieldTheory/CocycleMonomialCoefficients.lean`.

`lem-sc-projective-matrix-descent` records descent of an already supplied genuine semilinear
matrix action to a central simple algebra with its splitting. It is the second remaining
hole, in `lean/Sheaf/FieldTheory/ProjectiveMatrixDescent.lean`.

All inherit the original chapter, unit, and blueprint ancestry and have complete proof
plans, search records, source references, and exact Lean signatures. There are no interface
changes to existing declarations, forced adaptations, or change records.

## Second reading by V1

1. **Existing interfaces: pass.** Read the repository/sandbox diff of the original module.
   Its sole existing theorem signature is byte for byte identical (also checked directly),
   and its existing docstring is unchanged. No existing definition or target is altered.
   The added imports are private proof imports. The other three modules and their
   declarations are new, with matching new nodes; no change record is needed.

2. **Proof and trust: pass as a decomposition.** All four modules compile without errors
   or warnings using `lcompile.py --all`. Independently compiled scratch copies with
   `#print axioms` for all four public theorems and all five private helpers. The helpers,
   including the explicit invertible matrix construction, use only `propext`,
   `Classical.choice`, and `Quot.sound`. The public theorems additionally use `sorryAx`,
   precisely as expected from the two named remaining holes. No forbidden declarations
   or implementation attributes occur, and no definition has a hole or chooses data from
   an unproved existence assertion. Existential witnesses are eliminated only inside
   proofs of propositions. Scratch probes were removed before delivery.

3. **New statements: pass.** Read each full statement, docstring proof, and node. Finite
   coset factorization concerns the prescribed cocycle, and its twisted equation follows
   by lifting the third quotient index; no surjectivity assumption is needed by its user.
   Descent assumes a supplied genuine action and asserts no prescribed scalar defect.
   The coefficient theorem constructs the regular permutation action from the exact
   transported group law. These are strictly separate parts of the original argument,
   not a renamed copy of the item. Checked nonnormalized constant cocycles, a trivial
   quotient, n = 1, exclusion of n = 0, and characteristics dividing the quotient order:
   the invariant-vector argument uses independence of automorphisms, not division by
   that order. Rechecked the source sketches at
   [03R7](https://stacks.math.columbia.edu/tag/03R7),
   [03R6](https://stacks.math.columbia.edu/tag/03R6), and
   [0DVG](https://stacks.math.columbia.edu/tag/0DVG). The detailed constructions are
   correctly identified as expansions by an agent.
   Independent LeanFinder and Loogle queries used finite-map factorization and invariant
   semilinear vector spaces, rather than the first reader's combined query. Source `rg`
   also found `ProfiniteGrp.exists_openNormalSubgroup_right_invariant`,
   `openSubgroup_fixedField_finite_separable`, and the homogeneous-coordinate comparison.
   Those are ingredients for future work, not either full split statement; the first
   remains sorry and the comparison does not specify this evaluation's finite quotient.
   Mathlib's cofiltered-limit factorization and field fixed-point results likewise do
   not close either hole in a few minutes. Added the independent search evidence to the
   new nodes. No duplicate result or quick closure was found.

4. **Route and pruning: pass.** Read the top-level proof downward through its two proof
   imports and the proved coefficient construction. Checked both inverse matrix sums,
   the columnwise mapped product, scalar cancellation at the identity, and the order
   of the mapped conjugations. The splitting uses the same explicitly constructed b.
   Each added proof import is used; the original public scalar-defect import is needed
   by the signature. Tested replacing the new descent module's IsSepClosed import by
   SeparableClosure: that module lacks the named SeparableClosure construction, so kept
   the working import. The old node has no proof dependencies to remove. The unit
   `sk-thm-br` has empty realized statement/step arrays, so no realized route is bypassed.
   No existing import, node, or module is pruned; the No longer needed section is complete.

5. **DAG agreement: pass.** Checked the verbatim signatures in all four node records,
   proof-step uses and their unions, proof origins, sources, ancestry, chapter/unit,
   created records, and status. The original node uses the coefficient and descent nodes;
   the coefficient node uses the finite quotient node; the remaining two nodes state
   exactly the two whole-theorem holes. The unchanged fields of the existing node remain
   intact. The report correctly counts one original hole closed and two holes added,
   net -1: this is a decomposition, not a sorry-free proof.

Second reading changed only this report and the new nodes' search records. No Lean
proof or statement required repair; the attempted import reduction was reverted.
