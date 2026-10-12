## What changed
Proved `AlgebraicGeometry.GrpObj.lieEquiv_one` from `lieEquiv_mul` and the additive-group cancellation law.

## Proved and sorry left
`lieEquiv_one` is proved. `lieEquiv_mul` remains sorry; it requires the full two-parameter dual-number derivation calculation.

## No longer needed
No imports or DAG dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong
The identity theorem is an immediate formal consequence of the multiplication theorem, so no additional geometric construction is needed for it.

## Second reading by J2

1. Compared the delivered module against the repository with `diff -u`: only the body of
   `AlgebraicGeometry.GrpObj.lieEquiv_one` changes. All declaration signatures, definitions,
   docstrings, imports and existing proofs are byte-for-byte unchanged. No change record is needed.
2. The module compiles locally without errors or warnings. The identity proof specializes
   `lieEquiv_mul` to `(1, 1)`, rewrites `one_mul`, and cancels the common left summand to obtain
   `lieEquiv G 1 = 0`. The sole remaining direct `sorry` is the pre-existing
   `AlgebraicGeometry.GrpObj.lieEquiv_mul`; no new statements or split-off obligations were added.
   The delivery is a partial proof, not a claim that the multiplication theorem is closed.
   No forbidden declaration forms or hollow definitions were introduced.
3. No split-off statements need truth or duplication checks. Searched the library for the
   identity and multiplication laws and for `toLie`/`infDerivation` identity and multiplication
   lemmas; the only available multiplication law is the existing open `lieEquiv_mul`.
   Also searched Mathlib via msearch with cancellation-oriented queries. The short cancellation
   argument already uses Mathlib's `add_left_cancel` and is correct even for the trivial group.
4. Read the module from the bridge bijection down to the identity law. The existing import
   supplies definitions appearing in signatures and is correctly public; no import is unused.
   No old proof dependencies are pruned. The `sk-d-tangent` unit's statement and route are
   preserved; its existing `realized` fields are unchanged (both are empty).
5. Checked DAG occurrences of this module: they occur only in historical `lean_audit` open
   lists of five broader nodes, not in any node's primary `lean.module`. Therefore no existing
   node proof plan or dependency list describes this identity theorem and needs an update.
   The multiplication obligation remains recorded in those audit lists, including
   `def-wf-lie-algebra-derivation`, `lem-ag-cartier-reduced`, `lem-ag-closure-commutators`,
   `lem-wf-same-lie-closed-subgroup`, and `lem-sc-pic-tangent-space`.

Second reading changed the report to document the verification, the unchanged remaining
obligation, and the scope of the DAG audit. The Lean proof needed no repair.

A scratch copy with explicit `#print axioms` for all seven declarations also compiled.
`homOfDerivation_bijective`, `heq_of_pullbackCongr_inv_comp_homOfDerivation_eq`,
`toLie_bijective`, and `lieEquiv` use only `propext`, `Classical.choice`, and `Quot.sound`.
`lieEquiv_mul`, `lieEquiv_one`, and `lieEquiv_symm_add` additionally use `sorryAx`, as expected
from the still-open multiplication theorem. No other axiom was reported.
