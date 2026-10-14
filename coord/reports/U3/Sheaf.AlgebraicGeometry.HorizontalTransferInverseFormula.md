## What changed

Proved `AlgebraicGeometry.horizontal_transfer_eq_of_inverse_formula` with its signature
and public imports unchanged. Two proved private generic lemmas identify the unit and
counit of a restricted adjunction under full-subcategory inclusions. After substituting
`hp`, expansion of conjugation identifies the direct-image comparison with the ambient
one. Composing with `j.inv`, cancelling the comparison, and applying Mathlib's
`unit_rightAdjointUniq_hom_app_assoc` reduces the result to equivalence-unit cancellation.
Updated the existing node's proof route to match these calculations.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.horizontal_transfer_eq_of_inverse_formula`
(node `lem-sc-horizontal-transfer-inverse-formula`). No holes added; no `sorry` remains
in the delivered module. The private helpers `restricted_unit_map` and
`restricted_counit_map` are proved. Existing imported foundational theorems may still
contain `sorry`; this delivery introduces no new dependency theorem or split.

## No longer needed

No imports or modules removed: both original public imports are required by the existing
signature. The theorem `dualityEquationBaseChangeMap_eq_inverseSquareMate` (node
`lem-sc-duality-base-change-inverse-square-mate`) is not used in this proof; its module
`Sheaf.AlgebraicGeometry.QCohInverseBaseChangeMate` is retained for `qcPullback` and
`qcDirectImage` in the signature. Removed that node from this item's proof dependencies.
No blueprint unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt had two anonymous unfinished proof holes and several
scheme-specific restriction helpers that made compilation exceed the time limit.
They are replaced by generic, proved restriction helpers and a complete calculation.
The original theorem and its mathematical plan are correct; no statement or definition
was changed. The calculation uses only adjunction identities, so it also applies to
identity arrows, empty schemes and zero objects without additional hypotheses.

## Second reading by U3

1. Interface: PASS. Diffed the only delivered module against the repository and
   separately compared the entire existing theorem signature byte for byte. It is
   unchanged, as are the public imports, options and existing docstring. There are
   no definition changes, forced adaptations or change records. The only additional
   declarations are two proved private restriction helpers.
2. Proof: PASS. Independently compiled the delivered file with lcompile.py without
   errors or warnings (46.8 s). Inspected the whole proof and scanned for forbidden
   declarations, hidden holes and unsafe options: none. The separate scratch-copy
   axiom check is recorded below. The calculation cancels j.inv, reflects through
   the faithful inclusion, identifies the restricted conjugate with the ambient
   conjugate and uses right-adjoint uniqueness to cancel the equivalence unit.
3. Splits: PASS, none. No new public statement or unproved theorem is introduced.
   The private helpers are identity-comparison specializations of Mathlib's
   map_restrictFullyFaithful_unit_app and map_restrictFullyFaithful_counit_app,
   both directly used in their proofs. Independent Loogle, Lean Finder and grep
   searches, including restriction/conjugation searches with different wording,
   found those general tools and no shorter complete transfer theorem. The helpers
   require only closure of the two full subcategories under L and R; their formulas
   also hold for empty full subcategories and identity functors.
4. Route and pruning: PASS. Both public imports supply names in the unchanged
   signature (horizontalMate comparisons and qcPullback/qcDirectImage). There is
   no proof-only public import to demote. The sole removed original proof dependency
   is lem-sc-duality-base-change-inverse-square-mate; its module remains needed for
   the signature, as already reported under No longer needed. Checked
   dag/units/sk-thm-picard-duality.json and searched all unit records: neither this
   item nor the removed dependency realizes a unit statement or step. No unit route
   is bypassed and no module is pruned.
5. DAG: PASS. The sandbox node changes only proof, proof_deps and proof_origin.
   Its two steps match the restriction/conjugation expansion and unit cancellation
   in Lean. The remaining dependencies supply the horizontal comparison definitions
   and the pinned derived adjunction; the unused inverse-square theorem is removed.
   There are no new nodes to audit.

Second reading changed only this report; the Lean proof and node were retained.

Scratch-copy #print axioms check compiled cleanly in 45.0 s:
`horizontal_transfer_eq_of_inverse_formula` uses `propext`, `Classical.choice`,
`Quot.sound` and `sorryAx` from existing foundational imports. Both private
restriction helpers use only `propext`, `Classical.choice` and `Quot.sound`.
No new dependency or axiom was introduced.
