## What changed

Proved `IsIdempotentElem.eq_of_sub_mem_of_le_jacobson` using an algebraic argument. For
`d = e - e'`, idempotency gives `d^3 = d`; the Jacobson radical is closed under
multiplication, and `1 - d^2` is a unit by Mathlib's Jacobson criterion. Cancelling this
unit from `d(1-d^2)=0` yields `d=0`.

## Proved and sorry left

Proved `IsIdempotentElem.eq_of_sub_mem_of_le_jacobson` (1 of 1 previously open
theorems). No sorry remains in the delivered module; no statements were split off.

## No longer needed

The planned localization-at-maximal-ideals and annihilator argument is not needed. No
additional Sheaf modules are imported. The old `proof_deps` was empty, so no DAG
nodes or Sheaf imports are pruned. Removed the redundant proof import
`Mathlib.Tactic.Ring`: `Mathlib.Tactic.LinearCombination` supplies the ring tactic.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan is mathematically valid but longer than the direct cubic identity
argument available in a commutative ring.


## Second reading by M2

1. **Unchanged declarations: pass.** Compared the only delivered module with the
   repository using `diff`. The existing theorem signature is byte for byte identical:
   arbitrary `R : Type u`, `CommRing R`, ideal `J`, inclusion into `Ideal.jacobson ⊥`,
   both idempotency hypotheses, and `e - e' ∈ J`, concluding exactly `e = e'`.
   No definition, instance, public import, or other declaration changed. No change
   record is required.
2. **Kernel proof: pass.** Local compilation is clean. A scratch copy with
   `#print axioms IsIdempotentElem.eq_of_sub_mem_of_le_jacobson` reports exactly
   `propext`, `Classical.choice`, `Quot.sound`. Scanned the module: no `sorry`,
   `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`, and no definitions.
   Checked the cubic expansion, radical ideal closure, the precise Mathlib unit
   criterion `(1-d*d)-1 ∈ jacobson ⊥`, and right cancellation of that unit.
3. **Split statements: pass, none.** No new declaration or node and no open helper.
   The proof needs no nontriviality or characteristic assumption: in the zero ring
   it concludes the unique equality, with `J = ⊥` the difference is already zero,
   and in characteristic 2 the cubic identity remains an integral polynomial identity.
4. **Shortest route and pruning: pass.** Independently searched the upstream and
   Sheaf ring-theory sources, Mathlib idempotent files, and Loogle with
   `IsIdempotentElem, IsUnit, _ = _`. The upstream
   `IsIdempotentElem.eq_zero_of_mem_jacobson_bot` handles a single idempotent,
   whereas `e-e'` need not be idempotent; Mathlib nilpotent-difference uniqueness
   requires a stronger hypothesis. Neither directly replaces this short cubic proof.
   Removed the redundant `Mathlib.Tactic.Ring` import and recompiled successfully.
   Retained the two signature imports as public and LinearCombination as proof-only.
   The old `proof_deps` is empty, so the pruning list is complete. Read
   `dag/units/sk-thm-p1.json`, including `realized`: this auxiliary node realizes
   neither its statement nor a unit step. The replacement is below the unit level
   and preserves every realized unit route.
5. **DAG agreement: repaired, now pass.** The sandbox node had still described
   localization and claimed document provenance. Updated only `proof` and
   `proof_origin` to the actual three-step cubic/unit/cancellation argument,
   explicitly marked as an agent proof of the cited Stacks statement.
   `proof_deps` remains empty because all steps use elementary algebra and Mathlib.
   All remaining node fields, including the statement and Lean signature, are unchanged.

Changes made by the second reader: aligned the declaration's proof docstring and
node proof/provenance with the compiled proof; removed one redundant tactic import;
clarified the named proved theorem and empty pruning list in this report. The working
Lean proof was left intact. No source statement or definition was changed.
