## What changed

Replaced the sole hole in `Sheaf.RingTheory.FlatLocalDepthFormula` with a complete
Lean induction, keeping the theorem's signature and its existing docstring unchanged.
The closed fibre's nontriviality, local structure, Noetherianity and maximal ideal
are obtained from Mathlib. Its depth and the source depth are finite by
`IsLocalRing.depth_le_supportDim`, the self-module support-dimension identity and
Mathlib's finite local Krull dimension instance.

The depth-zero argument is implemented explicitly: depth zero forces the maximal
ideal to be associated, since otherwise the existing nonzerodivisor lemma gives a
singleton regular sequence and depth at least one. Choose annihilator witnesses in
the source and fibre. Flat annihilator base change gives a target element with
annihilator its maximal ideal; the regular-sequence definition then gives target
depth zero. No depth-drop theorem is used in this base case.

The positive-depth quotient construction (original proof steps 5-8) is isolated in
`Sheaf.RingTheory.FlatLocalDepthReduction`. It produces compatible quotient rings,
a flat local map between them, and two successor equalities: one for target depth
and one for the source-plus-fibre depth sum. The main proof cancels the finite
summand one in ℕ∞ and applies induction uniformly over rings in the original two
universes. The new statement neither assumes nor asserts the flat local depth
formula for the smaller map. The induction and its base case remain in the item's
module, so this is a proper decomposition, not a renamed theorem.

Added proof imports of `Mathlib.RingTheory.Ideal.KrullsHeightTheorem` and
`Sheaf.RingTheory.FlatLocalDepthReduction`; updated the original node's proof,
proof dependencies and proof origin to match. The unit route is unchanged.

Both modules compile locally without errors or warnings. The authoritative Stacks
Tag 0338 proof was read online because the local clone omits the literature tree.

## Proved and sorry left

Closed the original hole:
`IsLocalRing.depth_eq_add_of_flat_local`
(node `lem-weil-pbc-flat-local-depth-formula`). No sorry remains in the item's
module. Its five private helper theorems are proved.

Added one public theorem whose whole proof is `by sorry`:
`IsLocalRing.exists_depth_reducing_flat_local_quotients`, in
`Sheaf.RingTheory.FlatLocalDepthReduction`
(node `lem-weil-pbc-flat-local-depth-reduction`). It is precisely the positive-depth
quotient construction and depth drops; the full natural-language proof and source
are in its docstring and node.

This delivery is a decomposition: one original hole closed and one lower hole
added, net zero new-hole improvement. Existing imported holes in
`IsLocalRing.depth_le_supportDim`, `exists_mem_maximalIdeal_smul_injective` and
`RingHom.annihilator_element_flat_base_change` are used as the stage intends.

## No longer needed

Removed these direct proof imports from the item's module:

- `Sheaf.RingTheory.FlatModInjective`
- `Sheaf.RingTheory.DepthQuotSMulTop`
- `Sheaf.RingTheory.DepthOverQuotientRing`

Their nodes `lem-weil-pbc-flat-mod-injective`,
`lem-weil-pbc-depth-drops-by-one`, `lem-weil-pbc-depth-over-quotient-ring`, and
`lem-weil-pbc-flat-module-quotient-flat` now belong to the new reduction's proof
plan instead of the main induction's direct dependencies. They remain needed
transitively; this delivery claims no whole module pruned from the target closure.
`def-weil-pbc-flat-ring-map` is also removed from the main node's direct `proof_deps`,
while remaining in its `stmt_deps` and the reduction's dependency plan. Its public
Mathlib import is retained for the unchanged signature.

The main proof does not need to prove or use finiteness of the target depth: only
source and fibre finiteness are needed to start induction.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The positive-depth steps require substantial glue that
the existing statements do not directly supply: transporting depth between
isomorphic rings, identifying the two closed fibres after quotienting, turning
the flat cokernel from `flat_mod_injective` into the appropriate quotient ring,
and assembling the induced flat local map. These are left together in the one
quotient-reduction theorem rather than silently assumed inside the induction.

The new statement's edge cases were checked mathematically: when the source is a
field, use J=0 and a regular element of the positive-depth fibre; when the fibre
has depth zero, choose a regular source element and quotient both source and
target, preserving the fibre; when the depth sum is zero the strict positivity
hypothesis excludes the construction. The ideals may be zero, but cannot be top,
so the quotient rings are nonzero. The theorem is independent of a formula for
any smaller map and supplies no induction hypothesis.

LeanSearch was attempted but returned an internal server error; its unavailable
status is recorded without a false no-match verdict. LeanFinder, Loogle, Mathlib
source searches and project source searches found no existing quotient-reduction
statement. The blueprint search for depth found no duplicate blueprint node.

## New nodes

`lem-weil-pbc-flat-local-depth-reduction` records
`IsLocalRing.exists_depth_reducing_flat_local_quotients` in the new module
`Sheaf.RingTheory.FlatLocalDepthReduction`. It groups the original depth-formula
plan's positive-depth cases, with compatible quotients and two depth-drop
equalities, preserving the original chapter, unit and blueprint ancestry. Its
proof cites the existing regular-sequence, flat-injectivity, annihilator,
flat-base-change, depth-drop and quotient change-of-rings nodes. There are no
change records because no existing public statement, definition or public import
is changed.

## Second reading by M2

1. **Statements unchanged.** I diffed `FlatLocalDepthFormula.lean` against the repository version and checked the original theorem signature byte for byte. The existing node changes only `proof`, `proof_deps`, and `proof_origin`; no target or existing declaration statement was changed. Verdict: pass.

2. **Proof and axioms.** Both delivered modules compile with `lcompile.py --all` without errors or warnings. The original theorem has no `sorry`; the only new `sorry` is the whole named public theorem `IsLocalRing.exists_depth_reducing_flat_local_quotients`, matching its node and docstring. The axiom probes report only the permitted base axioms plus `sorryAx` from the intentionally open reduction and existing imported statements. Verdict: pass.

3. **New statement.** The quotient-reduction statement is a strict decomposition of the positive-depth part of the induction: it supplies proper quotient ideals, a commuting flat local quotient map, and the two depth-drop equalities, while assuming no depth formula for the smaller map. Its hypotheses and conclusions match the two positive-depth cases of Stacks Tag 0338; edge cases with zero ideals and depth-zero fibre were checked. Searches found no duplicate declaration. Verdict: pass.

4. **Pruning and route.** The main proof uses the existing depth bound together with Mathlib finite Krull dimension and closed-fibre structure, proves the depth-zero case directly, and calls the reduction only for the successor case. The removed direct proof imports are `FlatModInjective`, `DepthQuotSMulTop`, and `DepthOverQuotientRing`; the main node also no longer needs the direct flat-module-quotient-flat and flat-ring-map proof dependencies; these remain recorded transitively in the reduction node where needed. The unit route is retained through the reduction node. Verdict: pass.

5. **DAG agreement.** The original node's proof steps and dependencies now name the reduction theorem, and the new node records its statement, source, proof plan, searches, module, and declaration. The report's no-longer-needed list was amended to include the removed direct flat-map dependency. Verdict: pass.

I completed the no-longer-needed dependency list and appended this review. In the new reduction module I changed `Noetherian.Basic` to a plain proof import and kept `Noetherian.Defs` public, since only the latter is needed by the statement. No declaration signature or proof body changed.
