## What changed

Proved `Algebra.locallyFreeCharpoly_eq` in the sandbox module. The proof handles the
subsingleton base-ring case by polynomial subsingleton elimination; in the nontrivial case it
uses `locallyFree_constantRank_eq` to align ranks and then applies the uniqueness parts of
`locallyFreeCharpoly_spec` (specialized at universe level 0). The specification and constant-rank
theorems remain as their existing postponed statements.

## Proved and sorry left

`Algebra.locallyFreeCharpoly_eq` is proved. `Algebra.locallyFreeCharpoly_spec` remains `sorry`.
`Algebra.locallyFree_constantRank_eq` remains `sorry`. Both are existing declarations of
node `def-weil-pbc-charpoly-locally-free`; no new statement was split off.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The first proof moved the constant-rank declaration before the independence theorem,
but left the independence docstring attached to the rank theorem and removed the original
rank docstring. It also used two `haveI` commands that triggered compiler warnings.
The second reader repaired these faults; no mathematical statement changed.


## Second reading by K2

1. Compared the complete sandbox module with the repository module by `diff`, and checked
   the declaration table with `stage3_delivery.diff_module`: `statement_changed` and
   `new_sorry` are empty. The definition body is unchanged. Every existing declaration's
   signature is byte for byte identical, including universes, both covers, local bases,
   the endomorphism and the nontriviality hypothesis only on the rank theorem. Reordering
   the rank theorem supplies a forward dependency without changing any statement.
2. Compiled the repaired file through `lcompile.py`: no errors or warnings. Scanned the
   complete module: no forbidden declarations and no missing data in the definition.
   A scratch copy with `#print axioms` for all four declarations reports exactly
   `propext`, `Classical.choice`, `Quot.sound` and `sorryAx`; the last is expected from
   the existing open existence, specification and rank results. The equality proof itself
   contains no `sorry`. Thus one of the three original postponed theorems is closed as
   a reduction, not an axiom-free completion of this module.
3. No new split-off statement or node. The existing specification and rank statements
   remain open under `def-weil-pbc-charpoly-locally-free`, with their source and word proofs.
   Checked the zero-ring case: polynomials are subsingleton, so differing ranks cause no
   problem. For a nonzero ring an empty cover cannot generate the unit ideal; rank zero
   is permitted and the basis-size comparison still holds. Rank comparison is invoked
   only after installing `Nontrivial A`. The specification at universe parameter zero
   quantifies over `Type u`, since `max u 0 = u`; both covers have exactly the same
   characterizing predicate after `subst m`. This makes uniqueness applicable with no
   universe restriction on the original theorem. The retained rank docstring describes
   comparison in a common nonzero localization, which is a strictly separate subproblem.
4. Read `CharpolyLocallyFree.lean`, the full defining node and `dag/units/sk-thm-p1.json`.
   The shortest equal-rank route is precisely uniqueness, and the zero-ring branch is
   subsingleton elimination. Searched Mathlib by Loogle (`Module.Basis, Localization.Away`,
   zero hits), LeanFinder (two covers with local bases of sizes n and m), and grep
   (`rankAtStalk|rank_eq|charpoly_baseChange`), plus `rg` in the local library. LeanFinder
   supplies invariant-basis-number and cardinality lemmas for two bases over the same
   ring; it does not supply the localization transport needed to finish the rank theorem.
   No direct replacement for the complete open statements was found. The sole public
   import supplies names in the existing definition and signatures, so it stays public.
   No old node dependency is pruned: the open specification and rank proofs still need
   the original five dependencies. The item is below the unit level, and no `realized`
   statement or step is bypassed or changed.
5. The existing node's three steps still describe this module: existence/specification,
   cover independence by uniqueness, and rank independence by common localization with
   a separate zero-ring case. The Lean independence proof composes the existing local
   specification and rank declarations, which realize those steps of the same node;
   its `proof_deps` and agent `proof_origin` remain accurate for the complete module.
   No node fields need correction and no new nodes or change records are required.

Changed: restored the original rank docstring before `locallyFree_constantRank_eq`,
restored the original independence docstring before `locallyFreeCharpoly_eq`, and replaced
both `haveI` commands with `have`. Kept the mathematical proof and all signatures intact.
