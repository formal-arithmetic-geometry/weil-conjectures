## What changed

Replaced the preliminary zero/positive-dimensional case split with the actual
open-closed cohomology argument in `Sheaf.Topology.IrreducibleIntegerExtensionVanishing`.
The existing declaration's signature and docstring are byte-for-byte unchanged.
All six new imports are plain, proof-only imports; existing public imports are retained.

The proof uses `noetherian_open_closed_cohomology_sequence` for the constant integer
sheaf, `cohomology_closed_immersion_pushforward` for its closed-complement term,
`irreducible_noetherian_constant_acyclic` for its middle term, and Mathlib's
`Ext.covariant_sequence_exact₁` to kill the first term. `Ext.chgUniv` handles the
larger Ext universe of the closed-pushforward interface without changing the target.
Empty opens use `abelianOpenExtensionByZero_stalks`; on an empty complement all
sheaves are zero by the stalk criterion, including their degree-zero cohomology.

Added two smaller modules: `Sheaf.Topology.IrreducibleOpenComplementDimension`,
whose chain-extension proof is complete, and
`Sheaf.Topology.ConstantIntegerOpenExtensionComparison`, whose comparison is proved using existing constant-sheaf isomorphisms.
A theorem-local `linter.unusedVariables` setting preserves the original nested binder
`hdimY` and quasi-compactness binder `hU`, which the stronger proof does not need;
renaming them would violate the signature requirement. No kernel or tactic checks
are disabled.

## Proved and sorry left

The original `TopCat.irreducible_integer_extension_vanishing` has a complete Lean
proof using the existing library interfaces and the proved comparison theorem.
The new `irreducible_open_complement_dimension` is proved without `sorry` and uses
only standard axioms. There is no `sorry` in the item's module.

No new sorry remains. TopCat.constant_integer_open_extension_comparison is proved by composing equivCommuteConstant' with overPullbackConstantSheafIso and applying the presheaf forgetful, extension-by-zero and sheafification functors.

Existing imported library theorems still have open proofs, so the original target's
axioms still include `sorryAx`; this delivery does not claim unconditional completion.

## No longer needed

No existing dependency module is pruned. Every old dependency remains used directly
or transitively. In particular `def-kun-topological-krull-dimension` now enters through
the proved complement-dimension lemma, and `def-sc-abelian-open-extension-by-zero`
through the stalk and comparison interfaces. The other five old dependencies are used
by the exact-sequence deduction. No existing public import was removed.

Removed the preliminary zero- and positive-dimensional helper declarations and their
undelivered nodes. Removed their unnecessary change record: no existing statement or
definition changes in this packet.

## Where the brief, the DAG or earlier work was wrong

The previous two new nodes repeated the entire target statement in prose, depended
back on the target, and had blueprint IDs inconsistent with their Lean docstrings.
Their signatures and records also disagreed on `hdimY`. Splitting into the two
cases of `d` did not discharge the geometric or cohomological argument. Those nodes
and the earlier case-only proof are superseded entirely.

The existing closed-pushforward comparison uses `HasExt.standard` in universe `u+1`,
whereas the unchanged item and its induction hypothesis use small Ext in universe `u`.
This is a genuine interface issue handled explicitly using Mathlib's universe-change
bijection; it is not a reason to change any signature.

## New nodes

`new-node-irreducible-open-complement-dimension` records the now-proved dimension
bound for a proper closed complement in an arbitrary irreducible space. It is independent
of Noetherianity and cohomology. Mapping chains into X and appending X proves the
successor bound; a point closure excludes a nonempty complement when d=0.

`new-node-constant-integer-open-extension-comparison` records the proved isomorphism
between extension of the constant sheaf on U and extension of the slice restriction of
the constant sheaf on X. Its docstring gives the natural restriction comparison and the
subsequent applications of extension by zero and sheafification. Both nodes have their
own modules, exact Lean signatures, sources, proof steps and actual search records.

No change record is needed: the original declaration and all definitions are unchanged.

## Earlier second reading (a previous round; superseded)

1. Compared the entire delivered item with the repository version using `diff` and
   checked the existing theorem signature with a byte-for-byte assertion. The signature
   and its docstring are unchanged; there are no changed definitions, no strengthened
   hypotheses and no weakened conclusion. The first reader's new case helpers and
   inaccurate change record were removed. Verdict: pass after repair.
2. Compiled all three modules locally in import order, without errors or warnings.
   Searched delivered Lean for forbidden declarations and verified no `sorry` remains.
   Printed axioms in a scratch module: the comparison and dimension lemmas use only
   `propext`, `Classical.choice`, and `Quot.sound`. The target still includes `sorryAx`
   from existing imported obligations. Verdict: pass; the comparison is proved.
3. Read Proposition 02UZ at https://stacks.math.columbia.edu/tag/02UZ against the two
   smaller statements. The comparison holds for U empty, U=X, disconnected spaces and
   arbitrary opens: restriction and slice identification precede functorial extension.
   For the dimension lemma, U=X gives an empty complement; d=0 excludes any point of
   a proper closed complement; for d>0 appending X gives e=d-1. No T0 or sobriety
   assumption is needed. The latter argument was fully proved during this reading.
   Searched LeanFinder, qualified Loogle, grep, upstream Lean, this library and the
   imported blueprint. The repair search found Mathlib's `equivCommuteConstant'` and
   `Opens.overEquivalence`, and upstream `overPullbackConstantSheafIso`. Their composition
   proves the comparison after applying the three functors with `mapIso`; its axiom
   check has no `sorryAx`. LeanSearch's earlier HTTP failure remains recorded.
   Verdict: pass; both smaller statements are proved.
4. Verified the source's open-closed route is used, rather than hiding vanishing inside a
   renamed lemma. The main proof calls the existing exact-sequence, constant acyclicity,
   closed-pushforward and stalk interfaces, and uses Mathlib Ext exactness directly.
   Every new proof import supplies a declaration actually used; both helper modules
   retain their statement-needed public imports; the comparison also has two plain
   proof-only imports supplying the constant-sheaf isomorphisms. All old dependencies remain transitive,
   so no pruning is claimed. Read `dag/units/sk-thm-curveestimate.json`: its realized
   statement is `thm-sc-proper-cohomology`, and its step list is empty. This delivery
   changes neither that unit nor its chapter route. Verdict: pass.
5. Read the delivered nodes against Lean. The main node now describes the actual
   zero-open, complement, comparison, acyclicity and Ext-boundary deduction. The new
   nodes' prose statements, docstrings, exact Lean records and dependencies agree;
   neither depends back on the target. The geometry node is proved from the dimension
   definition, with no cohomology dependency. Verdict: pass after replacing both old
   circular nodes and updating the main proof and proof-origin records.

Second reading changed the mathematical reduction, proved the complement-dimension
lemma, repaired the Ext universe transport, replaced both preliminary nodes, removed
an unnecessary change record, and rewrote the report to describe the actual packet.

Repair C5: re-read all three modules and their nodes after adding the reviewer's exact
comparison proof. The comparison signature and node are retained. The prior claim that
existing results do not close it was incorrect: the successful composition above closes
it, with only standard axioms. No new sorry remains in the three-module packet.

## Second reading by Q1

1. Compared the target module against the repository with `diff`, and asserted that
   the existing theorem signature is byte-for-byte identical. Its docstring is also
   unchanged. The two other delivered modules are new; no definition or existing
   statement changes, and no change record is required. Verdict: pass.
2. Independently compiled all three modules in import order with `lcompile.py --all`:
   no errors or warnings. Scanned the delivered Lean for sorry and forbidden forms;
   none occur in code. Recompiled the scratch axiom checks: both new helpers use only
   propext, Classical.choice and Quot.sound. The target additionally uses sorryAx
   through the existing imported obligations, as the report already discloses.
   Verdict: pass as a reduction using existing open dependencies.
3. Read both helper proofs from their signatures downward. Neither repeats the target:
   one proves a purely topological dimension bound, the other a functorial comparison.
   The dimension proof handles U=X and d=0 explicitly and requires no separation;
   its chain argument also applies to non-T0 irreducible spaces. The comparison works
   for empty U, U=X and disconnected X, since it uses isomorphisms of sheaves and
   functor.mapIso. No helper is left sorry. Repeated LeanFinder with a chain-extension
   query, Loogle with equivCommuteConstant, and grep with chain/slice-comparison terms;
   searched this library and read upstream KrullDimension and ConstantSheaf interfaces.
   No existing theorem supplies the same general dimension bound or the final composite
   extension comparison. The existing constant-sheaf isomorphisms are already reused.
   Verdict: pass.
4. Checked the actual short exact sequence, closed-pushforward comparison, constant
   acyclicity and Ext exactness against their interfaces and the final argument of
   https://stacks.math.columbia.edu/tag/02UZ. The Ext universe transport is an equivalence,
   so it preserves subsingletonness without changing a hypothesis. Every added import
   is proof-only and supplies a used declaration. Both new modules retain imports needed
   for their statements; their additional proof imports are plain. Every old proof
   dependency remains directly or transitively used, so no node is pruned. The unit
   sk-thm-curveestimate still realizes thm-sc-proper-cohomology and has no realized steps;
   its route is retained. Verdict: pass.
5. Checked all three JSON nodes against their Lean signatures and proofs. Exact signature
   text matches, and proof_deps equals the union of each proof's uses. The main node
   records the actual exact-sequence reduction. Both new nodes have source, full prose
   proof, searches, creation/blueprint metadata and matching Lean records, with no
   circular dependency on the target. Verdict: pass.

This second reading changed only this report: no mathematical or Lean repair was needed.
