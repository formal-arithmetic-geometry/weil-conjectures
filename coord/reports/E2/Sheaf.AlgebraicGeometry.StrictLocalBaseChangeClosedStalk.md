## What changed

Replaced the rejected `True`-hypothesis reduction with a genuine decomposition. Added the
model-global-homology intermediate theorem and proved the closed-stalk transfer lemma in the
main module. The transfer proof uses the existing strictly henselian germ naturality theorem
and the geometric-point field-extension isomorphism. The target signature and its public imports are unchanged.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Etale.isIso_strictHenselization_baseChange_closedStalk`
by decomposition. The private general transfer lemma `closedStalk_isIso_of_sections` is
proved without sorry. Added one hole in the new intermediate theorem
`AlgebraicGeometry.Etale.isIso_strictHenselization_baseChange_modelGlobalHomology`
(node `lem-weil-pbc-strict-local-base-change-model-global-homology`); it is strictly a
global-sections statement for an arbitrary bounded-below complex and integer degree.
The original module has no remaining holes. This is a decomposition (one hole closed,
one hole added; net zero), not a completed proof of the dependency closure.

## No longer needed

Removed direct imports `Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology`
and `WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal` from the item;
both remain in the new model-global-homology module as dependencies of its unfinished
proof plan. The second reader also removed the redundant added import
`Mathlib.CategoryTheory.Sites.GlobalSections`; its declarations are already available.

The old direct proof dependencies no longer used directly by the item are
`def-weil-pbc-cartesian-square`, `def-weil-pbc-derived-inverse-image`,
`lem-weil-pbc-strict-local-base-change-global-homology`,
`lemma-weil-pbc-derived-exchange-coherence`, and
`lemma-weil-pbc-derived-exchange-replacement`. They remain dependencies of the new
model-global-homology node (the cartesian-square definition also remains in the item's
statement dependencies). No module is pruned from the transitive target closure.
The earlier rejected `closedStalk_of_globalHomology`, `globalHomology_of_baseChange`,
and the `True` hypothesis are absent from this delivery.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt was correctly rejected: its intermediate `closedStalk_of_globalHomology`
was the target restated with an unused `True` hypothesis. The replacement intermediate theorem
has a different conclusion (global sections for a chosen model, all complexes and degrees), and
the main theorem combines it with a separately proved stalk-transfer argument.
The helper first enlarges k to its algebraic closure; the residue composite maps to the
closed point by `PrimeSpectrum.comap_residue`. Naturality and the two germ isomorphisms
transfer the invertible section map to the enlarged stalk. The natural field-extension
comparison then transfers it back to the requested stalk. Zero sheaves, degree zero,
empty total spaces, and arbitrary separably closed k cause no exceptional case.

An attempted further proof of the global comparison using the existing derived mate
characterization did not compile within the 60-second limit. No part of that attempted
proof or additional transport statement is included.

## New nodes

`lem-weil-pbc-strict-local-base-change-model-global-homology` records the remaining global
comparison hole in its own module and DAG node.

## Second reading by E2

1. PASS: diffed both delivered modules against the repository. The only existing
   declaration is `isIso_strictHenselization_baseChange_closedStalk`; its signature
   is byte-for-byte unchanged. Public imports and definitions are unchanged; there
   are no forced adaptations or interface change records.
2. PASS: compiled both modules in import order through `lcompile.py`, without
   warnings or errors. Exactly one named sorry remains, in
   `isIso_strictHenselization_baseChange_modelGlobalHomology`. Scratch-copy
   `#print axioms` gives only `propext`, `Classical.choice`, and `Quot.sound` for
   `closedStalk_isIso_of_sections`; the two public theorems additionally use
   `sorryAx`. No forbidden declaration or hollow definition was introduced.
3. PASS: the new hole is the global-homology portion of the original argument,
   with no stalk field or geometric-stalk conclusion. The proved transfer lemma
   supplies the distinct remaining portion, so this is a genuine decomposition,
   not the target under a new name. Checked zero complexes, arbitrary integer
   degrees (including negative degrees), the identity model and alternative
   pullback models, zero sheaves and empty total spaces. The generality in K and
   n matches the existing canonical global comparison. Read Stacks
   [03Q9](https://stacks.math.columbia.edu/tag/03Q9),
   [03QO](https://stacks.math.columbia.edu/tag/03QO), and
   [0GIT](https://stacks.math.columbia.edu/tag/0GIT): the derived comparison does
   not require torsion. The named hole has a source, complete categorical proof
   plan and matching node. Independent leanfinder, loogle and grep searches with
   different queries, plus rg over both Lean roots, found no existing theorem
   for the chosen-model comparison. The global-sections theorem covers only the
   canonical model; the stalk formula is likewise canonical. Closing the new
   hole still requires mate identification and model transport, rather than a
   short application of an existing result.
4. PASS after repair: the proof follows the canonical global comparison, model
   transport and closed-stalk transfer route. Read `dag/units/sk-thm-p1.json`:
   no realized unit statement or step is bypassed. Proof-only imports remain
   plain imports. Removed the redundant GlobalSections import and made the
   direct dependency removals explicit above; none disappears transitively.
5. PASS after repair: the item's node names precisely the new global comparison
   and the two comparison theorems used by the transfer proof. The new node has
   all required provenance, statement, search, blueprint and Lean fields; its
   recorded Lean statement matches the module. Added the cartesian-square node
   to its proof dependencies and step uses, since its model-transport proof
   plan uses pullback cancellation.

Second reading changed only the redundant proof import, the new node's missing
cartesian-square proof dependency, and this report's pruning and review details.
The result remains one original hole closed and one new hole added (net zero).
