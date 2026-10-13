## What changed

`StrictLocalRootInvariants.lean` now constructs the intermediate power map explicitly, proves its
root relation from Lagrange's equality, restricts the map to the actual equalizer subalgebra, and
uses injectivity and the image characterization to form the inverse algebra equivalence. Its
signature and both existing definitions are unchanged. Two non-public proof imports were added:
`StrictLocalRootsOfUnity` and `RootPowerMapInvariants`. The node's proof dependencies and proof
origin were updated to match this route.

The new module `StrictLocalRootsOfUnity.lean` fully proves the Hensel-lifting input. Reduction on
roots of unity is injective by a geometric-sum unit argument and surjective by the simple-root
Hensel condition. Cardinality and cyclicity transfer from the separably closed residue field.
Nonidentity roots have nonidentity residue, hence unit difference from 1.

The new module `RootPowerMapInvariants.lean` isolates the general monic-basis image calculation,
with one named public theorem and complete proof in words. It accepts an explicitly supplied
power map and rotations; it does not choose algebra data from an unproved existence theorem.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.Scheme.strict_local_root_invariants`, node
`lem-sbc-strict-local-root-invariants`, by a complete proof using the coefficient lemma below.
Fully proved the new theorem `AlgebraicGeometry.Scheme.strict_local_roots_of_unity`, node
`lem-sbc-strict-local-roots-of-unity`, using Mathlib and the existing Henselian interface.

The only added and remaining hole is `AlgebraicGeometry.Scheme.root_power_map_invariants`, node
`lem-sbc-root-power-map-invariants`. It has exactly `:= by sorry`. This delivery is a decomposition:
one original hole closed, one strictly smaller hole added, net zero. The Hensel-lifting part,
index positivity and divisibility, actual power-map construction, codomain restriction, and
bijection-to-equivalence assembly are now written and compiled. No hole remains in the item.

Edge cases checked mathematically: n=1, trivial K (all coefficients survive), full K (only
constants survive), h=0 and h a zero divisor. The monic basis argument does not cancel h or t.
The remaining lemma also allows the zero ring when its cardinality hypothesis forces n=1.

## No longer needed

No original import, node or module is pruned. All five original public imports support the
existing statements or definitions. Redundant direct imports of
`Mathlib.GroupTheory.SpecificGroups.Cyclic` were removed from both new modules after checking
that their statements compile with cyclicity available through their existing public imports.

## Where the brief, the DAG or earlier work was wrong

The original DAG had three substantive steps with empty dependency lists. Its mathematical plan
is sound, but the Hensel and coefficient arguments were not separate Lean declarations. They now
have nodes and statement modules; the Hensel argument is already proved. The route preserves the
trait-case intermediate-root calculation and changes no unit realization or target signature.

The cited Tags 0EYG and 09EV concern regular-divisor and DVR field calculations. They do not state
this arbitrary-ring invariant theorem verbatim. The delivered proof and remaining lemma explicitly
expand that calculation by a monic basis; `proof_origin.by` is `agent`, so the generalization is not
misattributed as a quotation. The source pages were read online because literature sources are not
installed in this clone. LeanSearch returned HTTP 500; LeanFinder, Loogle and actual Mathlib grep
searches were run and logged. No matching general invariant theorem was found.

## New nodes

`lem-sbc-strict-local-roots-of-unity`: Hensel lifting of roots, cyclicity, cardinality and unit
separation. Module `Sheaf.AlgebraicGeometry.Morphisms.StrictLocalRootsOfUnity`; theorem fully proved.

`lem-sbc-root-power-map-invariants`: injectivity and image of the explicitly supplied intermediate
power map under finite cyclic, cardinality and separation hypotheses. Module
`Sheaf.AlgebraicGeometry.Morphisms.RootPowerMapInvariants`; one named remaining `sorry`. It is
strictly smaller than the item: no strict henselian theory, no index conclusion, no choice or
construction of an isomorphism, and no fixed-subalgebra API is needed in its statement.

No statement changes, change records or forced adaptations.

## Second reading by W2

1. **Signatures:** Compared `StrictLocalRootInvariants.lean` with the repository version. Existing declarations and definitions are byte-for-byte unchanged; the two added imports are proof-only imports.

2. **Compilation and axioms:** Compiled all three delivered modules with `lcompile.py --all`. The completed Hensel theorem has only `propext`, `Classical.choice`, and `Quot.sound`; the target and coefficient theorem depend on the explicitly listed remaining `sorryAx` through the split coefficient lemma. No forbidden declarations or hollow definitions occur.

3. **Split statements:** Checked both new theorem statements against their proofs and DAG nodes. The roots-of-unity theorem is fully proved and the coefficient theorem is a strictly smaller, necessary decomposition with its documented `sorry`, source, and node. No duplicate library declaration was found.

4. **Route and pruning:** The target proof follows the unit route: root lifting, index calculation, explicit power map, fixed-subalgebra range, and equivalence assembly. Public imports needed by interfaces remain; `StrictLocalRootsOfUnity` and `RootPowerMapInvariants` are private proof imports. No old proof dependency or module is unused.

5. **DAG agreement:** Updated proof, proof dependencies, and proof origin agree with the Lean route. Unit realization and target statement are unchanged.

I changed only this review section and made no proof or interface changes after compilation. The delivered proof closes the target hole; the only remaining hole is the named `root_power_map_invariants` decomposition theorem.
