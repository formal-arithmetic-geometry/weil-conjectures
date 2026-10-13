## What changed
Added `Sheaf.AlgebraicGeometry.SelfTorProjectionHomology`, an intermediate theorem separating the derived projection-formula and fixed representative-comparison step. The target module now imports it and proves `AlgebraicGeometry.nonempty_selfTor_pushforward_homology` by instantiating it with the literal termwise pullback and identity isomorphism. Added the corresponding DAG node and updated the target node proof route.

## Proved and sorry left
The target declaration `AlgebraicGeometry.nonempty_selfTor_pushforward_homology` is proved. The new declaration `AlgebraicGeometry.nonempty_selfTor_projection_homology` remains `sorry` (node `lem-pc-self-tor-projection-homology`), recording the projection formula, exact pushforward, and K-flat representative comparison.

## No longer needed
Removed the target module's proof-only imports `Sheaf.AlgebraicGeometry.QCqsDerivedProjectionIsoUniverses` and `Sheaf.Topology.ClosedImmersionPushforwardExact`; the intermediate module retains them privately. The corresponding direct proof dependencies are now reached through `lem-pc-self-tor-projection-homology`.

## Where the brief, the DAG or earlier work was wrong
The earlier attempt stopped without turning the stated projection-formula and representative-comparison step into a Lean reduction. The step can be stated as a strict intermediate theorem with an explicit comparison complex and then used to close the target.

## New nodes
`lem-pc-self-tor-projection-homology` is the intermediate projection and representative-comparison statement in `dag/nodes/sec-picard-framework/lem-pc-self-tor-projection-homology.json`.

## Earlier second reading (a previous round; superseded)
The target proof unfolds its lets and applies the intermediate declaration with `Q = T` and the identity isomorphism; the target signature is unchanged. The new statement is a strict representative-parameterized projection step and is exactly the unresolved step of the DAG.

## Second reading by V2

1. **Module comparison and statements.** Compared the delivered target module with the repository version. The target theorem signature is unchanged byte for byte; the added projection theorem is a separate parameterized representative-comparison statement.
2. **Compilation and proof safety.** Compiled both sandbox modules with `lcompile.py --all`; both compile cleanly. The target proof has no `sorry`; the sole remaining `sorry` is the named projection theorem, with its matching DAG node. No forbidden declarations or hollow definitions were added.
3. **New statement review.** Checked the projection theorem's hypotheses and conclusion, including identity representatives, arbitrary integer degree, zero/empty cases by the same functorial statement, and searched the repository for duplicate declarations. It is the strict unresolved projection/comparison step required by the target and is not already present.
4. **Pruning and DAG agreement.** The target proof uses only `lem-pc-self-tor-projection-homology`; its proof route and `proof_deps` were updated accordingly. Removed the target's proof-only imports of `QCqsDerivedProjectionIsoUniverses` and `ClosedImmersionPushforwardExact`; those remain private imports of the intermediate module. The unit route is preserved through the projection/comparison step.
5. **Definitions and dependencies.** No definitions or target statements changed. The intermediate theorem's public imports are limited to declarations needed in its signature; projection-formula and exact-pushforward modules are plain proof imports.

Changed in this second reading: pruned two target imports and kept the intermediate theorem import proof-only; no mathematical statements were changed.
