## What changed
Replaced the first worker's empty/nonempty case split by an actual induction on the finite union of the cover members. The invariant is universal degree-q vanishing on `S.sup id`, before imposing the ambient cover equation. The empty union is proved using the zero-stalk criterion and the additive Ext functor. The insertion case uses binary closed-union gluing. Rewriting the cover equation then uses a proved whole-space subtype comparison.

The existing theorem `TopCat.cohomology_vanishing_of_finite_closed_cover`, its signature and docstring, and all six public imports are unchanged. Three new modules are imported with plain `import`, because only the proof uses them. The original uncommitted empty/nonempty helpers and their two inaccurate node files were removed from this delivery. No existing statement or definition changed, so no change record is needed.

## Proved and sorry left
The body of the item's sole original theorem, `TopCat.cohomology_vanishing_of_finite_closed_cover`, is now a compiling finite induction with no local sorry. It is a reduction, not an axiom-free final proof: it still depends on the named binary gluing obligation and on the existing closed-pushforward comparison.

`TopCat.cohomology_vanishing_of_isEmpty` is proved using Mathlib alone; node `lem-sc-empty-space-cohomology-vanishing`.

`TopCat.cohomology_vanishing_of_whole_closed_subtype` is proved from `TopCat.cohomology_closed_immersion_pushforward` and Mathlib; node `lem-sc-whole-closed-subtype-cohomology-vanishing`. The existing comparison is still sorry upstream.

The sole sorry introduced by this delivery is `TopCat.cohomology_vanishing_of_closed_union` in `Sheaf.Topology.ClosedUnionCohomologyVanishing`; node `lem-sc-closed-union-cohomology-vanishing`. Its proof is exactly `by sorry`, and its docstring gives the complete open/closed argument, including support on the closure, comparison inside W, exactness, and degree zero. This is a binary gluing step, with no finite cover or induction hidden in its statement.

## No longer needed
No existing module or node is pruned from the transitive argument, and no original public import is removed. The old direct proof dependencies `lem-sc-noetherian-open-closed-cohomology-sequence`, `lem-sc-cohomology-closed-immersion-pushforward`, and `def-sc-topological-abelian-cohomology` have been replaced in the target's direct proof_deps by the three helper nodes. All three original nodes remain needed through those helpers; they are not globally prunable.

The uncommitted `new-node-finite-closed-cover-empty-base` and `new-node-finite-closed-cover-nonempty-step` and their declarations are discarded. They never existed in the repository baseline. The generic empty-space theorem replaces the first; the binary gluing theorem replaces the second, while the induction itself is now written in the target proof.

## Where the brief, the DAG or earlier work was wrong
The first worker's nonempty theorem had the target's entire conclusion with only an extra nonempty-cover assumption, and no induction hypothesis. Applying it after a case split was a relabelling, not a finite-cover induction. Both helper node statements copied the full finite-cover statement even though one Lean theorem only concerned an empty cover. Their docstrings lacked source details and complete proofs, and the target node's proof record was not updated.

The existing source route is mathematically sound. I read Stacks 02UZ, its open/closed component reduction, 02UT, and 02UV. For a binary union T=Z union W, closure_T(T minus Z) is contained in W, so pushing its support sheaf onto W makes the hypothesis on every sheaf on W usable. No vanishing in degree q-1 on intersections is necessary. The intrinsic subspace topology is preserved when Z and W are viewed inside T.

## Second reading by P1
1. **Unchanged visible statements: PASS.** Diffed every delivered module against the repository baseline. The target signature is byte for byte unchanged, with the same X, Noetherian instance, finite cover equation, arbitrary q, universal vanishing hypothesis, and ambient sheaf F. Its existing docstring and public imports are also unchanged. The other three modules are new, and no definition is introduced or changed. No undeclared statement change or change record is needed.

2. **Proof and compilation: PASS as a partial reduction.** Compiled all four modules in import order through lcompile.py. Only the named binary gluing theorem contains a local sorry. There is no axiom, unsafe, opaque, implemented_by, extern, definition sorry, or partial proof sorry. A scratch copy prints axioms for all four declarations: the empty-space proof uses only the permitted standard axioms; the whole-subtype and target reductions additionally use sorryAx from their documented open dependencies. The delivery tool also runs its all-declaration probe and the server compiler. No claim of complete axiom-free vanishing is made.

3. **Split statement and searches: PASS after repair.** The remaining obligation quantifies over exactly two arbitrary closed subsets of a Noetherian ambient space, and concludes vanishing on their union; it is strictly the binary gluing part of the argument, not the original arbitrary finite-cover theorem. Read its full natural-language proof against 02UZ/02UT/02UV. Checked empty Z or W, equal subsets, nested subsets, an empty ambient space, and q=0: the support/comparison argument still works; q=0 on a nonempty member makes the universal hypothesis impossible for a nonzero skyscraper sheaf, rather than causing a missing degree condition. Searches through msearch.py used different semantic terms (binary closed union; empty-space cohomology; homeomorphism/whole subtype), Loogle H', and grep on Mathlib, upstream and lean/Sheaf. No duplicate theorem was found. Mathlib's stalkwise-zero, Ext zero-preservation, presheaf pushforward composition/identity and Ext.chgUniv primitives are reused; LeanSearch returned Internal Server Error and is recorded as unavailable, not as no match.

4. **Top-down route and pruning: PASS after repair.** The target now contains the actual finite induction; its base is closed, and its remaining analytic step is isolated as binary gluing. The top-subtype comparison uses the existing comparison declaration rather than another restatement of finite-cover vanishing. All added target imports and the stalk/comparison imports used only in helper proofs are plain imports. The six original public imports provide the target's mathematical objects and cohomology instances. No unit route is bypassed: `dag/units/sk-thm-curveestimate.json` still realizes `thm-sc-proper-cohomology` as its statement and has no realized steps; the existing open/closed and closed-pushforward nodes remain in the helper route. The No longer needed section accounts for all three old direct proof_deps and distinguishes them from globally pruned nodes.

5. **Nodes and Lean: PASS after repair.** Opened the original node and all three replacement helper nodes. The target's proof/proof_deps/proof_origin now describe the exact empty/insert/cover-rewrite proof. Each new node has a self-contained statement, source, proof steps, their dependency union, real search records, blueprint ancestry, chapter/unit, created record, and a verbatim Lean signature. The binary node's proof names the existing open/closed and closed-pushforward declarations that provide the necessary short exact sequence, support and comparisons; the cohomology definition records the long exact sequence used at the middle group. The two first-worker nodes that misstated their Lean were removed from the uncommitted packet. No existing node field outside stage-3 ownership changed.

Changes made in this second reading: replaced the relabelled nonempty obligation by binary closed-union gluing; wrote a real finite induction; proved the empty-space case and whole-space subtype transfer; moved the new statements to their own modules; supplied complete source/proof docstrings and matching nodes; corrected dependency records and this report.

## New nodes
`lem-sc-empty-space-cohomology-vanishing`: generic empty topological space, all nonnegative degrees, proved by the zero-stalk criterion and the additive Ext functor. Module `Sheaf.Topology.EmptySpaceCohomologyVanishing`.

`lem-sc-closed-union-cohomology-vanishing`: universal degree-q vanishing on two closed subsets implies universal vanishing on their union. The sole new open obligation, with its full support and exact-sequence proof. Module `Sheaf.Topology.ClosedUnionCohomologyVanishing`.

`lem-sc-whole-closed-subtype-cohomology-vanishing`: universal vanishing on the subtype of the whole space implies ambient vanishing. Proved from the existing closed-pushforward comparison and pushforward composition/identity, with Ext universe transfer. Module `Sheaf.Topology.WholeSpaceClosedSubtypeCohomologyVanishing`.

No change records: no existing mathematical interface changed.
