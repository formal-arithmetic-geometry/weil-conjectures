## What changed

The module `Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorComponentImageOrbit` keeps its
original public target statement and imports. Its proof now introduces the two strict
implications and composes them to prove the equivalence. The two intermediate theorems
remain explicit named holes because the geometric deck-graph and stabilizer-quotient
arguments are not formalized in the available library. Their docstrings record the
complete source argument. The split-node metadata now depends on the two actual parent
proof dependencies (`lem-sbc-affine-torsor-split-label-laws` and
`lem-sbc-affine-torsor-split-point-lifting`), rather than circularly depending on the
parent target node.

## Proved and sorry left

The target `affine_torsor_component_image_orbit` is proved by applying the forward and
backward implications. Sorries remain only in
`affine_torsor_component_image_orbit_forward` and
`affine_torsor_component_image_orbit_backward`, with nodes
`lem-sbc-affine-torsor-component-image-orbit-forward` and
`lem-sbc-affine-torsor-component-image-orbit-backward`. This is a decomposition into two
strictly simpler directional statements, not a changed target.

## No longer needed

None. Both existing proof-dependency imports are used by the stated route and retained.

## Where the brief, the DAG or earlier work was wrong

The earlier split-node records listed the parent target node itself as each split
statement's `proof_deps`, creating a circular proof plan. The records now list the two
actual prerequisite nodes used by the parent route. No Lean declaration signature or
definition was changed.

## Second reading by B4

1. **Signatures and visibility.** I diffed the delivered module against the repository
version. Existing declarations, including the target theorem, have byte-for-byte
unchanged signatures; only new named intermediate declarations, their proof, and
comments were added. The auxiliary imported modules are unchanged.

2. **Compilation and axioms.** All three delivered modules compile with
`lcompile.py`. Explicit `#print axioms` checks on all three theorems return only `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx`, as expected from the named holes.
The target proof contains no new axiom mechanism, and the only remaining
`sorry`s are the two named split theorems listed above; neither definition contains a
`sorry`.

3. **Split statements.** Each split theorem is exactly one logical direction of the
parent equivalence with identical hypotheses and quantifiers. The statements are true by
the Tag 03SF deck-graph/stabilizer argument recorded in their docstrings, and are
strictly simpler than the biconditional. The corresponding DAG nodes and declarations
match.

4. **Shortest route and pruning.** The target is closed by direct introduction of the
biconditional and application of the two directional lemmas. The split-label-laws and
split-point-lifting imports are both required by the recorded geometric route; no import
or reachable node can be pruned.

5. **Unit route and metadata.** The unit `sk-prop-input-spreading` remains the unit of the
parent and split nodes. The `proof`, `proof_deps`, and `proof_origin` fields now follow
the actual route and avoid a circular dependency.

## New nodes

`lem-sbc-affine-torsor-component-image-orbit-forward` and
`lem-sbc-affine-torsor-component-image-orbit-backward` are the two directional
intermediate statements. Their node files record the source, strict implication
statements, actual proof dependencies, and the matching Lean declarations.

Second-reading changes: corrected the circular split-node dependencies; updated the
parent node to record the actual two-implication Lean proof; supplied verbatim Lean
signatures in the new nodes; converted the split comments to full declaration
docstrings; preserved the original target docstring on the target; removed long-line
warnings; repeated searches with different terminology (LeanSearch unavailable,
LeanFinder found only abstract results, Loogle and grep no direct match). Edge cases:
`d = 0` has no `x`; the trivial group permits only `y = x`, as in the parent argument.
The unit has no realized entry for this below-unit node, so none is bypassed or changed.
No hole was closed by an independent geometric proof: one original hole was closed
syntactically and two strictly directional holes added (net -1).
