## What changed

Replaced the sorry in `ModuleCat.exists_tor_ideal_connecting_formula` by a complete
Lean proof. It obtains a linear map on homology with the cycle formula, proves
its injectivity and image using a separate exactness statement, and composes it
with the hom of `P.isoLeftDerivedObj`. The proof explicitly transports the range
using surjectivity and cancels the inverse isomorphism in the cycle formula.
The original theorem signature, visibility and docstring are unchanged.

Added two modules, `Sheaf.RingTheory.TorIdealHomologyFormula` and
`Sheaf.RingTheory.TorIdealHomologyExactness`, imported privately by the item.
They separate construction and the exactness argument of the original plan.
Updated the item's DAG proof and dependencies to describe the Lean reduction.

## Proved and sorry left

Closed: `ModuleCat.exists_tor_ideal_connecting_formula`
(`lem-weil-pbc-tor-ideal-connecting-formula`). No sorry remains in the item's module.

Added holes:

- `ModuleCat.exists_tor_ideal_homology_formula`
  (`lem-weil-pbc-tor-ideal-homology-formula`): existence of the homology-level
  linear map with the finite-expression formula, with no injectivity or image
  conclusion and no multiplication-map hypothesis.
- `ModuleCat.tor_ideal_homology_exactness`
  (`lem-weil-pbc-tor-ideal-homology-exactness`): injectivity and image of any
  homology map satisfying that formula; it does not construct the map.

This is a decomposition, not a completed algebraic proof: one upper hole closed,
two lower holes added (net -1). All three delivered modules compile with
`lcompile.py --all`, without warnings other than the two intentional sorry
notifications. No definitions or axioms are added. In particular, the proof
only eliminates an existential theorem locally; it does not select arbitrary
data for a public definition.

## No longer needed

No original Lean imports removed. No claim that an entire module has become
unreachable. Removed from the parent node's direct `proof_deps`: `lem-weil-pbc-free-module-projective`,
`lem-weil-pbc-projective-module-flat`, `lem-weil-pbc-flat-tensor-exact`,
`lem-weil-pbc-tensor-right-exact`, and `lem-weil-pbc-snake-lemma-modules`.
The first four are retained transitively in the two new nodes; only the snake
lemma is bypassed by this decomposition. The original free/projective/flat and tensor-right-exactness nodes
remain needed by the two lower arguments. The direct cycle construction and
exactness argument bypass `lem-weil-pbc-snake-lemma-modules`; it is no longer a
proof dependency of this route. `def-weil-pbc-tor-modules` remains a direct
proof dependency for transport via `P.isoLeftDerivedObj`.

## Where the brief, the DAG or earlier work was wrong

The planned dependencies give general flatness, tensor exactness and snake-lemma
interfaces, but none states the specialized cycle formula or its homology
construction. The existing Tor kernel boundary construction resolves the other
argument and does not provide the formula relative to this specified resolution.
The existing first-variable Tor long exact sequence gives existential connecting
maps without the needed formula or comparison with this resolution.

A map's injectivity and kernel image alone do not determine its normalization.
Consequently the exactness lemma assumes the cycle formula, and does not assert
the formula for an arbitrary injective map with the same range.

Edge cases checked mathematically: I = 0 gives zero first homology of the
resolution; I = R gives a zero quotient complex and multiplication is an
isomorphism; M = 0 gives zero source and target. In each case both lower statements
have the expected zero-map behavior. In general every quotient tensor has a
lift y tensor 1 (finite tensor expansion and coefficient lifts); therefore the
formula hypothesis is not vacuous and determines a map on all homology classes.

Searches: LeanFinder returned cotangent connecting maps and `SnakeLemma.δ`,
which do not identify this tensor complex or augmentation. Loogle on `Tor'`
returned its definition, evaluation/map formulas and projective vanishing.
The logged grep returned general connecting-complex and cotangent files.
LeanSearch returned Internal Server Error (unavailable, not a negative result).
Read the official Stacks pages 00M5 and 00M6, the original dependency nodes,
and the relevant Mathlib tensor exactness and snake-lemma declarations.
A blueprint search for Tor, homology and ideal found no duplicate of either
new specialized statement. The unit's realized statements and steps are untouched.

## New nodes

`lem-weil-pbc-tor-ideal-homology-formula`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-tor-ideal-homology-formula.json`,
records the cycle-map construction and descent to homology. Its Lean module is
`Sheaf.RingTheory.TorIdealHomologyFormula`. Its source and docstring explain
lift independence, boundary vanishing and the explicit finite-expression value.

`lem-weil-pbc-tor-ideal-homology-exactness`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-tor-ideal-homology-exactness.json`,
records the kernel and image arguments for a map already satisfying the formula.
Its Lean module is `Sheaf.RingTheory.TorIdealHomologyExactness`. Its source and
docstring explain tensor lifting, resolution exactness, and boundary detection.

No change records or forced adaptations: existing interfaces are unchanged.

## Second reading by J4

1. Compared the delivered connecting-formula module with the repository version. The theorem signature, visibility, and docstring are unchanged byte for byte; only proof text and private imports were added. Verdict: pass.

2. Compiled all three sandbox modules with `lcompile.py --all`. The connecting theorem compiles without `sorry`; the two explicitly split-off declarations retain only their named `sorry`s. A scratch probe through `lcompile.py` printed axioms for all three declarations:
only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` occur, with
`sorryAx` expected from the two open statements. No custom axioms, unsafe
declarations, or hollow definitions were introduced. Verdict: pass.

3. Checked the two split-off statements against their proofs and edge cases (zero ideal, unit ideal, and zero module). They are strictly weaker than the parent theorem, are needed by its proof, and have docstrings and matching DAG nodes. Independent searches used Loogle `TensorProduct, LinearMap.ker`, LeanFinder
`free resolution modulo an ideal first homology embeds into ideal tensor module`,
and grep `homologyπ|isoLeftDerivedObj`, plus repository searches for ideal
homology and connecting formulas. Tensor right-exactness and cotangent results
provide ingredients, not either asserted statement. Read the existing
`TorKernelBoundaryConstruction` interface: it uses a chosen resolution of the
other tensor factor, so does not supply this formula for the specified `P`.
Also checked the cited [00M5](https://stacks.math.columbia.edu/tag/00M5) and
[00M6](https://stacks.math.columbia.edu/tag/00M6) source passages. Verdict: pass.

4. The parent proof uses the two new homology declarations and the existing Tor resolution interface; no original import can be removed. The snake-lemma dependency is pruned from the route as recorded above. Verdict: pass.

5. The unit route and realized unit statements are unchanged. DAG `proof`, `proof_deps`, and `proof_origin` agree with the Lean proof, and the two new nodes carry the required metadata. Verdict: pass.

Changed during second reading: added this review section, explicit axiom evidence,
and the complete list of removed direct proof dependencies (four retained
transitively). Added independent search results and descriptive titles to the two
new nodes. No Lean statements or proofs required repair. Closing either lower
hole requires the substantive tensor-complex construction or exactness argument;
neither has an immediate proof by a searched declaration.
