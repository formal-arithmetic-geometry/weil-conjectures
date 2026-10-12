## What changed

Proved `CategoryTheory.BigradedExactCouple.derivedCoupleFunctoriality` in
`lean/Sheaf/CategoryTheory/DerivedCoupleFunctoriality.lean`, with its signature and
existing docstrings unchanged. All supporting results are proved private helpers
in that same module; there are no new modules or public declarations; the only new definition is
the private, fully constructed `nextMorphism`.
The proof constructs one-step maps with Mathlib image/kernel/cokernel universal
properties, iterates them with dependent natural-number recursion, proves transport
of finite cycles and boundaries, passes to GLB/LUB subobjects, and descends to the
infinite quotient. Updated the existing node's proof and proof dependencies to
match this route. The unit's realized statement and steps are unchanged.

The kernel/projection equations uniquely determine the E map and the image
inclusion equation uniquely determines the D map, so the private `nextMorphism`
choice is determined up to equality. It adds no arbitrary witness data.

Validation: repeated single-file local compilation through `lcompile.py`; the final
single module compiles without errors or warnings in approximately three seconds.
The required `deliver3.py --no-push` dry run printed OK: compilation and
preflight pass except for the second reading, which the assigned second reader
writes. Nothing was pushed. Mathematical edge
cases are covered by the general category proof: zero maps, zero objects, initial
index zero, arbitrary nonnegative couple type, and all integer bidegrees. Infinite
transport uses only the supplied GLB/LUB universal properties; it assumes neither
a complete subobject lattice nor existence of arbitrary infinite limits.

## Proved and sorry left

Closed the module's sole hole:
`CategoryTheory.BigradedExactCouple.derivedCoupleFunctoriality`
(node `lem-sp-derived-couple-functoriality`). No `sorry` remains in the delivered
module and no holes are added or split off. Every new private helper is proved.
This is a proof from the existing declarations, rather than a decomposition.
The imported construction theorems in `ExactCouple` and
`ExactCoupleConvergence` retain their pre-existing holes and remain future work;
this delivery does not claim transitive axiom-free completion of those modules.

## No longer needed

Removed proof-only imports:

- `Sheaf.CategoryTheory.DerivedCoupleExact`: neither `derived_couple_exact` nor
  `pageCouple_image` is used. Its node `lem-sp-derived-couple-exact` is removed
  from this node's proof dependencies. No part of that module is needed by this
  proof; the exact couples and the restriction equations already come from
  `DerivedMaps` and `derivedMaps_exists` in `ExactCouple`.
- `Sheaf.CategoryTheory.ExactCouple`: the direct import is redundant because the
  retained public import `Sheaf.CategoryTheory.ExactCoupleConvergence` already
  publicly imports it. Its node `def-sp-exact-couple` remains necessary and is
  retained in the proof dependencies.

No further modules or nodes of the old plan are pruned. Global reachability of
`DerivedCoupleExact` from other consumers is left to the maintainer's queue.

## Where the brief, the DAG or earlier work was wrong

The existing declarations are usable and the statement is unchanged. The DAG's
extra dependency `lem-sp-derived-couple-exact` was unnecessary: the existence of
exact derived couples and their restriction equations is already part of the
construction in `def-sp-exact-couple`. The existing docstring retains the former
plan, as required for existing docstrings; the updated node records the actual
Lean proof. The full source files under `literature/stacks-project/` are absent
on this machine; Tags 011R and 011S were read from the official Stacks pages.
Tag 011R omits its proof, so the detailed categorical argument is explicitly
recorded as agent-written in `proof_origin`. No source or statement error was found.

## Second reading by F1

1. **No accidental visible changes.** Compared the delivered module with the repository
version. The `CoupleMorphism` structure and the statement of
`derivedCoupleFunctoriality` are byte for byte unchanged. The delivery only removes two
proof-only imports and fills the existing proof. The node changes are limited to the
stage-3-owned proof route and dependencies.

2. **Proof and trust basis.** Compiled the module with `lcompile.py` and compiled a
scratch copy with axiom probes. There are no `sorry` tokens, forbidden declarations, or
warnings in the delivered module. The target and all helpers use only `propext`,
`Classical.choice`, and `Quot.sound`, apart from the pre-existing `sorryAx` in imported
construction theorems (`derivedMaps_exists`, `d_comp_d`, `cycleBoundaryTower_exists`,
and related declarations).

3. **Statements and split-offs.** No statements were split off and no new public
statement was added. The private helper theorems are strict reductions of the node's
one-step construction, finite transport, and limiting quotient steps. I searched the
local library and Mathlib for exact-couple functoriality and the relevant image/factor
lemmas; no existing declaration duplicates the target or a helper. The edge cases are
covered uniformly by the universal properties, including zero maps and index zero.

4. **Shortest route and pruning.** The proof uses the existing exact-couple and
convergence constructions, then universal properties directly. It does not use
`DerivedCoupleExact`; that proof-only import and its node dependency are removed. The
direct `ExactCouple` import is also redundant because convergence publicly imports it.
The unit route remains the same: one-step derived maps, page recursion, finite cycle and
boundary transport, and GLB/LUB descent.

5. **DAG agreement.** The node's `proof`, `proof_deps`, and `proof_origin` match the
Lean proof. The statement and unit metadata are unchanged. No change record is needed.

**Changes made:** removed the two redundant imports, updated the existing node's
proof route and dependencies, and recorded this second reading. No holes were added or
split off.
