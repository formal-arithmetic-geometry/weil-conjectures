## What changed

Proved both clauses of
`Module.finiteProjectiveCokernel_residue_localization` directly from Mathlib.
Its existing signature, visibility, universes, hypotheses and conclusion are unchanged.
No definition or public import changed, and no change record is needed.

Added two proved private implementation helpers in the item's module:
`Module.split_atPrime` transports the residue hypothesis to the prime localization
and applies Mathlib's local splitting criterion; `Module.spread_split` clears the
denominators and the left-inverse identity using finite presentation and finiteness.
The injective clause then splits the cokernel off the projective target.
For the bijective clause, right exactness and Nakayama kill the local cokernel;
Mathlib spreads the resulting local isomorphism.

The second reader removed the proposed `FiniteProjectiveCokernelLocalizationInjective`
and `FiniteProjectiveCokernelLocalizationBijective` modules and their undelivered nodes.
They are unnecessary now that both clauses have complete proofs. Updated the parent
node's `proof`, `proof_deps` and `proof_origin` to match the direct Mathlib route.

## Proved and sorry left

Closed the one original hole:
`Module.finiteProjectiveCokernel_residue_localization`.
Added zero holes; no `sorry` remains in the delivered module. This is a proof,
not a decomposition (local net: one hole closed, none added).

The first worker's proposed holes
`Module.finiteProjectiveCokernel_residue_localization_injective` and
`Module.finiteProjectiveCokernel_residue_localization_bijective` have been eliminated
from the delivery, rather than landed as new open statements.

Both private helpers and the parent were checked with `#print axioms` in a scratch
copy through `lcompile.py`. Each uses exactly `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx`. The complete file compiles without warnings.

## No longer needed

Removed these original proof imports and dependencies:

- `Sheaf.RingTheory.FiniteFreeMapResidueLocalization`, node
  `lem-pc-finite-free-map-residue-localization`.
- `Sheaf.RingTheory.FiniteProjectivePrimeLocalFree`, node
  `lem-weil-pbc-finite-projective-prime-local-free`.

This lists every old `proof_deps` entry. The parent now has no project-node proof
dependencies: its three steps are discharged by Mathlib and the proved private helpers.
These imports are pruned from this module; whether the modules leave the whole
closure depends on their other users and the maintainer's ledger.

Also removed the first worker's two new clause imports and nodes. The sole new
proof import is plain `import Mathlib.RingTheory.LocalRing.Module`; its public
transitive imports supply all other proof tools. Explicit imports of
`Mathlib.RingTheory.Flat.Stability` and
`Mathlib.LinearAlgebra.TensorProduct.Tower` were tested and found unnecessary.
The three original public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

The first delivery only paired two unproved clauses, closing one upper hole while
adding two lower holes. Both clauses are mathematically correct, but the proposed
node statements were not self-contained, their proof docstrings abbreviated the
localization transport, and their search records were inherited rather than fresh.
This review removes those proposed nodes and replaces the decomposition with a
complete proof using the shorter direct Mathlib route.

Searches with fresh wording through `msearch.py` (leanfinder, loogle, grep), plus `rg`
on the project and Mathlib, found
`IsLocalRing.split_injective_iff_lTensor_residueField_injective`,
`Module.FinitePresentation.exists_lift_of_isLocalizedModule`, and
`Module.FinitePresentation.exists_notMem_bijective`. The latter needs a local
isomorphism, so the proof first establishes it from the residue hypothesis using
local splitting and Nakayama.

The statement's source is [Stacks Tag 00O0](https://stacks.math.columbia.edu/tag/00O0),
parts (1) and (3). The source statement was checked online because this machine
has no local `literature/stacks-project/algebra.tex`.

## Second reading by B3

1. Compared the delivered module with the repository using `diff`, and compared
   the existing theorem signature as a byte string: identical. Only the proof,
   private helpers, proof documentation and plain proof imports change. No public
   definition, target statement or existing visibility changed. Verdict: pass.
2. Compiled the first worker's three modules, then compiled the complete repaired
   module through `lcompile.py`. No warnings, no holes, no forbidden declarations,
   and no definition with unproved data. Printed the axioms of the parent and both
   helpers: only the three permitted axioms. Verdict: pass.
3. Read both proposed clause statements and checked their small cases: zero source,
   zero target, zero map, and a prime equal to zero cause no exception to the local
   splitting/Nakayama argument. Fresh Mathlib and project searches found a complete
   route, so both split statements and nodes were removed. No split-off statement
   remains to document or deliver. Verdict: pass after repair.
4. Followed the proof from the parent downward, checked both original dependencies,
   and removed both unused imports. The theorem still provides the same local
   finite-projective-cokernel and isomorphism criteria used in the affine perfect
   cut. `dag/units/sk-prop-av-cube.json` has empty realized statement and step lists;
   neither removed node occurs in any unit's realized route. This is a change
   below the unit level; no unit statement or step changed. Verdict: pass.
5. Replaced the parent node's proposed clause-pairing route with the actual three
   Mathlib steps, and made `proof_deps` the empty union of their `uses`. Preserved
   all other original node fields and the Lean signature record. There are no
   new nodes. Verdict: pass after repair.

Second-reading changes: completed both clauses, eliminated both proposed lower
holes and their modules/nodes, pruned both original proof dependencies, minimized
proof imports, used explicit tensor syntax to avoid a new scoped-open command,
and corrected the proof documentation, DAG route and report.

The first dry run flagged the scoped tensor-notation opening as an interface command.
It was removed in favor of explicit `TensorProduct`/`TensorProduct.tmul` syntax;
no change to the interface is needed.
