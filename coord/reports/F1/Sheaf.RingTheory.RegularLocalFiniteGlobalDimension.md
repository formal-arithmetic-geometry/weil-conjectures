## What changed

Added `Sheaf.RingTheory.RegularLocalFiniteModuleResolution`, splitting the finite-module
resolution part of the argument into a named theorem. The target theorem now combines
that theorem with `Ring.hasGlobalDimensionLE_iff_finite_iff_cyclic`. Removed unused proof
imports from the target module.

## Proved and sorry left

Closed hole: `IsRegularLocalRing.hasGlobalDimensionLE_of_ringKrullDim_eq`
(node `lem-weil-pbc-regular-local-finite-gl-dim`). Its proof combines the finite-module
bound with `Ring.hasGlobalDimensionLE_iff_finite_iff_cyclic`.
Added hole: `IsRegularLocalRing.finiteModule_hasProjectiveResolutionLE`
(node `lem-weil-pbc-regular-local-finite-module-resolution`). This is the only delivered
`sorry`; its docstring gives the complete finite-module resolution argument.

This delivery is a decomposition: one hole closed and one added, net zero in the
import closure, not a completed proof of the regular-local global-dimension theorem.
The upper theorem still depends on `sorryAx` through this new theorem and the existing
finite-module criterion. No additional split-off hole was closed during second reading.

## No longer needed

Removed direct imports from the target module:
`Sheaf.Algebra.ProjectiveDimensionWellDefined`,
`Sheaf.RingTheory.CohenMacaulayFreeResolution`, `Sheaf.RingTheory.Depth`,
`Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence`, and
`Sheaf.RingTheory.RegularLocalMaximalCohenMacaulayFree`.

All old proof dependencies except
`lem-weil-pbc-global-dimension-finite-modules-suffice` moved out of the target node's
immediate proof: `def-weil-regular-scheme`, `def-weil-pbc-noetherian-ring`,
`lem-weil-pbc-regular-local-generators-regular-sequence`, `def-weil-pbc-depth`,
`def-weil-finitely-generated-module`, `lem-weil-pbc-cm-local-free-resolution-to-mcm`,
`def-weil-pbc-exact-sequence`, `lem-weil-pbc-regular-local-mcm-free`,
`def-weil-pbc-projective-module`, `def-weil-pbc-finite-global-dimension`, and
`lem-weil-pbc-projective-dimension-well-defined`.
They are retained in the new split theorem's planned proof. The removed direct imports
are proof-only imports there. No module is pruned from the target's transitive import
closure by this decomposition.

## Where the brief, the DAG or earlier work was wrong

The original node bundled the finite-module resolution construction and the passage to
all modules. The proof is reduced by making the finite-module part an explicit named
intermediate theorem; no statement is weakened.

## New nodes

`lem-weil-pbc-regular-local-finite-module-resolution` records the finite-module
resolution subclaim and its source. Its module is
`lean/Sheaf/RingTheory/RegularLocalFiniteModuleResolution.lean`.

## Second reading by F1

1. Compared the delivered target module with the repository by `diff -u`.
   The existing declaration's signature and both public imports are byte-for-byte
   unchanged; only proof-only imports and the proof body differ. No definitions or
   target statements change, and no change record is required. There are no adapted
   existing modules. Verdict: pass.
2. Compiled both files in import order with `lcompile.py --all` after repairs:
   no errors or warnings. Inspected both files: exactly one named theorem has `sorry`;
   no definitions, prohibited declarations, or arbitrary chosen data are added.
   Scratch copies with `#print axioms` compile; both theorems use only `sorryAx` and
   permitted standard axioms. Verdict: pass as a decomposition, not an axiom-free proof.
3. Checked the finite-module subclaim against Stacks
   [00O7](https://stacks.math.columbia.edu/tag/00O7) and
   [00NG](https://stacks.math.columbia.edu/tag/00NG), and read the existing regular-sequence,
   Cohen--Macaulay resolution, maximal-Cohen--Macaulay freeness, and padding statements.
   It isolates steps 1--4; the upper theorem still performs the distinct finite-to-all
   modules step. Edge cases: the zero module has the zero resolution; at dimension zero
   the ring is a field and finite modules are free; when depth equals dimension the
   exact sequence identifies its leftmost module with the original module. The zero
   ring cannot satisfy the displayed natural-number Krull dimension equality.
   Repeated searches with different wording through LeanFinder, Loogle and grep;
   `rg` on the library found only the upstream unspecified finite Ext-dimension result
   `IsRegularLocalRing.exists_hasProjectiveDimensionLE`, which does not provide the
   uniform bound `d` or a bounded projective resolution. Mathlib's regular-sequence
   dimension shifts also do not give the needed statement directly. Verdict: true,
   needed, and a proper part of the original argument; no exact duplicate found.
4. Reviewed the top-down reduction and all imports. Retained the short upper proof.
   Statement imports remain public; imports for the unfinished proof's plan are plain.
   The report now names every removed old proof dependency and distinguishes direct
   import removal from transitive pruning. Read `dag/units/sk-thm-p1.json`: neither this
   node nor its subclaim replaces a realized unit step; the existing unit route and
   `realized` entries are unchanged. Verdict: pass, with no transitive module pruning.
5. Compared node metadata with the Lean. The target node records exactly the two
   lemmas applied by its proof. The new node has a matching verbatim Lean signature,
   source, creator, searches, chapter/unit, and complete proof steps with their union
   as `proof_deps`. Its statement cites regularity, dimension and finite generation
   definitions as well as the projective-resolution definition. Verdict: pass after
   repair.

Second reading changes: supplied the missing complete proof docstring for the sole new
`sorry`; restored its five proof-only dependency imports; expanded its DAG proof to the
original finite-module steps, completed statement dependencies and recorded fresh
searches; restored non-owned fields of the existing node to the repository values;
corrected the report's hole accounting and pruning claims. No Lean statement or
existing proof body was changed by second reading.
