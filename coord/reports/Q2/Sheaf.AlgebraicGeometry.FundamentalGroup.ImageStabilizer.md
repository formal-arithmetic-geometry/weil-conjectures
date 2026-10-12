## What changed
The existing `fundamentalGroupMap_range_eq_stabilizer` signature is byte-for-byte unchanged.
Its proof combines the range equality and openness/index components in two new modules,
`ImageStabilizerRange` and `ImageStabilizerOpenIndex`. The second reader proved the latter
using `isConnected_of_connectedSpace`, Mathlib's fundamental-group transitivity instance,
`stabilizer_isOpen`, and `MulAction.index_stabilizer_of_transitive`.
Only the range equality remains admitted. Its docstring now gives the complete marked-fibre
restriction argument. The existing theorem's docstring was adjusted to reflect the actual
route through `toAutMulEquiv` and Mathlib transitivity. The item node records the conjunction
proof, and the two new nodes record their actual arguments and dependencies.

All added imports used only in the main proof are plain `import`. The existing public imports
are unchanged. The range helper publicly imports `Restriction`, which supplies its statement.
The openness/index helper publicly imports `ConstantCover` (for `fiberMk` and fundamental-group
structures) and `Mathlib.GroupTheory.Index` (for the index in its statement); its proof-only
`Connected` import is plain.

## Proved and sorry left
The item has one theorem: `fundamentalGroupMap_range_eq_stabilizer` now has a complete Lean
proof conditional on the range helper. It is not yet an axiom-clean mathematical result.
The new `fundamentalGroupMap_stabilizer_open_and_index` is proved with exactly the axioms
`propext`, `Classical.choice`, and `Quot.sound`.
The only directly admitted theorem in this delivery is
`fundamentalGroupMap_range_eq_stabilizer_range`, in `ImageStabilizerRange`, with node
`lem-galois-pi1-finite-etale-image-stabilizer-range`. Its body is exactly `by sorry`.
The main theorem and range helper have the three permitted axioms plus `sorryAx`.
All three modules compile locally with the prescribed launcher without errors or warnings.

## No longer needed
Removed from the item module:
- `Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence`;
- `Sheaf.AlgebraicGeometry.GaloisCategories`;
- `Sheaf.CategoryTheory.Galois.GaloisTransitive`;
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic`;
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Connected`;
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale`;
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality`.
The last four declarations are available through the statement imports or used in the helper.
The two new modules' unused imports from the first worker were also removed; in particular,
`Mathlib.GroupTheory.Index` is not needed in `ImageStabilizerRange`.

The old item's nine direct `proof_deps` are replaced by the two strict component nodes.
Seven remain in the helpers' combined dependency closure:
`lem-galois-pi1-functoriality`, `def-galois-categories`, `def-galois-fibre-functor`,
`lem-weil-pbc-finite-composition`, `lem-weil-pbc-etale-composition-cancellation`,
`lem-galois-finite-etale-connected-object`, and `lem-fet-galois-category`.
The delivery no longer needs `thm-galois-lc-etale` or `lem-galois-transitive`:
the former is unnecessary for a fundamental-group model of the finite-etale fibre functor;
the latter is replaced by Mathlib's transitivity instance. This is pruning of this proof's
route, not a claim that either node is globally unreachable.

## Where the brief, the DAG or earlier work was wrong
The first worker left the openness/index component admitted although it follows directly
from existing connectedness and Mathlib results. Both new node statements were incomplete
one-sentence descriptions, both had the same generic proof, and their search records did
not correspond to the searches of this second reading. Their docstrings lacked the complete
proof required for a named gap, and the existing item node had not been updated at all.
These faults are repaired. LeanSearch returned an HTTP internal-server error in both actual
queries and is recorded as unavailable, not as evidence of no match. LeanFinder, Loogle,
Mathlib grep, and library/upstream searches supplied the actual alternative results.
No existing theorem statement or definition was changed, so no change record is required.

## New nodes
`lem-galois-pi1-finite-etale-image-stabilizer-range` states only the image equality,
strictly one component of the item. Its three proof steps are the diagonal inclusion,
restriction to the marked fibre after finite-etale composition, and naturality/faithful
evaluation for the reverse inclusion. Its source is SGA 1 V.6.13 and §7, and its public
Lean theorem remains the single named gap.

`lem-galois-pi1-finite-etale-image-stabilizer-open-index` states only openness and index.
It records the connected-object and Galois-category dependencies and the precise Mathlib
lemmas used. Its Lean theorem is proved. Both nodes have self-contained mathematical
statements, full signatures, actual search records, and the item's chapter/unit.

## Second reading by Q2
1. Compared the existing delivered module with the repository using `diff` and a literal
   signature comparison. Verdict: its sole existing theorem signature is byte-for-byte
   unchanged, its two public imports are unchanged, and no definition or target changed.
   The additional modules and nodes were absent in the repository. No change record is needed.
2. Compiled all three modules in import order with `lcompile.py --all`. Used scratch copies
   and `#print axioms` for each of the three theorems. Verdict: clean compilation; the
   open/index helper has exactly the permitted axioms, and the main theorem and range helper
   also have `sorryAx` from the single named gap. There is no forbidden declaration or
   hollow definition, and the range theorem's body is exactly `by sorry`.
3. Read SGA 1 V.6.13 and §7, pp. 114–116 (arXiv math/0206203). The proposition identifies the
   slice-category fundamental group with the marked-point stabilizer; §7 specializes this
   to finite-etale covers. Read both new Lean signatures and their nodes. Verdict: the
   finite/etale, connectedness, geometric-point and fundamental-group hypotheses are intact;
   each conclusion is a strict component. The range restriction and its inverse work also
   for the identity cover. For a one-point fibre the stabilizer is the whole group, open
   with index one; the empty-fibre case is impossible because `a` is given. The transitivity
   and continuous-action lemmas cover these cases without extra hypotheses. Actual searches
   found no ready-made finite-etale range equality. The open/index component was closed
   rather than left as a duplicate admitted statement. The remaining gap has a complete
   natural-language proof and matching node.
4. Read the imported connectedness and fundamental-group declarations and took the shorter
   Mathlib route to openness/index. Verdict: proof-only imports are plain and unused imports
   are removed. The no-longer-needed list accounts for every old direct dependency, distinguishing
   retained helper dependencies from the two pruned nodes. Read `dag/units/sk-prop-h2.json`:
   its `realized.statement` and sole realized step are empty. No unit realization is removed
   or changed, and the finite-etale stabilizer clause of `thm-galois-fundamental` is retained.
5. Checked all delivered nodes against the Lean declarations, proof bodies and remaining gap.
   Verdict: the item now records conjunction introduction using the two components; the range
   node retains its genuine three-step argument; the proved open/index node records connectedness
   and Mathlib's continuous-action/transitivity argument. `proof_deps` equals the union of
   step uses, `proof_origin` identifies the route, and new node records have the required fields.

Changes by the second reader: proved openness/index; supplied full source/proof docstrings and
module headers; removed unused imports; repaired both new statements, proofs, search records
and blueprint provenance; added the updated existing node; replaced the inaccurate report.
