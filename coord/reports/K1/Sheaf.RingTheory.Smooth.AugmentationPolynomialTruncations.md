## What changed

The existing declaration `Algebra.bijective_augmented_polynomial_truncations`
combines separately stated injectivity and surjectivity components. Its signature,
visibility, and original docstring are unchanged. Both new modules contain named
public theorem obligations. Their imports are needed by their signatures; the
parent imports them privately because only its proof needs them.

The second reader strengthened the new surjectivity component: it requires only
surjectivity modulo the square and does not assume formal smoothness. Its parent
application now passes `h₂.2`. No existing declaration's signature was changed.

## Proved and sorry left

Hole closed: `Algebra.bijective_augmented_polynomial_truncations` (one original hole).
Holes added: `Algebra.bijective_augmented_polynomial_truncations_injective`
(node `lem-sbc-formally-smooth-augmentation-truncations-injective`) and
`Algebra.bijective_augmented_polynomial_truncations_surjective`
(node `lem-sbc-formally-smooth-augmentation-truncations-surjective`).
These are the only sorries delivered. This is a decomposition, not a completed
sorry-free proof: one upper hole closed, two lower holes added (net −1).
The parent still depends on `sorryAx` through these components.

## No longer needed

No old proof dependency or import was removed from the parent: its original
`proof_deps` was empty. No old module is pruned. Removed the Smooth.Basic import
from the new surjectivity component after removing its unnecessary smoothness
hypothesis. That new component is a purely ideal-theoretic induction.

## Where the brief, the DAG or earlier work was wrong

The first worker's report described the parent as proved without clearly reporting
the negative hole balance. The two auxiliary docstrings lacked complete proofs,
their Lean statement records were empty, and their node statements referred back
to the parent rather than introducing their own objects. The searches were empty.
These defects are repaired. The components are distinct parts of the argument:
surjectivity is an ideal-power correction induction without smoothness; injectivity
uses square-zero lifting and inversion of a perturbation of polynomial coordinates.
Neither auxiliary states the full parent bijectivity conclusion.

## New nodes

`lem-sbc-formally-smooth-augmentation-truncations-surjective` states the ideal-power
correction induction with only first-order surjectivity. Its docstring gives the
representative construction. `lem-sbc-formally-smooth-augmentation-truncations-injective`
states the formal smooth lifting argument, with the surjectivity component used in
its proposed induction. Both have self-contained statements, verbatim Lean
signatures, source, proof plans, and the searches actually run by the reader.
No change record is needed: both declarations are new and no old interface changes.

## Second reading by K1

1. Compared the parent module with the repository using `diff`; its existing
signature is byte for byte unchanged, and no definition or target is changed.
Only private proof imports and the proof body differ. No forced adaptations.
2. Inspected every delivered module: no definition, forbidden declaration,
anonymous hole, or data choice; precisely two named theorem sorries. Compiled
all modules in import order and checked declaration axioms in a scratch module.
The expected `sorryAx` comes only from the two open obligations; no new axiom.
3. Checked both components against Stacks Project Tag 05D5's induction, including
k = 0, 1, 2, n = 0, and the zero ring. First-order surjectivity gives polynomial
representatives in each I-power layer without smoothness. Injectivity uses the
square-zero lift and the degree inequality 2r−1 ≥ r+1 for r ≥ 2. Complete proof
sketches are now in the docstrings. Ran LeanSearch (unavailable, HTTP 500), leanfinder, loogle, and grep with queries
different from the parent's earlier searches, and searched upstream and Sheaf
ring-theory sources; found supporting APIs but no direct replacement. The
auxiliaries are strictly separate parts of the bijectivity argument, not a renamed
bijectivity assertion. No few-minute closure of either substantial induction found.
4. The parent's combination is the shortest proof from these two obligations.
Imports are signature imports or private proof imports as appropriate. The old
proof dependencies were empty, so no old node is omitted from No longer needed.
Read `dag/units/sk-prop-input-spreading.json`: this is below its depth-two local
completion step; no unit route or realized record is changed.
5. Parent dependencies match the two component applications; new node statements
and Lean records now match exactly. Removed circular parent statement references,
filled the searches and blueprint origins, and recorded the injectivity plan's use
of surjectivity. New obligations remain explicitly open, with no claim of net
proof progress.

Changes by the reader: strengthened the new surjectivity theorem and adjusted its
call; removed its unnecessary smooth import; supplied full proof docstrings;
repaired node statements, signatures, search records, dependency metadata and
blueprint origins; corrected the report's hole accounting and long-line warnings.
