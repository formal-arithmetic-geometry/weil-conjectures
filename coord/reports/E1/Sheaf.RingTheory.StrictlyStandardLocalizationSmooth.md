## What changed

The unchanged target theorem now unpacks its strictly standard witness, obtains a left
inverse for the original localized conormal map, transports that inverse through
`Algebra.Generators.principal_localization_naive_cotangent`, and applies
`Algebra.Extension.formallySmooth_iff_split_injection`. Finite presentation comes from
Mathlib's localization-away instance, imported only for the proof.

Added `Sheaf.RingTheory.StrictlyStandardLocalizedConormalSplit`, containing the exact
steps 1–4 of the previous plan with a complete source-based proof in its docstring.
Removed the first worker's proposed standard-smoothness module and node before delivery.
No existing declaration signature, definition, visibility, or public import changed.

## Proved and sorry left

Closed the upper hole in `Algebra.smooth_localizationAway_of_isStrictlyStandardElement`.
Added one lower hole: `Algebra.Presentation.strictlyStandard_localized_conormal_split`,
node `lem-weil-pbc-strictly-standard-localized-conormal-split`.
This is a decomposition, one hole closed and one added (net zero), not an axiom-free proof
of the target. The target and intermediate currently depend on `sorryAx`; other printed
axioms are only `propext`, `Classical.choice`, and `Quot.sound`.
The original plan's localization transport and formal-smoothness conclusion are now proved.
No data is chosen from an unproved existence statement: the intermediate provides only a
linear map used inside a proposition's proof, and no definition is added.

## No longer needed

Removed the target's proof-only import `Sheaf.LinearAlgebra.Matrix.LeftInverseMinors`;
its node remains needed by the lower splitting lemma. Retained
`Sheaf.AlgebraicGeometry.PrincipalLocalizationNaiveCotangent` and actually used it.

Old direct proof dependencies no longer used directly by the target:
`lem-weil-pbc-polynomial-ring-kahler-basis`, `lem-weil-pbc-matrix-left-inverse-minors`,
`lem-weil-pbc-localization-module-tensor` (all moved to the lower lemma's proof plan),
`def-weil-matrix`, `def-weil-submatrix`, and `def-weil-pbc-matrix-determinant` (their
matrix details are carried by the existing matrix-left-inverse node).
No globally unnecessary module is claimed: the matrix theorem is still needed downstream.
The superseded proposed standard-smoothness import/module/node is not delivered.

## Where the brief, the DAG or earlier work was wrong

The first worker replaced the smoothness target with an unproved stronger standard-smoothness
assertion, without a complete natural-language proof, and made that new node depend on the
original target, producing a DAG cycle. A split conormal injection establishes smoothness;
it does not by itself give Mathlib's submersive presentation with an invertible selected
Jacobian minor. The cited source states smoothness, not that stronger assertion.
The replacement is precisely the localized conormal splitting of Stacks 07CA's first
paragraph: https://stacks.math.columbia.edu/tag/07CA . Definition checked against
https://stacks.math.columbia.edu/tag/07C7 .

## New nodes

`lem-weil-pbc-strictly-standard-localized-conormal-split` records the original specified
presentation's localized conormal left inverse under its two explicit conditions. It is
strictly a part of the previous argument, with no smoothness conclusion, and depends on
the existing polynomial differential basis, matrix scalar left inverse, and module
localization/tensor nodes. It neither depends on nor imports the target. Searches were
rerun with different wording via leanfinder, loogle, and grep and recorded by msearch.py.
No change record is needed because no existing interface changes.

## Second reading by E1

1. Compared the delivered target with the repository using diff: the existing theorem
signature is byte for byte unchanged. Only its proof and proof-only imports changed.
No existing definition, target statement, or public import changed.
2. Compiled both modules in import order with lcompile.py. No compiler errors or warnings.
Only the named lower theorem has sorry; no axiom, unsafe, opaque, implemented_by, extern,
or sorry in a definition. Scratch #print axioms checks allow only the standard three
axioms plus sorryAx from the documented lower hole.
3. Rejected and removed the standard-smoothness split. The new splitting statement is the
source's genuine partial argument. Tested c=0 (the conormal module becomes zero), n=0,
m=0, a=0 (the localization is zero), and c=m (there are no remaining relations).
Its docstring gives the full matrix and generation argument. Searches of Mathlib,
upstream RingTheory, and lean/Sheaf found criteria and transport lemmas, no duplicate
of this two-condition result; smooth-to-conormal declarations require smoothness and
cannot prove this direction.
4. The target genuinely proves the localization transport and smoothness steps using the
existing principal-localization theorem and Mathlib criterion. The remaining lemma
contains only steps 1–4. Proof imports are used; the removed matrix import is documented.
Read dag/units/sk-thm-p1.json realized: this node is not a realizing node of the unit's
statement or steps, and the fixed unit route is untouched.
5. Rewrote the target node's proof, proof_deps and proof_origin to match the actual proof.
The new node has its complete source, proof steps, searches, creation metadata,
blueprint provenance, chapter/unit and verbatim Lean statement. Dependency cycles removed.

Second reading changed the proposed decomposition, supplied the actual conormal transport
proof, corrected node dependencies and proof documentation, and made the pruning report
explicit. The final delivery is a net-zero decomposition with one strictly smaller hole.

LeanSearch was also attempted for the lower statement; the service returned Internal
Server Error. This unavailability is recorded without an invented search verdict.
The successful Loogle, LeanFinder and source grep searches support the review.
