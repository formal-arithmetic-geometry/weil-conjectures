## What changed

Replaced the original hole in `AlgebraicGeometry.pic_zero_jacobian_point_comparison`
with a proof from existing upstream declarations. Its signature is byte for byte unchanged;
there are no new public declarations or definitions. All public imports are unchanged.

The proof obtains one Jacobian representation from `exists_jacobian`. The existing
`exists_picardZero_equiv_picardFunctorDegree_zero` and
`exists_picardZero_equiv_picardFunctorDegree` compare the two Picard subgroups with values
of that same Picard sheaf. Their sheafification formulas and
`exists_mulEquiv_of_isPicardZeroMul` supply the multiplicative equivalences with specified
values. Naturality of the representation and the sheafification unit proves the square,
using `hj`, Picard functoriality, and the pullback projection equation.

Removed the first worker's unlanded `PicZeroJacobianPointComparisonCore` and
`PicZeroJacobianPointComparisonCompat` modules and their imports. Replaced the theorem's
proof docstring and updated the existing node's `proof`, `proof_deps`, and `proof_origin`
to describe the actual reduction. No change records are needed.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.pic_zero_jacobian_point_comparison`
(node `lem-sc-piczero-jacobian-point-comparison`). Added zero holes. There are no `sorry`s
in the delivered module, and no split obligations are delivered. This closes the local
hole from existing dependencies, rather than introducing a decomposition.

Removed the proposed holes `AlgebraicGeometry.pic_zero_jacobian_point_comparison_core`
and `AlgebraicGeometry.pic_zero_jacobian_point_comparison_compat` before delivery.
They were not part of the repository baseline.

`#print axioms AlgebraicGeometry.pic_zero_jacobian_point_comparison` on a scratch copy
reports exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` inherited from
the upstream obligations. This is not a claim that the target's dependency closure is
already axiom-clean. The delivered source has no forbidden declarations and no hollow
definitions. Compilation succeeds without warnings under the normal heartbeat limit.

## No longer needed

Removed these proof-only imports, with their old proof dependency nodes:

- `Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible`:
  `lem-sc-jacobian-base-change-compatible`. One representation's naturality supplies the
  square, so a comparison between two Jacobians is unnecessary.
- `Sheaf.AlgebraicGeometry.BaseChangeCurve`: `lem-sc-base-change-curve`.
  The existing geometric-point comparison only needs smooth relative dimension one and
  properness on the pullback; both follow from existing base-change instances.
- `Sheaf.AlgebraicGeometry.CurveBaseChangeRelativeDimensionOne`:
  `lem-sc-curve-base-change-relative-dimension-one`. The existing source-library dimension
  criterion proves relative dimension one on X, and its instance preserves it on the pullback.

Also removed redundant direct proof imports of
`WeilConjectures.AlgebraicGeometry.Regular`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced`.
Their results remain used through public imports of the retained
`WeilConjectures.AlgebraicGeometry.Picard.Jacobian`; their dependency nodes remain in the DAG.

The removed unlanded Core and Compat helper modules have no repository nodes.
These are dependency edges and imports pruned from this item; no assertion is made that
other targets no longer reach any of these existing modules.

## Where the brief, the DAG or earlier work was wrong

The first worker's compatibility statement was false: it quantified over arbitrary e and e'
without relating their choices to the representing identifications. Even for an identity
extension and an elliptic curve over an algebraically closed field of characteristic zero,
compose just one canonical equivalence with inversion. On a point of order three, the
claimed square fails. The submitted helpers also had no matching new DAG nodes and their
docstrings did not give complete sourced proofs. The original node metadata had not been
updated to reflect those proposed helpers. Compilation also exposed a long-line warning
and unnecessary `letI` warnings in the first submission.

The report's claim that two arbitrary interfaces gave a valid decomposition was therefore
rejected. The existing geometric-point Picard comparison provides the missing shorter
route without any new interface or new axiom. The original target statement is preserved.

## Second reading by W3

1. Compared the delivered module against the repository with `diff`, and compared the
   complete existing theorem signature programmatically: byte-identical. Only its proof,
   proof docstring, and private imports changed. No existing definition changed. PASS.
2. Compiled the replacement module with `lcompile.py`; it succeeds without warnings.
   Checked the source for `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, and
   `extern`; none occur. A scratch `#print axioms` gives only the three standard axioms
   and upstream `sorryAx`. No new definition chooses data from an unproved existence
   theorem. PASS for closure of this local hole; upstream holes remain.
3. Rejected and removed the false compatibility split and the unsupported Core split.
   No new statements or split obligations remain to audit. Independently searched with
   leanfinder for evaluation of the degree-zero Picard functor at algebraically closed
   extensions, loogle for representability naturality, and Mathlib grep for Picard and
   sheafification comparisons. Read the upstream point-comparison proofs and the group
   transport theorem; these provide the actual reduction. The identity extension requires
   no inequality of fields; genus zero gives trivial groups, and the same naturality
   calculation applies. PASS after repair.
4. Checked the proof downward from its compatibility conclusion. The existing upstream
   point comparisons and naturality are shorter than constructing and comparing two
   Jacobians. The sole remaining private import supplies the proof's declarations;
   all public imports are needed by its signature. All three unused old dependency nodes
   are listed above. Read `dag/units/sk-prop-ext-invariance.json`: its `realized` fields
   remain unchanged, and the proper-case degree-one route through the Jacobian and
   canonical base-change map is retained. PASS.
5. Updated the existing node's proof steps and dependency union to agree with the Lean:
   geometric integrality, one Jacobian representation, both canonical point comparisons,
   and naturality. No new nodes or changes to node statements were needed. PASS.

Second reading changed the invalid two-hole decomposition to a proof from existing
upstream results, removed both proposed helpers, pruned six private imports and three
old dependency edges, and corrected the proof documentation, node metadata, and report.
