## What changed

Proved the unchanged declaration
`Algebra.smoothAtMaximalIdeal_of_finrank_differentials_le_krullDim` in
`Sheaf.Paper.SmoothAtMaximalIdeal` from an explicit algebraic presentation obligation.
The main proof derives regularity from the differential bound, constructs Mathlib's naive
pre-submersive presentation, identifies its Jacobian matrix with the transpose of the displayed
minor, and builds a submersive presentation from its unit determinant. Standard smoothness implies
smoothness, which is transported through the supplied algebra isomorphism.

Added `Sheaf.Paper.MaximalIdealDifferentialCotangentDimension`, with a complete Lean proof of
`Algebra.finrank_cotangentSpace_atMaximal_eq_differentials`. The proof obtains a residue-field
section using Zariski's lemma and algebraic closedness, applies Mathlib's conormal-retraction
construction, uses the exact sequence to prove surjectivity, extends the resulting linear
equivalence to residue scalars, and cancels localized differential base change.

Added `Sheaf.Paper.RegularMaximalJacobianPresentation`, with one named remaining theorem about
polynomial equations, an algebra isomorphism, and a unit minor. Its plan uses the already proved
`IsRegularLocalRing.exists_span_eq_of_isRegularLocalRing_quotient` from the source library.
Independent cotangent classes give a minor without the old global-complete-intersection route.
The existing `Matrix.exists_strictMono_submatrix_det_ne_zero_of_mulVec_injective` supplies the
minor selection; no second statement of that result was created.

Updated the item's DAG proof, dependencies and origin, and added nodes for the two new modules.
No existing signature, definition, public import, target statement, or other agent's module changed.
All files were compiled together through `lcompile.py`; no compiler errors or warnings remain.
The required `deliver3.py --no-push` dry run printed OK, with only the independent second
reading left for the dispatcher's second worker. Nothing was pushed.

## Proved and sorry left

Closed the one original hole:
`Algebra.smoothAtMaximalIdeal_of_finrank_differentials_le_krullDim`
(node `lem-weil-pbc-smooth-at-maximal-ideal-alg-closed-differentials-bound`).
The item's module now has no `sorry`.

Also proved the new declaration
`Algebra.finrank_cotangentSpace_atMaximal_eq_differentials`
(node `lem-weil-pbc-maximal-ideal-differential-cotangent-dimension`), with no `sorry` dependencies
in its Lean proof: it uses Mathlib only.

Added exactly one hole:
`Algebra.exists_jacobian_unit_presentation_of_regularAtMaximal`
(node `lem-weil-pbc-regular-maximal-jacobian-presentation`). Its proof is exactly `by sorry`.
This is a decomposition, not a claim that the original theorem is axiom-clean: one original hole
closed and one new hole added (net zero before the closure pruning). The obligation is the
polynomial presentation and Jacobian calculation from the geometrical portion of the argument;
it neither assumes the original differential bound nor concludes smoothness. The main theorem
contains the proved regularity deduction and the full submersive-presentation/smoothness argument.

The new presentation statement was checked on zero equations (empty determinant 1), no residual
kernel (take the shrinking element b=1), zero-dimensional regular points, positive characteristic,
and differing universes for k and S. The zero ring has no maximal ideal, so gives no input case.
The construction uses two inverse variables and has determinant b*Delta^2, with explicit inverses.
Data from its existence theorem are used only in the proof of the original proposition;
no definition selects data from an unproved existence theorem.

## No longer needed

Removed all thirteen old proof-only imports from the item's module:

- `Sheaf.AlgebraicGeometry.GlobalCompleteIntersectionEquidimensional`
- `Sheaf.FieldTheory.SeparableExtension`
- `Sheaf.Paper.RelativeGlobalCompleteIntersectionPresentation`
- `Sheaf.Paper.SeparableResidueCotangentInjective`
- `Sheaf.RingTheory.ClosedPointDimensionLocalRing`
- `Sheaf.RingTheory.CompleteIntersectionOverField`
- `Sheaf.RingTheory.LCIRegularSequenceGlobalCompleteIntersection`
- `Sheaf.RingTheory.PolynomialRingMaximalLocalizationDimension`
- `Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence`
- `Sheaf.RingTheory.RegularLocalQuotientKernelParameters`
- `Sheaf.RingTheory.RelativeGlobalCompleteIntersectionConormalFree`
- `Sheaf.RingTheory.RelativeGlobalCompleteIntersectionSmoothJacobian`
- `Sheaf.RingTheory.SingularIdeal`

The following old proof-dependency nodes are absent from the delivered route:

- `def-weil-pbc-separable-field-extension`
- `lem-weil-pbc-separable-residue-cotangent-injective`
- `lem-weil-pbc-polynomial-ring-maximal-localization-dimension`
- `lem-weil-pbc-regular-local-quotient-kernel-parameters`
- `lem-weil-pbc-regular-local-generators-regular-sequence`
- `lem-weil-pbc-lci-regular-sequence-global-complete-intersection`
- `def-weil-pbc-complete-intersection-over-field`
- `lem-weil-pbc-global-complete-intersection-equidimensional`
- `lem-weil-pbc-closed-point-dimension-local-ring`
- `def-weil-pbc-relative-global-complete-intersection`
- `lem-weil-pbc-relative-global-complete-intersection-conormal-free`
- `lem-weil-pbc-relative-global-complete-intersection-smooth-jacobian`

In particular, the former regular-system-of-parameters/regular-sequence construction, complete
intersection shrinking and equidimensionality, conormal freeness, and relative-complete-intersection
Jacobian criterion are unnecessary here. Their Sheaf modules are not imported by either new
module. The separable-residue injection module and its field-extension definitions are replaced
by Mathlib's residue-section retraction. This describes pruning from this item's route; other
target branches can still need these modules.

The existing field-injective-matrix minor-selection module remains needed by the new presentation
obligation and is imported there. The polynomial regular-ring instance, polynomial differential
basis, and source-library independent-kernel-generator theorem also remain needed. None of these
is re-stated or claimed as newly proved.

## Where the brief, the DAG or earlier work was wrong

The original seven-step route is mathematically usable but longer than necessary below the unit
level. The source library already proves the independent-kernel-generator version of 00NR, which
supplies the independence needed for the Jacobian rank calculation directly. A finite residual
kernel can be killed by one element outside the prime, after which adjoining inverses produces
a unit Jacobian minor. Thus the global-complete-intersection detour is unnecessary.

The general prime smoothness criterion and regular-local/separable-residue smoothness theorem
cannot be used as shortcuts: their import closure reaches this item and would form a cycle.

Read the Stacks Project pages for Tags 00TR and 00TS, and the source/library declarations recorded
in the dependencies. The local literature directory omits the ignored Stacks source text; the
online source agrees with the node's cited arguments. LeanSearch returned Internal Server Error
for both searches and is recorded as unavailable in `searches.jsonl`; LeanFinder, Loogle, and
Mathlib source searches ran successfully. Blueprint searches found no duplicate of the cotangent
comparison; the existing square-Jacobian nodes concern etale algebras, rather than this regular
closed-point construction with arbitrary relative dimension. No unit statement or realized step
was bypassed or changed: this item is strictly below the unit's realized nodes.

## New nodes

`lem-weil-pbc-maximal-ideal-differential-cotangent-dimension` records the proved 00TR comparison
with the cotangent space of the prime localization. Its proof is implemented using Mathlib's
residue section, split conormal sequence, and tensor differential localization. Module:
`Sheaf.Paper.MaximalIdealDifferentialCotangentDimension`.

`lem-weil-pbc-regular-maximal-jacobian-presentation` records the remaining equations-and-minor
construction from 00TS/00NR and the inverse-variable step of 00TE. Its hypotheses are local
regularity at a closed point; its conclusion specifies finite polynomial equations, a quotient
isomorphism to a principal neighbourhood, and an invertible minor. Its natural-language proof
explains the independent kernel generators, denominator clearing, finite-kernel annihilation,
and both directions of the resulting algebra isomorphism. Module:
`Sheaf.Paper.RegularMaximalJacobianPresentation`.

There are no change records or forced adaptations.

## Second reading by Q1

1. **Unchanged visible statements.** Compared each delivered module with the repository version. The
original theorem signature is byte-for-byte unchanged; the two added declarations are recorded by
new DAG nodes. No target, definition, or declaration belonging to another module was changed.
Verdict: pass.

2. **Proof and axioms.** Compiled all three modules with `lcompile.py --all`. The original hole is
closed in `Algebra.smoothAtMaximalIdeal_of_finrank_differentials_le_krullDim`; the cotangent theorem
is fully proved and has only `propext`, `Classical.choice`, and `Quot.sound`. The sole remaining
`sorry` is the named split theorem
`Algebra.exists_jacobian_unit_presentation_of_regularAtMaximal`, whose docstring and node give its
source and complete proof plan. No forbidden declarations or hollow definitions occur. Verdict: pass.

3. **New statements.** Searched the library and Mathlib for duplicates and checked the edge cases
listed above, including empty equation and zero-dimensional cases. The cotangent comparison is
strictly the intermediate dimension equality used by the main proof. The Jacobian presentation
statement is strictly the equations-and-unit-minor part and does not restate smoothness or the main
target. Verdict: pass.

4. **Pruning and imports.** Recompiled after removing the thirteen old proof-only imports. The
remaining imports are used by the proofs, and the DAG `proof_deps` and `proof` fields follow the
actual route. The unit's realized route is retained; pruning only removes an unnecessary global
complete-intersection detour below the unit level. Verdict: pass.

5. **DAG and report agreement.** Checked the three node records, module/declaration names, statements,
proof origins, dependencies, and the report's closed and added holes. The new nodes have complete
source, proof-step, Lean, and blueprint metadata. Verdict: pass.

Changed only this second-reading report section; no Lean source or DAG statement required repair.
