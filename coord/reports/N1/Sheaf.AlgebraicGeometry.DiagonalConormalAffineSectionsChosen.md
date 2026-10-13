## What changed

Proved `AlgebraicGeometry.diagonalConormalDerivation_ext` by extensionality on every
open and `AlgebraicGeometry.diagonalConormal_affine_sections_unique`. Added its module
as a proof-only import. Existing declaration signatures are byte for byte unchanged.
Removed three unnecessary imports, recorded in
`coord/changes/DiagonalConormalAffineSectionsChosen-imports.md`. Updated the uniqueness
node's proof, proof_deps and proof_origin to the actual sectionwise route. Expanded the
remaining affine theorem's docstring into its complete natural-language argument.

## Proved and sorry left

Closed: `AlgebraicGeometry.diagonalConormalDerivation_ext`
(node `stage3-diagonal-conormal-uniqueness`). Its axiom check shows only `propext`,
`Classical.choice`, and `Quot.sound`; the imported sectionwise uniqueness theorem also
has exactly those allowed axioms. Proved 1 of the 2 original holes.

Unchanged hole: `AlgebraicGeometry.exists_affine_sections_for_chosen_derivation`
(node `stage3-diagonal-conormal-chosen`). Its axiom check includes `sorryAx`.
Added holes: none. Split-off declarations: none. Net holes closed: one, not a decomposition.

## No longer needed

Removed imports: `Sheaf.AlgebraicGeometry.AffineConormalSections`,
`Sheaf.AlgebraicGeometry.BaseChangeConventions`, and
`Sheaf.AlgebraicGeometry.DiagonalConormal`. The last remains publicly reachable through
`DiagonalConormalDerivation`; none of the removed imports is used by the delivered proof
or needed to elaborate its signatures. The retained public Derivation import supplies
all signature notions; the new Unique import is needed only by the proof.

Removed from the uniqueness node's old proof_deps: `def-sc-diagonal-conormal` and
`lem-sc-diagonal-conormal-derivation-exists`. Their definitions remain statement
dependencies, and the latter is still a proof dependency of the unclosed chosen node.
The proof now depends on `lem-sc-diagonal-conormal-affine-sections-unique`.
No claim that these removed imports become unreachable throughout the library:
the original direct importer still imports them itself.

## Where the brief, the DAG or earlier work was wrong

The uniqueness node's old plan called for a new affine comparison even though the
existing sectionwise theorem covers every open and is already proved. The first worker's
Lean proof used that theorem correctly but omitted the DAG update and import pruning.
The existing affine-hole docstring named a calculation without spelling out its proof;
the second reader supplied the argument without altering the theorem or adding a hole.

Further search: rg on the project's diagonal/conormal modules and the compiled-library
Mathlib/upstream source found no independent affine-diagonal comparison suitable for
closing the remaining hole. The scheme-level affine comparison and differential-isomorphism
modules depend on this item, so using them would be circular. A fresh LeanFinder query
about affine diagonal conormal sections returned ring-level tools including
`KaehlerDifferential.endEquivDerivation'`, `tensorKaehlerQuotKerSqEquiv`, and
`Derivation.liftKaehlerDifferential_apply`, but no theorem supplying the missing geometric
restriction and kernel/tensor-pullback identifications. An initial Loogle query using two
quoted names was rejected by the query parser; it is not counted as a no-match search.

## Second reading by N1

1. Compared the complete repository and sandbox modules with diff and compared the raw
   theorem headers through `:=`: both existing signatures are byte for byte identical.
   No definitions or declarations were added or removed. Public-import pruning is explicit
   in the change record. Its users table lists the read-only downstream scan (295 modules).
   The only direct importer, `DiagonalConormalAffineSectionsBase`, imports this module
   proof-only and already imports the removed modules explicitly. Verdict: no accidental
   statement or definition change and no target meaning change.

2. Compiled the delivered module cleanly with lcompile.py. Compiled a scratch copy with
   #print axioms for both declarations and the imported sectionwise uniqueness theorem:
   extensionality and its dependency use only the three permitted axioms; the unchanged
   affine theorem additionally uses sorryAx. The original direct importer compiles against
   the changed module in the same scratch import-order compile. The only sorry in the
   delivered Lean is the existing named affine theorem. No forbidden declarations or
   hollow definitions. The theorem-local chosen derivation is determined uniquely by
   its normalization, now established by the proved extensionality theorem; no arbitrary
   witness is introduced in a definition. Verdict: valid proof, one documented old hole.

3. No statements were split off and no new nodes were added. Read the imported theorem
   and its kernel-section construction: for W = p₁⁻¹(U) ∩ p₂⁻¹(U), the difference of
   the projection pullbacks is killed by the diagonal. The actual kernel section gives
   the same normalized value for both derivations. The argument covers the empty open,
   empty schemes, f = id, arbitrary characteristics, and nonseparated morphisms; W is
   not assumed affine. The chosen affine equivalence agrees with the affine calculation
   in [Stacks 08S2](https://stacks.math.columbia.edu/tag/08S2), using the conormal quotient
   of [01R3](https://stacks.math.columbia.edu/tag/01R3) and the diagonal charts of
   [01KJ](https://stacks.math.columbia.edu/tag/01KJ). The zero ring causes no exception.
   Verdict: no new statement or restatement; the remaining hole is mathematically valid.

4. The proof takes the existing proved all-open uniqueness result and elementary
   derivation extensionality, with no new geometric argument. It needs just one new
   proof-only import; removed unused imports and reported every superseded proof_dep.
   Read `dag/units/sk-thm-picard-duality.json`: neither item node realizes a unit statement
   or step (the realized lists are empty), and both uniqueness nodes are in this same
   unit. No unit proof step is bypassed or changed. Verdict: short route and pruned imports.

5. Updated `stage3-diagonal-conormal-uniqueness.json`: its sole elementary step now cites
   the actual all-open uniqueness node and explains extensionality; proof_deps is exactly
   that uses union and proof_origin describes this route. The chosen node and its statement
   remain unchanged because that theorem is still open. No new node fields to check.
   Verdict: delivered DAG agrees with the Lean proof.

Second reading changed: unused imports, the uniqueness node's proof metadata, the residual
hole's proof docstring, and this report/change record. The first worker's correct proof
was retained unchanged.
