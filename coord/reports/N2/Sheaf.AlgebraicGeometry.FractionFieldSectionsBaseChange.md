## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_fractionField_sections_baseChange`
in `Sheaf.AlgebraicGeometry.FractionFieldSectionsBaseChange`, preserving its statement,
universe, hypotheses and public imports. Added proof-only imports of
`Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologySeparated` and
`Mathlib.RingTheory.Flat.Localization`.

The equivalence tensors the inverse of the existing H-zero/sections equivalence,
composes with the canonical flat cohomology comparison, then applies H-zero/sections
on the base change. Fraction-field flatness is Mathlib `IsLocalization.flat`.
The private, fully proved `zero_inverseImage` helper derives the normalization from
Ext in degree zero, the constant-sheaf adjunction and uniqueness of left adjoints.
The coefficient adjunction then gives exactly the module-unit section in the statement.
No data is chosen from a mere existence theorem.

Updated the node's proof, proof_deps and proof_origin to describe this route.
The unit `sk-prop-av-cube` has no realized node attachment here; its cube route is preserved.
No statement, definition, visibility or other module was changed.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.Modules.exists_fractionField_sections_baseChange`
(node `lem-sc-fraction-field-sections-base-change`).

Added 0 holes and split off 0 statements. No sorry remains in the delivered module.
The private helper `AlgebraicGeometry.Scheme.Modules.zero_inverseImage` is proved.
This is a proof from existing library declarations, not a decomposition into new holes.
The theorem still depends transitively on the existing flat-cohomology base-change
infrastructure; this report does not claim that its entire axiom closure is sorry-free.

## No longer needed

No existing import was removed: all original public imports support the unchanged
statement and remain public. Only the two necessary proof imports were added.

Pruned direct proof dependencies:
- `lem-pc-cech-inverse-image-degree-zero`, module
  `Sheaf.AlgebraicGeometry.Cohomology.CechInverseImageDegreeZero`: not imported or
  used for this theorem's normalization; proved directly from the adjunctions instead.
- `pqf-def-cohomology`, module `Sheaf.Paper.PQFCohomology`: not imported or used;
  its derived-direct-image/delta-functor theorem is unnecessary. The proved source
  `H.zeroLinearEquiv` is already available through FlatCohomologyComparison.

These are local dependency removals, not claims of global unreachability: other
modules, including the retained flat-cohomology infrastructure, may still use them.
No retained proof-dependency import is unused.

## Where the brief, the DAG or earlier work was wrong

The original proof plan associated the H-zero/sections identification with
`pqf-def-cohomology`, whose Lean declaration instead describes derived module
cohomology and higher direct images. The needed equivalence is the already proved
source declaration `H.zeroLinearEquiv`.

The planned Cech degree-zero normalization is not needed here. Unfolding the exact
inverse-image comparison and the constant-sheaf isomorphism makes its normalization
an adjunction calculation, implemented and compiled in the private helper.

## Second reading by N2

1. **Interface preservation — pass.** Read the full repository/sandbox module diff.
   The existing theorem signature, including its let-bound scalar restrictions,
   is byte-for-byte identical. All original public imports, visibility, universe
   declarations and options remain unchanged. The only additions are two plain
   proof imports, a private proved helper and the replacement of the original sorry.
   There are no adapted modules, new definitions or interface change records.
2. **Proof and axioms — pass.** Independently compiled the delivered module with
   lcompile.py: no errors or warnings (18.5 seconds). Scanned for sorry and forbidden
   declarations: none. Compiled a scratch copy with #print axioms for both declarations
   (20.4 seconds): zero_inverseImage uses only propext, Classical.choice and Quot.sound;
   exists_fractionField_sections_baseChange additionally uses sorryAx through existing
   flat-cohomology infrastructure. The equivalence is constructed from specified maps
   and their inverses; ofBijective determines the inverse uniquely. No arbitrary data
   witness of an unproved existence statement is selected.
3. **Split statements and reuse — pass.** No split-off statements or new holes exist.
   Checked the private helper by following Ext-zero conversion, uniqueness of left
   adjoints, unit naturality and evaluation at 1. Its formula and the final theorem
   include empty schemes and zero modules without nonemptiness assumptions. Searched
   Lean sources for equiv-zero/mapFunctor and zeroLinearEquiv/baseChange combinations;
   Loogle search for Sheaf.H.equiv₀ returned the equivalence and its two naturality
   lemmas, already used here. CechInverseImageDegreeZero contains a similar private
   ext_zero_sections helper, unavailable to this module; its public theorem requires
   cover/cochain infrastructure and offers no shorter direct section calculation.
4. **Route and pruning — pass.** Read FlatCohomologySeparated and
   FlatCohomologyComparison, and checked H.zeroLinearEquiv in the source library.
   The proof specializes the existing canonical comparison to degree zero and proves
   the normalization, rather than introducing a restatement hole. Both added imports
   are proof-only: FlatCohomologySeparated supplies bijectivity and the comparison;
   removing Flat.Localization in a scratch copy fails with unknown IsLocalization.flat.
   The two removed old proof dependencies are both listed under No longer needed.
   No original import is removed and no global unreachability is claimed. Inspected
   dag/units/sk-prop-av-cube.json: its realized statement and step lists are empty;
   this local reduction does not change or bypass its prescribed cube route.
5. **DAG correspondence — pass.** Compared node JSON objects: only proof,
   proof_deps and proof_origin differ. Each proof step matches the actual equivalence
   construction or adjunction calculation, and proof_deps is exactly the union of
   step uses. Both retained nodes' Lean declarations match the imports and applications.
   No new nodes require validation.

Second-reading changes: appended this independent review and its verification evidence.
No repair to the Lean proof or DAG was necessary. One original hole is closed and zero
holes are added; the remaining transitive holes are not claimed as closed.
