## What changed

Proved `AlgebraicGeometry.Scheme.derivedFiberCohomology_baseChange_iso` with its
signature and existing docstring unchanged. Added proof-only imports of
`Sheaf.AlgebraicGeometry.KFlatStalkResidueCohomology`,
`Sheaf.AlgebraicGeometry.Modules.TensorPullbackStalk`,
`Mathlib.Algebra.Category.ModuleCat.Descent`, and
`Mathlib.CategoryTheory.Adjunction.Additive`. Existing public imports stay identical.
The two transparency options are scoped to this theorem.

Choose a K-flat representative of E and compute its pullback via the recorded
invertible counit. Compute both fibres using the existing K-flat stalk residue
cohomology theorem. Whisker the natural stalk pullback isomorphism with residue
extension and explicitly compose scalar-extension associativity isomorphisms using
`residue_residueFieldMap`. Lift this natural isomorphism to complexes and homology.
Flatness of the field map gives the final homology/scalar-extension comparison.
The DAG proof, proof dependencies and proof origin now record this argument.

Local compilation succeeds within the single-file limit. Edge cases require no
extra hypotheses: the zero and infinite-dimensional stalk complexes use the same
natural isomorphisms, every integer degree uses the same homology functor, and an
empty Y admits no y, so the universally quantified statement is vacuous there.
No boundedness, pseudo-coherence, global derived-category instance family, or
choice of an arbitrary unproved existence witness is introduced. The chosen
derived functor is the pre-existing one specified by its universal property.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.derivedFiberCohomology_baseChange_iso`
(node `lem-sc-derived-fiber-cohomology-base-change`).
No sorry remains in the delivered module; no new holes, declarations, definitions,
or modules were added. This is a proof from existing library declarations, not a
new decomposition. Existing dependencies can still carry sorry transitively.

## No longer needed

No original import was removed: each of the four original imports supplies the
statement or a declaration used by the proof. Each of the four added imports supplies
a proof declaration: the two geometric comparisons, the flat scalar-extension
finite-limit theorem, and additivity of left adjoints, respectively.

The original direct proof dependency
`lem-pc-module-pullback-identity-composition` is unnecessary for this item: the proof
uses stalk tensor associativity and Mathlib `ModuleCat.extendScalarsComp` instead.
Its module `Sheaf.AlgebraicGeometry.TensorPullback` remains needed for the actual
pullback functor and adjunction, so this delivery does not claim that entire module
is pruned from the targets' import closure. The other removed original direct proof dependency is
`def-sc-derived-fiber-betti`: its definition remains a statement dependency, and
`Sheaf.AlgebraicGeometry.DerivedFiberBetti` remains publicly imported. Its fibre
computation is now delegated to `lem-sc-kflat-stalk-residue-cohomology`, rather than
performed directly in this proof. No additional node or module can be claimed
globally unreachable from this local change.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The planned residue-square/composite-pullback route is
longer than necessary: existing K-flat stalk residue cohomology and natural stalk
pullback statements supply the geometric comparisons. The unit
`sk-prop-av-cube` has no realized nodes for this helper; its cube statement and proof
route are unchanged. The node `lem-weil-pbc-module-stalk-pullback` is used as a
shared tool for the natural stalk tensor comparison; the item's unit supplies no
alternative stalk comparison.

Searches were run through msearch.py using LeanFinder, LeanSearch, Loogle and grep.
LeanSearch returned Internal Server Error and is recorded unavailable. LeanFinder
found residue-field pullback geometry but no whole fibre-cohomology theorem;
Loogle found scalar-extension associativity and the adjunction. Repository searches
located the two existing stalk comparison modules used in the proof.
No forced adaptation or change record is needed.


## Second reading by D2

1. Interface preservation: PASS. Compared the complete delivered module against
   the repository with diff and checked the theorem signature byte for byte.
   Its hypotheses, conclusion, docstring and public imports are unchanged. The
   only Lean changes are the proof, four proof-only imports and two theorem-scoped
   elaboration options. No definition or declaration was added or adapted.
2. Proof and axioms: PASS. Independently compiled the delivered module using
   lcompile.py without errors or warnings (11.3 seconds). Compiled a scratch copy
   with `#print axioms AlgebraicGeometry.Scheme.derivedFiberCohomology_baseChange_iso`:
   exactly `propext`, `Classical.choice`, `Quot.sound` and inherited `sorryAx`.
   There is no direct sorry or forbidden declaration in this module. The K-flat
   representative and stalk isomorphisms are local proof witnesses; no arbitrary
   witness is installed as definition data. The existing derived functor is
   specified up to canonical isomorphism by its left-derived universal property.
3. Split statements: PASS, vacuous. No new statement, module, node or sorry was
   split off. Read the existing K-flat resolution, K-flat pullback preservation,
   fibre/stalk comparison, natural tensor-pullback stalk comparison and chosen
   derived-pullback specification used by the proof. The comparison applies to
   zero complexes, arbitrary vector-space dimensions and every integer degree;
   no flatness of the residue map or boundedness hypothesis is silently required.
4. Route and pruning: PASS after report correction. Checked Mathlib's
   extendScalarsComp and ShortComplex.mapHomologyIso against the compositions in
   the proof. An independent Loogle query for ShortComplex.mapHomologyIso did not
   resolve that short identifier; direct Mathlib reading verified the theorem.
   Repository searches found no alternative complete fibre comparison. The
   retained imports each provide a used declaration or statement interface.
   The unit sk-prop-av-cube has empty realized statement and step lists; this
   helper comparison changes none of its statement or route. The report now
   accounts for both removed original direct proof dependencies and explicitly
   distinguishes them from globally pruned modules (none).
5. Node agreement: PASS. The existing node changes only proof, proof_deps and
   proof_origin. Verified all six dependencies against their Lean records and
   verified proof_deps equals the union of the steps' uses. The steps follow the
   actual resolution, counit, stalk-tensor and exact homology comparison. No new
   node or change record is required.

Second-reading changes: corrected the omitted pruning explanation for
`def-sc-derived-fiber-betti`, replaced trial-import history with the purpose of the
retained imports, and added this independent review. The Lean proof and node were
left unchanged.
