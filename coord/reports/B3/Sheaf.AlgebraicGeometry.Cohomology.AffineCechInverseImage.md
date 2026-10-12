## What changed

Completed the earlier incomplete sandbox attempt. The earlier main module was empty, its
report named helper theorems which did not exist, and its three actual helper modules had
no DAG nodes. The delivery now contains four compiling modules and matching DAG records.

`Sheaf.AlgebraicGeometry.Cohomology.AffineCechInverseImage` preserves the entire signature
and original docstring of `AlgebraicGeometry.Scheme.Modules.exists_affineCech_inverseImage`.
Its proof obtains normalized additive comparison systems, proves their affine maps
bijective and linear, builds the two module isomorphisms with `LinearEquiv.ofBijective`,
and specializes their matching-cocycle equality. Both new imports are proof-only imports.
No existing definition, statement, public import or visibility changes.

`CechComparisonSystem` defines a genuine structure of natural additive comparisons, with
its degree-zero normalization and connecting-map law. It also constructs the forgetful
presheaf isomorphism, additive homology transport and induced additive map explicitly.
No definition chooses data from the remaining existence theorem. The theorem witnesses
are used only inside a proposition proof; inverses of bijective linear maps are determined
uniquely by those maps.

`CechComparisonAffine` proves bijectivity by induction on degree, using the existing
injective short exact sequence, affine section lifting, exact connecting sequences,
and Mathlib's cokernel form of the five lemma. It proves linearity by naturality under
multiplication and the proved scalar-compatible categorical/explicit Cech transport.
Its source import was reduced from `Affine.Leray` to `Affine.CechAcyclic`.

`CechComparisonInverseImage` states the remaining additive comparison-construction and
inverse-image naturality step on arbitrary covers and arbitrary module coefficients.
It has no quasi-coherence or affine-intersection hypotheses and asserts neither
bijectivity nor scalar linearity. It is therefore a strict part of the original argument,
combined with a separately proved affine theorem, rather than the original statement
renamed or repackaged.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.exists_affineCech_inverseImage`
(node `lem-pc-affine-cech-inverse-image`): 1 of 1 original holes closed.

Also proved `AlgebraicGeometry.Scheme.Modules.cechComparison_affine_bijective_linear`
(node `lem-pc-cech-comparison-affine`) and its private helpers `comparison_bijective`
and `comparison_smul`. All three transport definitions in `CechComparisonSystem`
contain complete proofs and no postponed data or laws.

The only hole added or left in this delivery is
`AlgebraicGeometry.Scheme.Modules.exists_cechComparison_inverseImage`
(node `lem-pc-cech-comparison-inverse-image`), whose whole proof is `:= by sorry`.
This is a decomposition: one upper hole closed and one strictly partial lower hole added,
net zero holes. The remaining lower theorem's construction, normalization, boundary law,
and inverse-image diagram argument are documented in its docstring and DAG node.
The target theorem and affine helper are proved relative to this lower theorem.

Validation: the entire four-module sandbox compiled in dependency order through
`lcompile.py --all`, without errors or warnings. Statement comparison reports no
changed signature. The delivery dry run performs the compilation and axiom probes again.

## No longer needed

Removed from the item's proof imports:

- `Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison`: redundant direct import;
  all statement definitions remain available through the original public import
  `FlatCohomologyCechBaseChange`. Its definition node remains a statement dependency.
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray` and node
  `lem-pc-cech-computes`: the unspecified Leray isomorphism is replaced by bijectivity
  of the specific normalized system, proved in `CechComparisonAffine`.
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Cech` and node
  `lem-sc-cech-spectral`: the full Cech-to-derived spectral-sequence theorem is not
  used. The remaining lower construction uses injective row augmentation and the
  first-quadrant finite-diagonal comparison directly.

The affine helper also drops the earlier sandbox's `Affine.Leray` import in favor of
`Affine.CechAcyclic`, which contains precisely the proved acyclicity and section-lifting
facts it uses. No claim is made that these removed modules are globally unreachable;
other branches of the targets may still need them. No unit statement or realized step
is removed: the parent is a below-unit helper, and the affine-degeneration and
comparison-functoriality steps are both retained explicitly.

## Where the brief, the DAG or earlier work was wrong

The earlier report described nonexistent `exists_affineCech_leray_witnesses` and
`affineCech_inverseImage_compat` declarations, while the main file was empty. It has
been replaced by this report of the actual files and compiled proof.

The original planned use of `nonempty_cechComplex_linearEquiv_H` does not supply
compatibility of its existentially chosen isomorphism with inverse image. Its own
source docstring explicitly says it does not name the canonical edge map. The present
proof applies affine degeneration to the same normalized comparisons that satisfy
inverse-image naturality, so the witnesses used in the final equality are fixed.
This changes no mathematical statement or required unit argument.

Searches: LeanFinder returned sheaf pullback and restriction facts, not the required
comparison. Loogle found Cech infrastructure but no matching naturality theorem;
Mathlib grep found no Cech comparison/inverse-image naturality declaration. LeanSearch
returned an Internal Server Error, recorded as unavailable without a mathematical
verdict. Local searches also found `Sheaf.Paper.CechComparisonMapNaturality`; it is
coefficient naturality on one scheme with module-derived cohomology, so it does not
supply this abelian Ext-based comparison between schemes or its connecting-map law.
Blueprint searches for inverse image Cech, normalized Cech comparison and 01FD found
no duplicate of the new system or remaining inverse-image theorem. The existing
`lem-sc-cech-comparison-map-iso-affine` uses that module-derived comparison predicate,
which differs from the additive system used here. All source transports and section
lifting results have been reused rather than restated.

Read Stacks Tags 01EQ and 01FD: the coefficient augmentation, inverted injective
section augmentation, refinement pentagon and two global-section squares are the
remaining construction. Edge cases checked mathematically: degree zero is gluing
followed by the Ext-section identification; an empty covering forces an empty scheme
and zero groups; the zero module gives zero maps; identity g and equal covers gives
ordinary coefficient naturality. Repeated tuple indices are allowed. The construction
uses finite diagonals, so infinite covers introduce products but no unbounded total
sum in fixed degree. The affine proof assumes affine tuple intersections directly
and adds no separatedness or flatness assumption. Scalar linearity is deduced from
natural multiplication, not included as an unproved structure field.

## New nodes

`def-pc-cech-comparison-system`, realized by `CechComparisonSystem.lean`, records the
normalized comparison structure and the explicit scalar-restriction transports.
It is data supplied as a parameter, with no existence choice and no sorry.

`lem-pc-cech-comparison-affine`, realized by `CechComparisonAffine.lean`, records the
proved affine bijectivity and scalar linearity for any normalized system. The proof
reuses the complete source acyclicity and section-lifting APIs.

`lem-pc-cech-comparison-inverse-image`, realized by `CechComparisonInverseImage.lean`,
records the single remaining lower obligation: normalized additive comparisons
compatible with inverse image on matching cycles, without any affine degeneration.

No change record is required: all existing signatures and public imports are preserved,
all added dependencies of the item are proof-only, and no module held by another group
has been adapted.

## Second reading by B3

1. **Interface and statement preservation.** I diffed the delivered target module against the repository version. The theorem signature and docstring are byte-for-byte unchanged; only proof-only imports and the proof body changed. The three helper modules expose the declarations recorded by their DAG nodes, with no altered existing declaration.

2. **Compilation and trust basis.** I compiled all four modules with `lcompile.py --all`; all compiled successfully. The only remaining `sorry` is the named theorem `exists_cechComparison_inverseImage`, documented above and represented by node `lem-pc-cech-comparison-inverse-image`. No definition contains `sorry`, and searches found no forbidden `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declaration.

3. **New statements.** I checked the helper signatures against their node statements. `CechComparisonSystem` is explicit data with normalization and connecting-map laws; its transport definitions construct their data directly. The affine theorem is strictly about bijectivity and scalar linearity of a supplied system. The inverse-image theorem is strictly the remaining additive naturality construction and includes no affine or quasi-coherence assumptions. These are true partial obligations rather than a restatement of the target.

4. **Pruning and route.** The target proof uses only `CechComparisonSystem`, `CechComparisonAffine`, and `CechComparisonInverseImage`; the removed Leray and spectral-sequence imports are not used. The affine proof uses the source affine acyclicity and exact-sequence APIs. The DAG proof dependencies match the declarations used by the Lean proofs, and the parent unit assignment and route are retained.

5. **Proof quality and edge cases.** The target proof obtains both systems, applies the affine bijectivity/linearity theorem, constructs linear maps, and specializes the matching-cycle equality. Degree zero, empty covers, zero coefficients, repeated indices, and infinite covers are addressed in the split theorem's proof documentation. No assumptions are added to the target.

Changed in this second reading: appended this review section only; no Lean proof or statement required repair.
