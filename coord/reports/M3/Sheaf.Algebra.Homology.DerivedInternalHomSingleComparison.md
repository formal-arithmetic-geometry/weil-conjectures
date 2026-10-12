## What changed

Replaced the sorry in `CategoryTheory.derivedInternalHom_single_comparison` by a complete
Lean proof from the natural chain-level comparison
`CategoryTheory.homComplex_single_natIso`, the existing
`CategoryTheory.derivedInternalHom_comparison`, and
`CategoryTheory.quasiIso_homComplex_map`. The proof uses the source library's functorial
K-injective resolution and Mathlib's K-injective derivability criterion. It constructs the
comparison after precomposition with Q, then descends it with `Localization.liftNatIso`.
All existing theorem signatures and docstrings are unchanged.

Added `Sheaf.Algebra.Homology.HomComplexSingleNatural`, a statement solely about functors
on complexes, with a complete product-projection proof in its docstring. It isolates
naturality of the single-source comparison; it has no derived category, S, delta, or
right-derived-functor hypothesis. The final theorem does substantial additional work:
inversion on K-injectives, computation of the given derived functor, specialization of
bifunctorial RHom, composition, and localization.

## Proved and sorry left

Closed the original hole in `CategoryTheory.derivedInternalHom_single_comparison`
(node `lem-sc-derived-internal-hom-single-comparison`). Its module has no sorry left.

Added one hole: `CategoryTheory.homComplex_single_natIso`
(node `lem-sc-hom-complex-single-natural`). This is a decomposition, not a net reduction
in the number of holes: one upper hole closed and one strictly smaller lower hole added.
The other existing dependencies retain their own proof status; none was edited.

Both delivered modules compile in import order through lcompile.py. The remaining
statement includes zero P, zero coefficients, the empty scheme, and unbounded complexes:
its product projection and insertion argument uses neither exactness of products nor
local freeness. The parent statement retains the arbitrary derived-category universe.

## No longer needed

Removed the proof imports `Sheaf.AlgebraicGeometry.HomComplexSingle` and
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions` from the item's module.
The proof no longer uses nodes `lem-sc-hom-complex-single` or
`prop-pur-kinjective-resolutions-exist` as separate statements. The new natural comparison
uses the product, differential, and map formulas in `def-pur-hom-complex` directly.
The source resolution constructors already exposed by DerivedInternalHom supply precisely
K-injectivity and the quasi-isomorphism; the generator and degreewise-injectivity clauses
of RingedSiteKInjectiveResolutions are unnecessary here.

No claim is made that these modules disappear from the whole targets' import closure:
other users or transitive imports can still reach them. No public import was changed.

## Where the brief, the DAG or earlier work was wrong

The objectwise theorem `AlgebraicGeometry.homComplex_single_iso` does not state naturality.
Its existence-only statement cannot supply canonical projection components, so applying
it objectwise does not establish a natural isomorphism. The remaining step is explicitly
stated as a natural functor isomorphism, with its projection construction and map-formula
proof. Attempts to extend the existing construction in Lean repeatedly encountered
costly dependent conversions between P[0].X 0 and P; the attempted code is preserved
in the sandbox scratchpad, not delivered as an unfinished proof.

For the successfully compiled parent proof, defining the fixed derived source literally
as Q(P[0]) avoids a similarly costly conversion during the naturality check; it is
definitionally the original derived single source, so the theorem's signature is unchanged.

The blueprint ancestor utility returns None because the existing node's created.item
names a Lean module rather than a DAG node. The new node inherits the existing item's
explicit blueprint ancestor `lem-sc-finite-duality` and its precise affine sheaf-Hom place.
Blueprint searches for Hom complex and internal Hom found no equivalent natural
single-source statement. The unit record's realized arrays are empty; no unit statement
or realized proof step was bypassed.

## New nodes

`lem-sc-hom-complex-single-natural`, in sec-picard-framework, is the natural chain-level
identification between the single-source Hom-complex functor and degreewise internal Hom.
It serves the affine sheaf-Hom identification in `lem-sc-finite-duality`, through the
existing item's blueprint chain. Its source is Stacks Section 0A8X. The module is
`Sheaf.Algebra.Homology.HomComplexSingleNatural`; the sole remaining declaration is
`CategoryTheory.homComplex_single_natIso`. LeanSearch was unavailable and recorded as such;
LeanFinder, Loogle, and grep supplied no exact sheaf-valued natural comparison.
No definition or statement was changed, and no change record is required.

## Second reading by M3

1. **Signatures and accidental changes.** I compared `DerivedInternalHomSingleComparison.lean` against the repository version. The existing declaration `CategoryTheory.derivedInternalHom_single_comparison` has the same signature and docstring. The delivery adds only the separately named declaration `CategoryTheory.homComplex_single_natIso` in `HomComplexSingleNatural.lean`; no existing declaration or target statement was altered.

2. **Proof and trust basis.** Both delivered modules compile with `python3 /home/ubuntu/weil-launcher/lcompile.py --all ...`. The parent proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`; the only remaining `sorry` is the named split-off theorem `homComplex_single_natIso`, whose node and source-backed proof plan are recorded. The parent uses the K-injective derivability criterion, the quasi-isomorphism of the Hom-complex map, the derived internal-Hom comparison, and localization descent, with no hollow definition.

3. **Split-off statement.** `homComplex_single_natIso` is strictly smaller than the parent: it concerns only the chain-level natural comparison on all complexes, with no derived category, localization, or right-derived-functor hypotheses. Its statement is true in edge cases including zero coefficients, the empty scheme, and unbounded complexes, and is not duplicated by `homComplex_single_iso`, which is only objectwise. Its named node `lem-sc-hom-complex-single-natural` has the required source, proof steps, dependencies, Lean record, and blueprint ancestry.

4. **Pruning and route.** The parent proof uses `HomComplexSingleNatural`, `HomComplex`, and `QuasiIsoHomComplexMap`, together with the existing derived-internal-Hom and derivability declarations. The former objectwise `HomComplexSingle` and K-injective-resolution imports are no longer needed by this proof and were removed as proof-only imports. The unit route is retained: the parent node still realizes the unit's affine sheaf-Hom comparison route, and the split-off node is an intermediate chain-level step rather than a bypass of the unit.

5. **DAG agreement.** The parent node's proof and `proof_deps` name the naturality node and the existing derived internal-Hom dependencies used by the Lean proof. The new node's declaration, statement, source, proof steps, `proof_deps`, `proof_origin`, chapter, unit, and blueprint ancestry agree with `HomComplexSingleNatural.lean`. No change record is required because no existing definition or statement changed.

I changed only the proof imports and proof body of the parent module, added the chain-level split-off module and node, and added this second-reading report section. No further repairs were needed.
