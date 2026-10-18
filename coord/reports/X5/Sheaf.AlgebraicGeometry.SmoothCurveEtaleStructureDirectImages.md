## What changed

The item keeps every existing declaration signature and definition unchanged. Its theorem
uses the concrete module E = (Scheme.Modules.higherDirectImage f 1).obj O_X.
The proof supplies the canonical degree-zero isomorphism, finite local freeness of E,
explicit normalized local scalar endomorphisms, and the sheafification/class calculation.
The raw coherent comparison is isolated in the new module
Sheaf.AlgebraicGeometry.CoherentEtaleRawDirectImageComparison.

The finite-local-freeness proof takes a finite-free residue model in degrees zero and one.
Its degree-zero term has rank one, as does H0. The existing bottom-differential theorem
makes its differential zero without assuming the base reduced. Exact restriction and
homology comparisons identify H1 with the degree-one free module. Fibre bounds use
proper-flat derived base change and Noetherian dimension vanishing. Restriction
sheafification instances are cached locally to prevent repeated expensive typeclass searches;
tensor and derived pullbacks are locally irreducible during the geometric application.
Complexes and module objects have explicit carrier types. Fibre nonnegativity uses the
proved source right-derived-single lemma directly, avoiding the larger structure-unit package.
The final sheafification calculation is factored through a proved lemma for abstract
presheaves; the class map is kept irreducible during the concrete specialization.
The class calculation is performed in the final proof to avoid a second kernel check
of the same dependent comparison statement. These are proof-local changes, with no
shared definition or interface repair.

The parent node's proof, proof_deps and proof_origin now describe this route.
The proof-local command changes are documented in
coord/changes/X5-smooth-curve-proof-local-settings.md, as required by the conservative
interface check. There are seven untouched downstream importers and no downstream textual
user of the theorem; the record lists the consumer check. Obsolete
entries are removed from its tool_uses list without adding or reordering approvals.
No unit statement or unit proof step is bypassed. No other existing module is adapted.

New direct tools, in place of the old unbounded combined theorem, are
lem-pc-proper-flat-single-derived-direct-image-perfect and
lem-pc-rf-base-change-flat-module. The finite-free step uses the existing
lem-sc-finite-free-bottom-differential-zero together with the residue-model node.
They provide the general derived and algebraic inputs that the proper-base-change
unit's curve argument needs; they do not replace the unit's own statement or steps.
The new comparison node likewise uses the existing normalized flat-base-change
resolution map and its invertibility, rather than an arbitrary isomorphism.
The existing src-right-derived-functor-plus-compatibility node records the proved
source interface also used for negative-degree vanishing. Their proof dependencies
are recorded, with no worker-added tool approvals.

## Proved and sorry left

Original item: one hole in
AlgebraicGeometry.Etale.smooth_curve_etale_structure_direct_images.
Its body is replaced by a complete proof from named dependencies and the new comparison.
The item's module has zero remaining sorry declarations.

Added: one hole in
AlgebraicGeometry.Etale.exists_coherent_etale_raw_direct_image_comparison,
node lem-weil-pbc-coherent-etale-raw-direct-image-comparison, in the new module above.
Its entire proof is exactly `by sorry`; its docstring and node carry the source and proof.
Thus this delivery is a decomposition of one upper hole into one strictly smaller
comparison obligation, not a net proof of the original target closure. No hole is placed
inside a definition, an anonymous declaration, or a private helper.

Completed private helpers: exists_curveLocalScalar,
isIso_appTop_of_structure_unit, smooth_curve_etale_structure_hzero,
perfect_curve_homology_one_locally_free, smooth_curve_structure_first_locally_free,
and sheafified_raw_iso. Existing imported theorems may themselves remain unfinished;
their existing nodes supply those obligations, as the stage-3 brief intends.

Validation: the complete item compiled cleanly remotely in 58.1 seconds. The delivery
dry run passed sandbox compilation in import order, axiom probes and preflight, including
signatures, node consistency and imports. All original definitions, the abbreviation and
the theorem signature were compared with the shared repository and are byte-identical.

## No longer needed

Removed direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.FlatDerivedStructureUnit`
- `Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap`
- `Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap`
- `Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf`
- `Mathlib.AlgebraicGeometry.Sites.Etale`
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMap`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded`
- `Sheaf.AlgebraicGeometry.GlobalSectionsGeomConnected`
- `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`
- `Sheaf.AlgebraicGeometry.TensorPullback`
- `Sheaf.AlgebraicGeometry.DerivedAdjoint`
- `Sheaf.AlgebraicGeometry.EtaleQuasiCoherentDescent`
- `Sheaf.AlgebraicGeometry.PerfectDegreeZeroFibreCriterion`
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial`
- `Sheaf.AlgebraicGeometry.QcoherentCohomologyComparisonPullback`
- `Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing`
- `Sheaf.AlgebraicGeometry.LeraySpectralSequence`
- `Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectBaseChange`
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap`
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial`
- `WeilConjectures.AlgebraicGeometry.TensorPullback`
- `WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction`
- `Sheaf.AlgebraicGeometry.DerivedBaseChangeHorizontalPasting`

The general degree-zero splitting of a perfect complex is unnecessary here: canonical
H0 is already a line bundle, and the rank-one bottom-differential theorem suffices.
The unbounded derived-adjunction, direct-image-composition, horizontal-pasting and
derived-to-ordinary base-change-map interfaces are not used by this Lean proof.
Etale quasi-coherent descent is replaced by sheafification into the already constructed
etale tensor-section sheaf. An arbitrary module witness or module action is never chosen.

The flat-derived structure-unit package is unnecessary: negative fibre cohomology
vanishes by the proved source nonnegativity lemma and the existing fibre isomorphism.

The comparison-specific quasi-coherent pullback comparison, affine-open basis and tensor
pullback composition are retained in the new comparison node's proof plan, not claimed
as globally pruned. Proper-flat global sections still uses geometric connectedness and
its own supporting nodes transitively. Definitions needed by the unchanged public
statement remain statement dependencies. Removing a direct import does not assert that
no other target or transitive source module imports it.

Removed parent proof-dependency entries:

- `lem-sc-flat-derived-structure-unit`

- `def-kun-topological-krull-dimension`
- `def-pc-derived-base-change-map`
- `def-pc-derived-module-base-change-map`
- `def-sc-etale-qcoherent-module`
- `def-weil-pbc-etale-site`
- `def-weil-pbc-module-cohomology-fmap`
- `def-weil-pbc-scheme-conventions`
- `def-weil-proper-morphism`
- `def-weil-sheaf-of-modules-category`
- `lem-pc-derived-base-change-horizontal-pasting`
- `lem-pc-derived-direct-image-composition`
- `lem-pc-h0-geom-connected`
- `lem-pc-module-pullback-adjunction`
- `lem-pc-module-pullback-identity-composition`
- `lem-pc-rf-perfect-base-change`
- `lem-pc-ringed-spaces-derived-adjoint`
- `lem-pc-smooth-flat`
- `lem-sc-etale-qcoherent-descent`
- `lem-sc-perfect-degree-zero-fibre-criterion`
- `lem-weil-pbc-affine-opens-basis`
- `lem-weil-pbc-module-cohomology-fmap-functorial`
- `lem-weil-pbc-proper-fp-permanence`
- `lem-weil-pbc-qcoherent-cohomology-comparison-pullback`
- `pqf-lem-affine-vanishing`
- `pqf-lem-leray`
- `sbc-lem-higher-direct-image-presheaf`
- `sbc-lem-smooth-geometrically-reduced`

Removed obsolete parent tool approvals (remaining entries retain their original order):

- `lem-sc-flat-derived-structure-unit`

- `lem-pc-derived-direct-image-composition`
- `lem-pc-h0-geom-connected`
- `lem-pc-module-pullback-adjunction`
- `lem-pc-module-pullback-identity-composition`
- `lem-pc-rf-perfect-base-change`
- `lem-pc-ringed-spaces-derived-adjoint`
- `lem-pc-smooth-flat`
- `lem-sc-etale-qcoherent-descent`
- `lem-sc-perfect-degree-zero-fibre-criterion`
- `lem-weil-pbc-affine-opens-basis`
- `lem-weil-pbc-proper-fp-permanence`
- `pqf-lem-affine-vanishing`
- `pqf-lem-leray`
- `sbc-lem-higher-direct-image-presheaf`
- `sbc-lem-smooth-geometrically-reduced`
- `lem-pc-derived-base-change-horizontal-pasting`

## Where the brief, the DAG or earlier work was wrong

The original plan's lem-pc-rf-perfect-base-change is now attached to the source library's
Cech/perfect-complex interface, rather than a declaration of precisely the full unbounded
perfect-direct-image/base-change conjunction used in its prose. The proof therefore uses
the separately stated proper-flat single-object perfectness and relatively-flat derived
base-change declarations. No false statement or target-signature change is asserted.
The reduced-base Grauert criterion cannot be used: this item's base may be nonreduced.

The public natural higher-image comparison theorem does not expose normalization on the
specific class map. The proof imports that module with `import all` and uses its proved
private canonicalComparison and canonicalComparison_class. These refer to the actual
sheafification construction and avoid choosing an unnormalized isomorphism.

## New nodes

lem-weil-pbc-coherent-etale-raw-direct-image-comparison: the sole new obligation concerns
raw structure-cohomology classes for any quasi-compact separated morphism, with no
properness, smoothness, curve-dimension or local-freeness assertion. It provides a locally
bijective presheaf map into the etale tensor sections of the fixed Zariski higher image,
with scalar compatibility before sheafification. The parent separately proves all curve
geometry and constructs the isomorphism after sheafification, so the new statement is
not the parent under another name or with repackaged hypotheses.

What remains is the affine construction using normalized etale/Zariski cohomology,
the invertible resolution-defined flat-base-change map and affine Leray section maps;
its restriction compatibility must then be glued over affine covers and its scalar
formula checked on those covers. The node names the existing declarations for these
steps. Its docstring describes the maps, restriction and coefficient squares, cover
gluing, local bijectivity and scalar calculation. Edge cases checked mathematically:
empty source, empty base object, q=0, degree above cohomological dimension, and zero
higher image. No positivity of a vector-bundle rank or reducedness is used.

Searches were run through msearch.py (leansearch, leanfinder, loogle and grep) and recorded in the
new node. Repository/DAG searches and blueprint_refs searches for etale structure,
03P2 and higher direct image found no existing node stating this combined raw coherent
comparison. Its blueprint origin is the parent's nearest blueprint ancestor and the
same inherited 0GKW/0GKV structure-cohomology step. The checker classifies the local proof commands conservatively as an interface change;
coord/changes/X5-smooth-curve-proof-local-settings.md records their exact scope and the
consumer check. No existing statement, definition or exported reducibility setting changes.

## Second reading by X5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
