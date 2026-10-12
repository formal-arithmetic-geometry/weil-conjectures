## What changed

Proved `AlgebraicGeometry.Etale.exists_addEquiv_module_abelian_stalk_exchange`
without changing its signature. The proof constructs canonical derived source and target
isomorphisms, transports exchange through the single-functor comparison, applies homology,
and uses the natural filtered-colimit stalk/forgetting comparison. The final equality uses
`Etale.baseChange_eq_derivedBaseChangeMapPlus` to recover the module map in the statement.

Added two modules, each with its own node:
`Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison` proves invertibility
of the canonical derived direct-image coefficient comparison and constructs the canonical
inverse-image comparison from the existing proved underived theorem.
`Sheaf.AlgebraicGeometry.ModuleAbelianDerivedExchangeCompatibility` fixes the source and
target comparison maps and states their compatibility with derived exchange.
All additions to the item's imports are proof imports. Existing public imports are kept.
No existing definition, theorem signature, target, chapter, or unit record changes.

The direct-image proof follows Stacks 03FD: the constant-ring module equivalence preserves
injectives; ringed-site injective Cech acyclicity and the etale complex comparison feed the
Cech vanishing criterion on all objects. The higher-direct-image sheafification theorem
then gives direct-image acyclicity of the forgotten sheaf. The source library's
`isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic` proves invertibility of the
canonical comparison on all bounded below complexes.

All three modules compile locally in import order without errors or warnings, within
the per-file limit. The delivery dry run supplies the server and preflight checks.

## Proved and sorry left

The original item had one sorry; it now has none:
`AlgebraicGeometry.Etale.exists_addEquiv_module_abelian_stalk_exchange` is proved from
named declarations, including the one remaining compatibility obligation below.

The new theorem
`AlgebraicGeometry.Etale.isIso_moduleAbelianDerivedLowerStarComparison`
(node `lem-weil-pbc-module-abelian-derived-direct-image-comparison`) is proved from
existing statements. Its module has no sorry, including its private evaluation-acyclicity
helper and its inverse-image naturality and invertibility proofs.

Exactly one new sorry remains:
`AlgebraicGeometry.Etale.moduleAbelianDerivedExchange_compatibility`
(node `lem-weil-pbc-module-abelian-derived-exchange-compatibility`). Its whole proof is
`:= by sorry`, with the source and complete proof plan in its docstring. This is the
map-compatibility part of the argument for fixed canonical comparisons in D+, independently
of stalks, homology degree, or the existence/invertibility of the comparison maps. It does
not restate the item: the isomorphisms are already constructed and the item performs
single-complex transport, homology naturality, stalk naturality, and additive-equivalence
conversion in Lean. Imported named theorems may still have sorry as intended in stage 3.

## No longer needed

The three pre-existing public imports remain required by the unchanged signature.
Removed proof imports from the item: `Sheaf.AlgebraicGeometry.DerivedExchangeTermwise`,
`Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`,
`Sheaf.AlgebraicGeometry.InjectiveModuleAbelianAcyclic`,
`Sheaf.AlgebraicGeometry.ModuleAbelianInverseImageComparison`,
`Sheaf.Paper.HigherDirectImageSheafifiedPresheaf`, and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KInjective`.
The inverse-image comparison and higher-direct-image theorem are still used through
the new direct-image comparison module. No unused proof import is retained.

The item's old direct proof dependencies are replaced as follows; this is a claim about
this route, not about global reachability from other targets:

- `lem-weil-pbc-injective-module-abelian-acyclic` and its module
  `Sheaf.AlgebraicGeometry.InjectiveModuleAbelianAcyclic` are not used. Its recorded
  `SheafOfModules`/ULift coefficient encoding only covers a ring in `Type u`. We instead
  prove the evaluation-acyclicity needed for `ModuleCat.{u+1} Λ`, with arbitrary
  `Λ : Type (u+1)`, from existing general constant-ring and Cech statements.
- `lem-weil-pbc-derived-exchange-termwise` and
  `Sheaf.AlgebraicGeometry.DerivedExchangeTermwise` are not needed. The remaining
  compatibility obligation uses the proved derived-unit factorization and uniqueness
  API, rather than the arbitrary K-injective comparison package.
- `prop-weil-pbc-cohomology-resolution-independent` and the dedicated
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KInjective` proof import are
  not needed. No pair of arbitrary resolutions is selected by this proof.
- `prop-weil-pbc-geometric-stalks-exact` is not needed: we apply the stalk functor to an
  already commuting square of sheaves; only its commutation with coefficient forgetting
  by filtered-colimit preservation is used.
- `prop-weil-pbc-inverse-image-modules-exact` and
  `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact` are not used. Existing exact
  `ModuleCat`-valued etale inverse-image instances and the canonical underived coefficient
  comparison suffice; no construction of ringed-site module inverse image is required.

`lem-weil-pbc-higher-direct-image-sheafified-presheaf` remains needed by the proved
new direct-image comparison, and `lem-weil-pbc-module-abelian-inverse-image-comparison`
remains needed by its canonical inverse-image utilities. Geometric stalks remain the
notion in the final statement. No node realizing a unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan named acyclicity for the `SheafOfModules`/ULift encoding with a ring in
`Type u`; that interface does not directly apply to this item's arbitrary ring in
`Type (u+1)`. The existing `ModuleSheafConstantRingEquivalence` and general ringed-site
Cech statements provide the correct encoding without changing any statement.

The plan's word "comparison" also hides a genuine coherence obligation. Arbitrary
existence of source and target isomorphisms would not identify exchange. The delivery
fixes both maps using units and explicitly isolates equality for those fixed maps.

`lem-weil-pbc-exchange-forget-coefficients` was found in the whole-DAG search. It has no
Lean record and is unsplit; it bundles underived inverse image, derived direct image,
exchange compatibility, and reflection of isomorphisms. The two new nodes isolate
strict parts with explicit Lean maps; they do not duplicate a usable declaration.

The clone lacks `literature/stacks-project/sites-cohomology.tex`; the cited source tags
03FD, 072W, 0736, 07A7, and 0D6J were read on the Stacks website. Source references remain
those of the existing node. LeanFinder, Loogle, and grep searches were run; LeanSearch
returned an Internal Server Error, recorded as unavailable. No exact declared exchange
coefficient compatibility was found. The blueprint ancestor script also returned None
for this created node; the new nodes therefore inherit the existing parent's explicit
blueprint ancestor `prop-weil-pbc-strict-local-exchange` and its via chain.

Edge cases were checked against the constructions: zero coefficients and zero complexes
use functorial isomorphisms, the identity square uses the canonical units, degree zero
is included, and empty schemes impose no extra condition. No properness, torsion,
strict-local, compactness, or small-ring hypothesis enters a new theorem.

## New nodes

`lem-weil-pbc-module-abelian-derived-direct-image-comparison` records the proved
invertibility of `moduleAbelianDerivedLowerStarComparison`, the source library's fixed
unit-compatible map for an arbitrary scheme morphism. The node's proof follows the
actual Cech, evaluation, sheafification, classical homology, and derived base-change
steps. Its module also contains proved exactness and canonical inverse-image utilities.

`lem-weil-pbc-module-abelian-derived-exchange-compatibility` records the sole remaining
sorry. It states a categorical equality for fixed canonical source and target
isomorphisms on any bounded below module complex and any commutative square. Its proof
plan expands unit, square isomorphism, and counit and uses uniqueness of the right
derived transformation. The item's node is updated to the resulting assembly route.
No change record is needed because no existing public interface changes.

## Second reading by R2

1. I compared the delivered item module with the repository version. The target declaration and its signature are byte for byte unchanged; only its proof and proof-only imports changed. The two added modules are new declarations with matching node records, and no existing definition was altered.

2. I compiled all three delivered modules with `lcompile.py --all`; they compile without errors or warnings. The item has no `sorry`; the sole remaining `sorry` is the named public theorem `moduleAbelianDerivedExchange_compatibility`, documented and represented by its split node. No axiom, unsafe, opaque, extern, or implemented_by declaration was added.

3. I checked the new statements against their constructions and edge cases. The direct-image comparison is the fixed unit-compatible map and is proved from the stated Cech and sheafification results. The exchange compatibility theorem is a strictly intermediate equality for fixed maps and does not restate the item. Searches recorded in the nodes found no existing declaration with either statement.

4. The proofs use the canonical derived comparison route and retain the unit's exchange path. Imports removed from the item are listed in `## No longer needed`; the added modules' imports are proof-only where appropriate. The DAG proof, dependencies, origins, and split status agree with the Lean declarations.

5. The unit route is retained: the item remains below `prop-weil-pbc-strict-local-exchange`, which realizes a step of `sk-thm-p1`; the new nodes isolate only the direct-image comparison and its remaining compatibility obligation. No statement or definition change record is needed.

I corrected the report's inaccurate claim that no import was removed, explicitly listed the six removed proof imports, and added this second-reading record. No Lean repair was necessary after compilation. Independent searches for exact coefficient-change compatibility found no matching declaration (grep: zero hits; LeanFinder: scalar-extension and Kan-extension comparisons only).
