## What changed

Restored the returned three-module reduction of
`Sheaf.AlgebraicGeometry.ExtPullbackResolutionSections`. The existing declaration
`AlgebraicGeometry.extPullback_resolution_sections` keeps its signature byte for byte.
Its proof constructs the square of explicit Hom-complex evaluation maps, applies homology,
and combines it with the remaining Ext comparison. The adjunction transpose is proved in
`Sheaf.AlgebraicGeometry.ConstantSheafPullbackTranspose`; the explicit chain map and the
remaining comparison are in `Sheaf.AlgebraicGeometry.ExtPullbackHomComplex`.

The local `backward.defeqAttrib.useBackward` option at `homPullbackMap` is retained from the
worker's timeout repair. No existing definition or interface is changed: both dependency
modules are absent from the repository baseline. This is restoration of a returned
reduction, not a forced adaptation. No change record is necessary.

The second reader replaced the dependency modules' unnecessarily broad public import of
`WeilConjectures.SixFunctors.Etale.Derived.GlobalSections` with the modules their signatures
actually require: `UpperLowerStar.GlobalSections` for the transpose and
`UpperLowerStar.TopologicalInvariance` for the Hom-complex comparison. The latter also
publicly imports Mathlib's `Injective.Resolution` for the chosen-resolution abbreviation
and `Injective.Ext` for the displayed equivalence. Enough-injectives instances are already
provided transitively by `TopologicalInvariance`.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.extPullback_resolution_sections`, node
`lem-weil-pbc-ext-pullback-resolution-sections` (the item's only original hole).
Hole added: `AlgebraicGeometry.SheafPullbackResolution.extPullback_homComplex`, node
`lem-weil-pbc-ext-pullback-hom-complex` (the delivery's only remaining `sorry`).
Thus this is a decomposition: one original hole closed and one lower hole added; net
zero holes closed in this reduction, not a completed Ext comparison.

The new theorem `AlgebraicGeometry.constantSheaf_pullback_transpose`, node
`lem-weil-pbc-constant-sheaf-pullback-transpose`, is fully proved. The new definition
`AlgebraicGeometry.SheafPullbackResolution.homPullbackMap` constructs all its data and proves
its additivity and chain-map law explicitly. No data is chosen from a holed theorem.

## No longer needed

Removed direct imports from the item:
`Sheaf.AlgebraicGeometry.EtaleInverseImageExact` and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`.
The latter is still reached transitively because its `cohomologyMap` occurs in signatures.
The second reader also removed the broad `Derived.GlobalSections` imports from both new
modules, replacing them as described above; the item still reaches that module through
its existing public import of `SheafHExtResolutionSectionsIso`.

Every old proof dependency absent from the item's new direct `proof_deps` is:
`def-weil-pbc-cohomology-pullback`, `lem-weil-pbc-ext-via-injective-resolution`,
`lem-weil-pbc-kinjective-hom-derived`, and `prop-weil-pbc-inverse-image-exact`.
These belong to the remaining Hom-complex comparison's plan; they are not claimed globally
unnecessary. `def-weil-pbc-ext-resolution-sections-iso` stays a direct proof dependency.
No whole-library module is claimed pruned, and no unit realization is removed.

## Where the brief, the DAG or earlier work was wrong

The returned reduction took 97 seconds in the global single-file build. The worker's local
elaboration-option repair now compiles within the 60-second limit. The first report called
this a forced importer adaptation and omitted the baseline hole accounting and old
proof-dependency list. Those claims are corrected here: the existing theorem's signature
and existing definitions are unchanged, and this delivery has one added lower hole.

Fresh searches by the second reader used different queries:
LeanFinder: "homology of Hom complex natural under an exact additive functor and a resolution comparison";
Loogle: `"extEquivCohomologyClass"`;
grep: `CohomologyClass.*map|map.*CohomologyClass|mapExactFunctor_hom|homologyIso.*naturality`.
The results supply same-category resolution naturality, the Ext/resolution equivalence,
and `Abelian.Ext.mapExactFunctor_hom`. Their source types were inspected. None directly
states the cross-category comparison with the supplied augmentation homotopy. Repository
search also found no existing theorem for it. Closing the remaining hole requires the
localized roof computation, not an immediate application of a found lemma.

## New nodes

`lem-weil-pbc-constant-sheaf-pullback-transpose` records the proved constant-sheaf adjunction
transpose, for arbitrary coefficient group and sheaf. It handles the evaluation part of
the original proof, independently of injective resolutions.

`lem-weil-pbc-ext-pullback-hom-complex` records the remaining Ext/resolution comparison
before evaluation. Its docstring gives the localized roof proof, including cancellation
of the augmentation using the supplied homotopy. This is strictly the Ext portion of the
argument; the chain-map evaluation square is actually proved in the item, rather than
moved into the hole. Both node records existed after the returned earlier delivery; their
Lean signatures have been rewritten verbatim from the restored source modules. The
parent node's proof and direct dependencies describe the actual reduction.

## Second reading by E1

1. Compared each module with the repository using `diff`. The item's only existing public
   theorem has exactly its old signature; only its proof, proof imports and a private
   naturality helper are added. The two dependency source modules are absent from the
   baseline. No existing target statement or definition was altered. Verdict: pass.
2. Read the explicit cochain construction, differential calculation, adjunction proof,
   evaluation square and homology calculation. All modules compile in import order with
   no errors or warnings. The sole `sorry` is the named Hom-complex theorem above; no
   forbidden declaration or holed definition occurs. The scratch axiom check and delivery
   probe validate the permitted axioms, including inherited `sorryAx` for open results.
   Verdict: pass, conditional on the documented remaining comparison.
3. Checked the lower comparison's mathematical proof and the fully proved transpose.
   In degree zero they compute the map on Hom; for a zero sheaf or an empty scheme both
   sides give the zero group map; for identity pullback augmentation-compatible lifts are
   equal after localization, as required. There is no extra injectivity assumption on the
   pulled-back resolution. Repeated three search kinds and inspected candidate types;
   no direct duplicate or immediate closure was found. The hole is only the Ext portion,
   and the evaluation portion is proved separately. Verdict: valid decomposition.
4. Checked the proof top downward and replaced the two overly broad imports. Every old
   direct dependency removed is listed above. Read `dag/units/sk-thm-p1.json`, including
   `realized`: this helper remains inside the strict-local exchange computation and
   changes no unit step or chapter route. Verdict: pass.
5. Checked node declarations and signatures against Lean, and the parent's steps against
   the actual proof. The new direct dependency set is precisely the Hom comparison,
   proved transpose and explicit resolution-section isomorphism. The lower node retains
   its sourced proof plan and complete docstring. Verdict: pass.

Second reading changed: narrowed both new modules' public imports, added the necessary
Mathlib chosen-resolution import, synchronized node Lean signatures verbatim, removed the
inapplicable change record, and corrected hole accounting, pruning and review documentation.
