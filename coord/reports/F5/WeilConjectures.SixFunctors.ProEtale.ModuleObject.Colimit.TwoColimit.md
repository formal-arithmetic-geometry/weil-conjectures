## What changed

Filled the five existing proof holes in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`.
The public declaration signatures, attributes, imports, and all existing definition bodies
are unchanged. Hom-surjectivity precedes object descent because the latter uses it.
All added imports serve proofs only; all added declarations are proved private helpers.
No new theorem hole is introduced by the helper reuse.
No other Lean module is edited, and no quarantined module is withdrawn or restored.

The preservation lemmas specialize the existing exact scalar-extension theorem.
Hom-injectivity uses the existing faithful derived scalar-extension theorem, with the
reflexive field inclusion as the eventual stage. Hom-surjectivity applies the existing
coefficient-complex presentation to a small final tail of coefficient fields. The single-sheaf Hom continuity theorem, the existing distinguished-extension closure
lemma, and bounded cohomological devissage give continuity for every bounded constructible
source. Filtered-colimit representatives give the required stage factorization. The actual
extension/restriction adjunctions then recover a finite-stage arrow. The parent proves the
component formulas for its actual full-subcategory tensor comparisons using `map_preimage`.

Object descent uses the finite-field triangulated structures from the existing finite-model
proof API, the existing directed-triangulated-image theorem, and finite-presentation sheaf
descent. Exact scalar extension identifies extended single complexes, and bounded devissage
then provides a finite model for every object. The full inclusion lifts its ambient isomorphism.
The specific finite-field triangulated structures avoid the disputed arbitrary-ring instance.

The proof reuses the already proved private derived-isomorphism, shift, triangulation,
and graded-tensor helpers of `Sheaf.Paper.CondensedFiniteModelExtensions`, imported with
`all`. It retains only local tensor-colimit and flat-resolution instance caches. Locally
prioritizing the direct colimit-preservation projections and deferring pending instance
synthesis while elaborating the original constructions avoids redundant tensor searches.
Their usual settings are restored for the new proofs. Local irreducibility keeps the
derived comparison values from expanding during instance matching. These settings
change no data or public interface.

The object-descent argument adapts the earlier A2/B2 proof preserved in the UpstreamExtra
archive. Hom-surjectivity uses the existing canonical Hom-continuity extension lemma directly. `import all` of the existing finite-model
proof API provides its proved private helpers without copying or redeclaring them. In particular
this avoids the archived module's `Unknown identifier factors` failure. The archive itself
remains untouched. The changed DAG proofs describe precisely the implemented route.

`coord/changes/F5-two-colimit-proof-elaboration.md` records the private instance and
local elaboration commands requested by server preflight, with the complete downstream
consumer table. No consumer adaptation or public-interface change is made.

Validation: the complete optimized source file compiles in 42.9 seconds with no errors
or sorries. The generic Hom-continuity closure block also compiles separately in 3.3 seconds.
Text comparisons verify that all six original theorem signatures, all three public imports,
and all nine existing non-theorem bodies remain unchanged. The dependency overlay has
no cycles, and every proof-dependency list equals the union of its steps' uses. No compile
limit has been raised. The required delivery runs compilation and preflight again.

## Proved and sorry left

Closed original holes (5 of 5):

- `AlgebraicGeometry.ProEtale.boundedConstructible_derivedExtendScalarsSubfield_obj`
  (`lem-sfb-extend-subfield-constructible`).
- `AlgebraicGeometry.ProEtale.boundedConstructible_derivedExtendScalarsToPadicAlgCl_obj`
  (`lem-sfb-extend-to-qlbar-constructible`).
- `AlgebraicGeometry.ProEtale.constructibleCocone_homSurj`
  (`lem-sfb-constructible-cocone-hom-surj`).
- `AlgebraicGeometry.ProEtale.constructibleCocone_essSurjObj`
  (`lem-sfb-constructible-cocone-obj`).
- `AlgebraicGeometry.ProEtale.constructibleCocone_homInj`
  (`lem-sfb-constructible-cocone-hom-inj`).

No sorry remains in the item. No new sorry or new obligation is added, and no existing
proved declaration is replaced by sorry. The unchanged assembly theorem uses these five
proofs through the existing constructible functors. Imported named inputs can still rest on
existing obligations; this delivery claims closure of the item's five holes, not closure of
all their dependencies.

## No longer needed

The Mathlib leanfinder, loogle, grep, and source searches found no replacement for the
coefficient-descent theorem. The existing source bounded-devissage theorem and the declared
Hom-continuity extension theorem provide the shorter route used here.

No original public import was removed. The proof-only imports are the generic preservation,
faithfulness, finite-model proof API and extension helpers, directed triangulated image,
finite-presentation descent, sheaf Hom continuity, Hom-continuity extension, and
coefficient-complex presentation modules.

Preservation uses `lem-weil-pbc-bounded-constructible-exact-scalar-extension`, so it does not
separately import `Sheaf.AlgebraicGeometry.SubfieldExtensionLocalPresentation`,
`Sheaf.AlgebraicGeometry.InternalExtensionInverseImage`, or
`Sheaf.AlgebraicGeometry.InternalExtensionFinitePresentation`.
The generic preservation proof already supplies these presentation calculations. Its exact
homology comparison also replaces a separate use of
`Sheaf.CategoryTheory.DerivedCategory.LeftDerivedTotalTensorExact` and
`lem-sfb-extend-scalars-preserves-homology`. These are removed direct proof edges, not claims
that their other consumers disappear.

Object descent does not import
`Sheaf.AlgebraicGeometry.ConstructibleCoconeAmbientRealization`: its necessary ambient cocone,
triangulated functors, and single-complex realization are proved privately in the item.
`lem-weil-pbc-condensed-flat-coefficient-calculus` is unnecessary as a direct parent input;
the existing Compatibility instances give exactness and the source exact-derived APIs give
all required realization maps. Other imported inputs may retain this node transitively.

Hom-surjectivity does not import
`Sheaf.Paper.CondensedBoundedHomContinuity` or
`Sheaf.AlgebraicGeometry.CoefficientCoconeComparisonAgreement`, both of which import the item.
It proves its needed factorization and comparison components directly. Consequently its direct
edges to `lem-sfb-condensed-bounded-hom-continuity` and
`lem-sfb-coefficient-cocone-comparison-agreement` disappear.
The small final tail uses Mathlib's `AsSmall`, `Under.forget`, and filtered upper bounds,
so it does not separately use `det-def-sfb-qlbar-condensed-subextensions` or
`Sheaf.Paper.FiniteSubextensionsDirected`.

The argument uses `def-weil-pbc-hom-colimit-property` and
`lem-weil-pbc-hom-colimit-extension` directly. It does not need
`lem-sfb-bounded-cohomology-cone-witness` as a direct parent input: the existing proved
`DerivedCategory.prop_of_bounded` supplies bounded devissage. The finite-model proof API
already supplies the representative and cocone-transport helpers. Hom-surjectivity no longer
needs faithful scalar extension; hom-injectivity still uses it.

The source assembly theorem constructs the three fields of
`CategoryCocone.IsFilteredTwoColimit`; it does not import
`lem-weil-pbc-coherent-cocone-normalization`, `det-def-sfb-filtered-two-colimit-model`, or
`det-def-sfb-filtered-two-colimit-characterization`. Those parent edges are removed.
No whole module is withdrawn, and no claim of global module pruning is made.
The unit's four descent clauses and its construction of the cocone are retained.

## Where the brief, the DAG or earlier work was wrong

Several declared DAG dependencies import this very item, so they cannot be used as proof
imports here. The existing generic preservation and finite-model APIs are below the item.
The existing extension lemma supplies a shorter valid route for bounded Hom continuity,
and the parent proves its tensor comparison components directly. This avoids the archived
monic-leg argument and its additional cancellation calculation. No statement change or weakened hypothesis is needed.

The earlier archive retained uses of private finite-model helpers but imported their module
without `all`. This item imports the API with `all` for its own private proofs; the
archive and all of its dependencies and attachments are preserved.

The source's module docstring still labels the inputs as sorried. It is kept unchanged along
with the source definitions; the actual proof and the report record which holes are closed.

The current unit record has no realized node entries. Its statement, its steps, and the
ordinary-category three-clause interpretation remain unchanged. The existing parent DAG
record had a separate normalization and pair-category-construction paragraph beyond what
the attached source declaration proves by assembly; its proof now matches that declaration.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
