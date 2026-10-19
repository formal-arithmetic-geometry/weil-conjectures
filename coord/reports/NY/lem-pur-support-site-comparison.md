## Worker report

The module `Sheaf.AlgebraicGeometry.SupportSiteComparison` states the ordinary-module etale/pro-etale comparison for sections with closed support and its compatibility with the two actual supported exterior products. All theorem proofs are `sorry`. The node's mathematical statement, hypotheses and proof are unchanged.

The earlier NZ merge was a stage-1 split and review, not a Lean statement. The item has no published comparison module. During this recovery the published N4 modules `SupportedExteriorProduct` and `ProEtaleSupportedExteriorProduct` were found and read in full; this delivery reuses both and removes the older sandbox copies of those constructions. Its only added statement dependency is the already-landed `def-pur-proetale-supported-exterior-product`. There are no new definition nodes.

Hypothesis and clause correspondence:

- The base is `k : Type u` with `[Field k] [IsAlgClosed k]`; schemes over it use `[T.Over (Spec (.of k))]`. Finite type is the conjunction of `LocallyOfFiniteType` and `QuasiCompact` on the structure map. `IsSeparated` is separatedness by the closed diagonal, not properness. These hypotheses appear for T in the comparison and open-restriction statements and separately for X and Y in the product statement.
- `A : Type (u + 1)` with `[CommRing A] [Finite A]` is any finite commutative ring. `Sheaf ... (ModuleCat.{u + 1} A)` is the published ordinary fixed-scalar module encoding of modules over the constant ring sheaf. It is not a condensed coefficient category. The sites retain object universe u+1 and morphism universe u.
- A closed subscheme C is a map `i : C ⟶ T` with `[IsClosedImmersion i]`. The product clause similarly has `i : Z ⟶ X` and `j : W ⟶ Y`. The open complement is Mathlib's `i.openComplement`; the product support is the published `Etale.supportedProductImmersion f g i j`, with source the fibre product of the closed subschemes over the base.
- The etale support functor is exactly the published `Etale.supportedEtaleSections A T i.openComplement`: the kernel of global-section restriction to the complement. `etaleSupportKernel` is only its abbreviation. The pro-etale functor is the recorded `ProEtale.supportSections i A`, the kernel of evaluation restriction. Canonical global-section/terminal-evaluation identification relates the presentations; no private support functor is constructed.
- `supportComparisonUnit_existsUnique` characterizes the ordinary comparison by its kernel inclusion: take the etale supported section, include it in global sections, use the canonical terminal-evaluation isomorphism, then apply the actual comparison adjunction unit at the final object. This normalization uniquely determines the natural transformation, so choosing it postpones only a proof and does not choose arbitrary map data.
- `supportComparison` is `rightDerivedFunctorPlusBaseChange` of that normalized ordinary map. Its type is a natural transformation on the entire `DerivedCategory.Plus`, so naturality in M is part of its type. `supportComparison_isIso` asserts invertibility under exactly the first paragraph's geometric and coefficient hypotheses.
- `supportComparisonUnbounded` transports the bounded-below components along `rightDerivedFunctorPlusCompatibility` into the unbounded `DerivedCategory (ModuleCat A)`. Thus all product and forgetful equations live in the node's D(A), while their inputs remain in D-plus.
- `etaleSupportForget` and `proEtaleSupportForget` reuse the published kernel inclusions. `supportComparison_forget` is their commuting derived square with the existing adjunction-unit map `comparisonGlobalSections`. `fullSupportForget_isIso` says both full-support vertical maps are invertible, identifying the full-support comparison with precisely that global-section comparison.
- `supportComparison_open` quantifies over every `v : U ⟶ T` with `[IsOpenImmersion v]`. The restricted support is `pullback.snd i v`. Its two `supportOpenRestriction` maps are the transposes of the pulled-back support counits through the quotient-normalized open-pullback identifications. The pro-etale helper `supportOpenRestrictionOverField` derives local Noetherianity of T and U from finite type over k, rather than adding it to the statement. The final coefficient arrow is the specified derived comparison-pullback isomorphism.
- K and L are arbitrary `DerivedCategory.Plus` objects on the two etale sites. The product is the actual `pullback` of the two structure maps to `Spec k`. Its two projections occur in the existing `Etale.externalProduct`; this uses the existing total left derived inverse images and K-flat derived tensor.
- F and `eF` package exactly the assumption that this actual external product is bounded below: `F : DerivedCategory.Plus ...` and `eF : F.obj ≅ Etale.externalProduct ... K.obj L.obj`. Every lift and every identifying isomorphism is quantified. Both directions of `eF` occur in the equation, so no identity or arbitrary-lift case is silently discarded.
- `supportExteriorCoefficientIso` is theta: use the canonical identifications of total left derived and exact termwise pullback, the existing comparison derived tensor isomorphism, and the two derived comparison-pullback identifications; then return to the existing pro-etale external-product convention. No arbitrary coefficient isomorphism is supplied as a hypothesis. `supportBifunctorIso` only applies the existing tensor bifunctor to two isomorphisms; the final `supportedExternalProduct_eq` transport reuses the published external-product identification. This avoids the upstream-documented expensive unfolding of a scheme-indexed monoidal instance.
- `supportComparison_exterior` is the displayed equality of the two maps in D(A). Lean's `≫` is composition in diagram order: kappa-et, transport to F, product support comparison, support of theta equals tensor of the two comparisons followed by kappa-proet. The left pairing is the published `Etale.supportedExteriorProduct`; the right is the published `ProEtale.supportedExteriorProductOverField`. The latter derives the necessary local Noetherianity internally from finite type over the field. Neither pairing is asserted to be an isomorphism.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.DerivedCategories`, `SupportCohomology` and `EtaleSupportedSections`: `DerivedCategory`, `DerivedCategory.Plus`, `Sheaf.supportedSectionsFunctor`, `Etale.supportedEtaleSections`, `Etale.supportedEtaleSectionsι`, `ProEtale.supportSections`, and the restriction arrows.
- `Sheaf.AlgebraicGeometry.SupportedExteriorProduct`: `Etale.supportedCoefficients`, `supportedCoefficientQuotient`, `supportedCoefficientDerivedAdjunction`, `supportedProductImmersion`, and `supportedExteriorProduct`. These are the existing exact supported constant construction and normalized pairing.
- `Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct`: the analogous `ProEtale.supportedCoefficients`, quotient, adjunction, `supportedModuleSectionsι`, and `supportedExteriorProductOverField`.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison` and upstream `Comparison.Defs`: `comparisonUpperStar`, `comparisonLowerStar`, `comparisonAdjunction`. `ProEtaleSiteComparisonDerived.siteComparison_boundedBelow` is the recorded bounded-below fully faithful comparison theorem. Its intrinsic coefficient-realization module imports the incompatible finite-coefficient operations; the file imports the smaller original `WeilConjectures.SixFunctors.ProEtale.Derived.Comparison` instead. Its `isIso_derivedComparisonAdjunction_unit_app` gives the exact unit-isomorphism assertion used in the proof in the ordinary fixed-ring presentation, before coefficient realization.
- `Sheaf.AlgebraicGeometry.ComparisonGlobalCohomology`: `comparisonGlobalSections`, normalized by the derived comparison unit followed by the canonical Leray identification.
- `WeilConjectures.SixFunctors.ProEtale.Derived.ComparisonMonoidal`: `derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso`, obtained from the strong monoidal inverse image's derived tensor comparison. The two upstream `leftDerivedUpperStarIsoMapDerivedCategory` declarations identify the standard external products with exact termwise inverse images. For the proof-only general ringed-topos tensor result, the compatible `Sheaf.Paper.RingedTopoiCanonicalTensorPullback` is imported instead of its `ProEtaleCanonicalTensorPullback` specialization, which transitively imports the incompatible operation family. The actual coefficient comparison in the statement is the original upstream canonical comparison, not arbitrary isomorphism data.
- The repaired `SupportComparisonPullbackCoherence`: `supportSiteComparisonCoefficientPullbackIso`, the restriction-induced canonical adjunction mate. `Functor.mapDerivedCategoryNatIso` and `mapDerivedCategoryCompIso` give its exact derived transport.
- Mathlib's `Scheme`, `IsClosedImmersion`, `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`, and `Limits.pullback` are used directly. The standard `ModuleCat` and site derived tensor instances are reused.

Edge cases checked before accepting the signatures: empty schemes and empty closed supports give zero supported objects; full support gives the specified global-section comparison; the zero coefficient ring is allowed; zero complexes are allowed; supports may be nonreduced since the kernel depends only on their open complement; no smoothness, nonemptiness, properness, finite Tor amplitude or constructibility is assumed. K and L being bounded below does not imply their tensor is bounded below, so F/eF is essential and retained. Open restrictions need no extra boundedness assumption because inverse image is exact. The pro-etale argument uses canonical support constructions, not conservativity of ordinary geometric stalks on that site.

Searches: the saved msearch runs include LeanFinder for “etale proetale comparison cohomology with closed support and supported exterior products” (only algebraic etale-module results), Loogle for `CategoryTheory.Sheaf, kernel` (no match), and Mathlib grep `support.*comparison|supported.*exterior` (no match). Recovery reran LeanFinder for the free-sheaf kernel/cokernel adjunction (free-sheaf ingredients only), Loogle for `CategoryTheory.Sheaf.freeYoneda`, and Mathlib grep for `supportConstantFunctor|supportComparison|supportedExteriorProduct`. Direct rg of upstream WeilConjectures and the shared Sheaf tree found the published N4 exterior-product constructions, now reused; it found no supported site-comparison theorem. The main statement does not occur under its DAG id in upstream. A recovery LeanSearch query for the supported etale/pro-etale comparison returned eight unrelated algebraic etale-module results. The generic support-adjunction search and old diagnostic constructions are scratch history, not delivered definitions.

Sources opened: [Stacks 099W](https://stacks.math.columbia.edu/tag/099W), [099V](https://stacks.math.columbia.edu/tag/099V), and [09B1](https://stacks.math.columbia.edu/tag/09B1) give bounded-below global/derived module comparison. [09XP](https://stacks.math.columbia.edu/tag/09XP) gives ordinary support and its right derived functor. [0H9A](https://stacks.math.columbia.edu/tag/0H9A) and [07A4](https://stacks.math.columbia.edu/tag/07A4) supply cup-product base change and tensor pullback ingredients. The supported exterior-product refinement is the node's explicit blueprint proof, not claimed to be the statement of any one tag.

No `STATEMENT-DISPUTED` flag and no mathematical statement correction.

## Dependency modules

`lem-weil-pbc-comparison-pullback`: its current recorded module `CompactSupportComparisonPullbackCoherence` imports `FiniteCoefficient.UpperLowerStar.Defs`. The published support/exterior-product modules require the original `UpperLowerStar.Defs`; importing both produces the actual compiler error that the environment already contains `AlgebraicGeometry.ProEtale.term(_)_*[_]`. Section 1(B) therefore repairs the dependency interface in `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`. It retains the full set/abelian-group/finite-module theorem, canonical sectionwise direct-image comparison and its unit-normalized adjunction mate, and all identity, arbitrary-composite and specified-Cartesian-square coherence equations. Its construction is read directly from the recorded source, with the compatible original upstream import and a distinct `supportSite` prefix. Only the dependency's `lean` record changes.

The proof-only intrinsic/finite-coefficient extension-by-zero imports and two higher-level comparison/tensor specializations likewise conflict with the original operations; the file uses the smaller original upstream open-extension module, which gives the exact ordinary-coefficient extension needed by this proof. The original derived comparison supplies bounded-below unit invertibility, and the generic ringed-topos module supplies the canonical tensor theorem. No duplicate declaration is introduced or hidden.

Validation: the prescribed `scompile.py NY lem-pur-support-site-comparison` invocation compiled both delivered files in dependency order without errors or warnings. In the final local run, the library forms of `SupportComparisonPullbackCoherence.lean` and `SupportSiteComparison.lean` took 13.1 s and 14.2 s respectively, within the unchanged per-file limit. The final source contains no diagnostic `#check` commands. The delivery is submitted only to the required `deliver2.py --no-push` dry run; the second reader performs delivery.

## Second reading by NY

I independently read the sandbox node, both delivered modules, and the current
statement dependencies. The Lean expresses every clause of the item; I found no
mathematical statement mismatch and made no statement correction. No new definition
nodes are delivered. I preserved both Lean modules and their signatures.

Source reading: the `.tex` files are absent from the shared checkout, so I opened the
same Stacks source in `/home/ubuntu/weil-launcher-nt/literature/stacks-project/`.
In `proetale.tex`, `lemma-relative-comparison` (099V),
`lemma-compare-cohomology` (099W), and `lemma-compare-derived` (09B1) assume a scheme,
with 09B1 additionally a ring; their bounded-below clauses impose no characteristic,
properness or constructibility condition. I read `section-cohomology-support` (09XP)
in `etale-cohomology.tex`: its derived support is the kernel of restriction to the
open complement. In `sites-cohomology.tex`, `lemma-pullback-tensor-product` (07A4)
uses flat K-flat representatives and their signed total tensor; and
`lemma-base-change-cup-product` (0H9A) concerns the specified relative cup product.
The supported refinement is the node's eight-step proof, rather than a claim that
099W or 0H9A alone states the whole item.

My object/hypothesis/conclusion inventory, with the actual Lean counterpart:

| Node item | Lean rendering and verdict |
| --- | --- |
| Algebraically closed field k | `(k : Type u) [Field k] [IsAlgClosed k]`; matches. |
| Finite commutative ring A | Section `(A : Type (u + 1)) [CommRing A]`, with `[Finite A]` in the comparison assertions; matches, without a nonzero or characteristic restriction. |
| Ordinary constant-ring modules | `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)` and `Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)`; these are the fixed-scalar presentation of ordinary constant-ring modules, not condensed modules. Matches the recorded derived-category convention. |
| Finite-type separated k-scheme T | `[T.Over (Spec (.of k))]`, `[LocallyOfFiniteType (T ↘ Spec (.of k))]`, `[QuasiCompact (T ↘ Spec (.of k))]`, `[IsSeparated (T ↘ Spec (.of k))]`; matches. Mathlib's separated class asserts the closed diagonal; the cited proper-morphism node includes that distinct notion. No properness is assumed. |
| Closed subscheme C | `(i : C ⟶ T) [IsClosedImmersion i]`; matches, including nonreduced supports. |
| Bounded-below M | `DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))`; matches cohomological boundedness, not termwise boundedness or boundedness above. |
| The comparison inverse image ν* | `comparisonUpperStar ... T` and its `mapDerivedCategoryPlus`/`mapDerivedCategory`; these are the recorded Kan-extension/sheafification inverse image. Matches. |
| Ordinary derived support functors | `etaleSupportKernel A i` abbreviates the published `Etale.supportedEtaleSections A T i.openComplement`; `supportSections i A` is the published pro-etale evaluation kernel. Their right derived functors match 09XP through canonical terminal-evaluation identification. |
| Canonical c | `supportComparisonUnit_existsUnique` normalizes the ordinary map by the kernel inclusion, terminal-evaluation isomorphism, and actual comparison adjunction unit. `supportComparison` derives precisely that map with `rightDerivedFunctorPlusBaseChange`. Matches; no arbitrary map is a hypothesis. |
| Isomorphism and naturality in M | `supportComparison_isIso` asserts `IsIso` of the natural transformation on the entire bounded-below category. Naturality is therefore in the transformation's type. `supportComparisonUnbounded` transports its components to D(A) by `rightDerivedFunctorPlusCompatibility`. Matches. |
| Forgetting supports | `supportComparison_forget` equates the two composites using the existing kernel inclusions and `comparisonGlobalSections`. Matches the required square with that actual global comparison. |
| Full support C=T | `fullSupportForget_isIso A T` concerns both inclusions for `𝟙 T`. Together with the preceding square, it identifies c with the adjunction-unit global comparison. Matches. |
| Open restriction | `supportComparison_open` quantifies over every `(v : U ⟶ T) [IsOpenImmersion v]`, uses `pullback.snd i v` as the restricted support, and ends with the map of `supportDerivedPullbackIso A v`. The restriction maps are the transposes of the actual support counits under quotient-normalized pullback. Matches, with no additional quasi-compactness hypothesis on the open. |
| X,Y,Z,W in the product clause | X and Y each have the same separated finite-type k hypotheses; i and j are closed immersions into them. Matches, with no finiteness hypothesis on K,L or smoothness hypothesis on the schemes. |
| Bounded-below K,L | The two independent `DerivedCategory.Plus` binders in `supportComparison_exterior`; matches. |
| Actual external product F bounded below | The independent plus object F and `(eF : F.obj ≅ Etale.externalProduct ... K.obj L.obj)` package precisely that condition. All F and eF are quantified. Both `eF.inv` and the comparison image of `eF.hom` occur, so arbitrary presentations and the identity presentation give the same assertion by naturality. Matches. |
| Products over k and their projections | `pullback (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))`; `Etale.externalProduct` is the tensor of the two total-derived projection inverse images. `Etale.supportedProductImmersion` is the induced map from `pullback (i ≫ f) (j ≫ g)`. Matches the scheme-theoretic product support. |
| Kp,Lp | The actual `mapDerivedCategory.obj K.obj` and `mapDerivedCategory.obj L.obj` for comparison inverse image. Matches; no separately chosen coefficients. |
| Specified θ | `supportExteriorCoefficientIso` uses exact/left-derived projection identifications, `derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso`, both `supportDerivedPullbackIso` components, and returns to the published pro-etale external-product convention. Its directions are ν* of the etale product to the pro-etale product. Matches the canonical tensor/pullback composite. |
| Equality in unbounded D(A) | `supportComparison_exterior` has left path etale κ, support of `eF.inv`, c at F, and pro-etale support of ν*(eF.hom) followed by θ; the right path is `tensorHom` of the two c maps followed by pro-etale κ. `≫` is diagram-order composition, so this is precisely the node's displayed equation. |
| Actual pairings and no Kunneth claim | The maps are `Etale.supportedExteriorProduct` and `ProEtale.supportedExteriorProductOverField`. I read their definitions: both are the normalized derived coefficient-tensor map followed by the tensor of pulled-back counits and the support-adjunction transpose. Neither κ is asserted invertible. Matches. |

Dependency interface reading: I opened `SupportCohomology`, `EtaleSupportedSections`,
`SupportedExteriorProduct`, `ProEtaleSupportedExteriorProduct`, `DerivedCategories`,
`ProEtaleSiteComparison`, `ComparisonGlobalCohomology`, and the upstream comparison,
derived comparison, derived tensor and derived-pullback definitions. I also read the
actual side-project `WeilConjectures.SixFunctors.ProEtale.Derived.ComparisonMonoidal`
and `coord/pefw-upstream-framework.md`. In the monoidal module, the comparison is
constructed from `leftDerivedTensorComparison` of the actual strong monoidal inverse
image; its generic source derives the ordinary comparison through the K-flat
localization universal property. This supplies the specified tensor comparison,
not arbitrary isomorphism data. The generic ringed-topos canonical-tensor module is
available for the proof; the recorded pro-etale specialization imports the conflicting
finite-coefficient operations. The original derived comparison supplies the actual
bounded-below unit isomorphism, before intrinsic coefficient realization. Thus the
smaller compatible imports preserve the ordinary-coefficient mathematical interfaces.

I read the dependency module `SupportComparisonPullbackCoherence` against the full
node `lem-weil-pbc-comparison-pullback` and its four proof steps. Its constructed
inverse image is Kan extension plus sheafification; the direct-image comparison
identifies sections on exactly the same chosen fibre product. `conjugateIsoEquiv`
with the composite adjunctions fixes the inverse-image isomorphism and its unit
normalization. The three conjuncts of `supportSiteComparisonPullbackCoherent` quantify
over every scheme/sheaf, every composable pair, and every specified
`ChosenCartesianSquare`, retaining the supplied `sq.w` transport. The final theorem
covers sets, abelian sheaves, and every finite ring's left modules, including
noncommutative rings. No clause of that dependency was weakened. The repaired
names are listed in the dependency's `lean.declarations`.

Mismatch and repair: the first report and dependency `lean.note` named the now
superseded `CompactSupportComparisonPullbackCoherence`. The current base instead
records `Sheaf.AlgebraicGeometry.ComparisonPullbackCoherence` (Q05). I opened that
file: it still imports `FiniteCoefficient.UpperLowerStar.Defs`, whereas the delivered
support constructions require the original `UpperLowerStar.Defs`. Both define the
same pro-etale operation names/notation, so the import incompatibility persists.
I updated the dependency `lean.note` to identify the current recorded interface and
preserved the current base's non-Lean metadata. The delivered repair states the full
same mathematical interface using the compatible imports. The older name in the
worker report is historical; this paragraph supplies its current correction. No
mathematical statement, definition or signature required rewriting.

Edge cases checked: empty ambient schemes, empty support, full support, empty or
whole open restriction, zero ring, zero complexes, arbitrary cohomological lower
bounds (including degree zero), and every characteristic are covered. Empty support
has zero kernel; full support has empty complement and the two kernel inclusions
are invertible. The product coefficient's boundedness is essential: two bounded-below
complexes over a general finite ring need not have bounded-below derived tensor.
The support-object tensor itself may be unbounded; the equation and support
adjunctions live in D(A), so this case is retained. No index-set parameter appears.
The sites have object universe u+1 and morphism universe u, while fixed-ring module
Homs live in u+1. Every u is quantified, coefficient A is finite, and the ordinary
size convention is the same as the recorded site/derived-category dependencies;
there is no extra equality imposed between site object and morphism universes.
Locally Noetherian instances in the pro-etale helpers are derived internally from
locally finite type over the field (and its open restriction); they are not additional
hypotheses of the item. I checked `autoImplicit false` and all section binders.

Independent H4 searches, using different queries from the worker: msearch LeanFinder
for "Local cohomology of ordinary module sheaves under etale to proetale inverse
image preserves external cup products" returned eight light-condensed/module results,
none about this statement. Loogle for `"supportedSections"` returned zero hits.
Mathlib grep for `localCohomology|support.*[Cc]omparison|[Cc]omparison.*support`
returned only the algebraic ideal-local-cohomology constructions. Direct rg of the
upstream project and the shared Sheaf tree for those patterns and `ΓRes` found
ordinary section restriction and compact-support direct-image comparisons, not this
closed-support site-comparison equality. I opened the existing supported-product
constructions rather than writing copies. These searches do not justify an
`existing: true` record for the whole item. There are no new nodes to audit under H12.

H5/H6/H8/H9: all choice-based definitions use uniquely normalized existence theorems;
their statements determine the map or natural isomorphism. Other definitions use
actual kernels, localization functors, canonical isomorphisms and adjunction transposes.
All delivered theorem proofs remain `sorry`; none was proved. Every declaration has
its source and blueprint docstring. The exterior theorem's proof docstring follows
the node's quotient/free-sheaf construction, flatness, normalized multiplication,
derived adjunction, counit comparison, coefficient tensor coherence, actual pairing
identification, and equality of transposes. Lines in both files are at most 100 columns.
Both node `lean.statement` fields are verbatim signatures from their delivered files.

Second-reader validation: `scompile.py NY lem-pur-support-site-comparison` compiled
both delivered files separately in dependency order, with exit 0 and no diagnostics.
The final library checks took 9.7 s for `SupportComparisonPullbackCoherence.lean`
and 14.7 s for `SupportSiteComparison.lean`, with the prescribed unchanged 60 s limit.


## Maintainer landing corrections

The independent immutable-delivery review found two mechanical landing faults,
repaired in the complete replacement modules. These corrections supersede the
earlier report's descriptions of the etale open-restriction helper.

H4/H9: `Sheaf.AlgebraicGeometry.NormalizedSupportTriangle` already declares
`AlgebraicGeometry.Etale.supportOpenRestriction`, together with its normalized
unbounded derived map `Etale.derivedSupportOpenRestriction`. The delivery's
second declaration of the former name would conflict when both modules were
imported. The replacement imports that published module and removes the four
new etale open-pullback/restriction helpers. `supportComparison_open` now
quantifies over every `U : T.Opens`, uses the existing derived map at `M.obj`,
and uses `U.ι` for the pro-etale restriction and coefficient comparison. This
is exactly restriction to every open subset in the node; it includes empty
and full opens and adds no hypothesis. Every open immersion is isomorphic
over its target to its open image. The pro-etale counit construction remains
the normalized restriction, while the etale arrow now reuses the canonical
ordinary-kernel/derived-composition construction. The primary exterior-product
signature and the mathematical DAG statement are unchanged. The merge tool's
record refitting removes the four deleted etale helper names automatically.

H6: `supportSiteComparisonSiteBaseChangeIso` contained an inline naturality
proof (`ext; simp; rfl`). Both site functors are definitionally equal. Replacing
that construction by `Iso.refl _` retains its identity components and hence
the same sectionwise direct-image comparison and adjunction mate, with no
new theorem or local proof. The dependency signature and record are unchanged.

All remaining theorem proofs are `sorry`. No definition contains `sorry`.
Both complete replacements were checked together through the prescribed
`scompile.py NY lem-pur-support-site-comparison` local side-overlay compiler,
one file at a time, with the default 60-second limit, nice 19 and two threads.
See the independent review.md for final timings and all checks.

Final maintainer validation: exit 0 without warnings or errors. The dependency
module took 10.2 s preliminary, 11.4 s sandbox and 11.4 s library; the item took
24.7 s sandbox and 18.7 s library. Final static checks also passed with the merge
tool's record refitting: the primary signatures remain verbatim, and the four
deleted etale helper names are removed from lean.declarations automatically.
