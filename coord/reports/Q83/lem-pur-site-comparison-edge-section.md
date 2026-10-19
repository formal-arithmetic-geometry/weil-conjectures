## Worker report

Item: `lem-pur-site-comparison-edge-section`, group Q83, stage 2, 2026-10-17 UTC.
Module: `Sheaf.Paper.SiteComparisonEdgeSection`.
Main declaration: `AlgebraicGeometry.ProEtale.siteComparison_edge_section`.

The module states precisely the edge-section compatibility in the node. Its only theorem
has proof `by sorry`. The eight helper declarations have actual construction data: two
abbreviations for existing terminal evaluation, two canonical derived-composition
isomorphisms, two specializations of the existing truncation spectral-object edge, and
two composites of the recorded comparison maps. There are no new independent notions,
new nodes, dependency repairs, or statement corrections. The existing landed node
`def-pc-hypercohomology-left-edge` was added to `stmt_deps` because its recorded spectral
object and target identification are used. The item's other fields are preserved.

The source is the opening paragraph of
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-a1-kummer/prop-pur-gm-relative-kummer.proof.md`.
It says that the classes and isomorphisms transport to the pro-etale site. The item is
its extracted compatibility refinement, as its source record explicitly explains.
I also read Stacks `proetale.tex`, `lemma-compare-cohomology` (099W), and
`sites-cohomology.tex`, `lemma-higher-direct-images` (072W); the adjunction normalization
is the one of Tag 0B65. I read every statement dependency's statement and recorded
signature/docstring, including the Mathlib-match record for cohomology sheaves.
The live `WeilConjectures.AlgebraicGeometry.DerivedCategories` source was obtained with
`scompile.py --source`, rather than replacing its missing older-checkout file.

Hypothesis and clause correspondence:

- Finite discrete commutative coefficients: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  `ModuleCat` has algebraic coefficients, so no non-discrete topology or additional
  topological hypothesis is introduced. This is the established fixed-coefficient
  encoding of the two recorded site-comparison interfaces.
- Schemes and the named qcqs morphism: `{U V : Scheme.{u}} (f : U ⟶ V)
  [QuasiCompact f] [QuasiSeparated f]`. There is no properness, separatedness,
  noetherianity, or nonemptiness assumption.
- Small etale and pro-etale sites: `U.smallEtaleTopology` and
  `Scheme.ProEt.topology U`, and likewise for V. Sheaves take values in
  `ModuleCat.{u + 1} Λ`. The finite-module dependency supplies the constant-ring
  realization; this uses the same fixed-ring sheaf categories as the recorded mate
  and global comparison, rather than a different intrinsic coefficient category.
- Exact comparison inverse image A_T: the existing
  `comparisonUpperStar (ModuleCat.{u + 1} Λ) T`, with its exact termwise extension
  `.mapDerivedCategoryPlus`. No arbitrary inverse image functor is a parameter.
- F is an arbitrary etale module sheaf and is placed in degree zero:
  `(F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))` and
  `(DerivedCategory.Plus.singleFunctor _ 0).obj F` throughout. The pro-etale input is
  A_U applied to precisely this object, canonically the degree-zero A_U F.
- q is any nonnegative integer: `(q : ℕ)`, coerced into the integral homology index.
- The named direct-image comparison b is exactly
  `(fixedComparisonDirectImageMatePlus Λ f).app (singleFunctor.obj F)` inside
  `siteComparisonHigherImageSectionMap`. Its dependency's qcqs theorem supplies
  invertibility, and its counit theorem fixes normalization. No comparison
  isomorphism, inverse, counit witness, or additional compatibility is hypothesized.
- The named global comparison c is `siteComparisonCohomologyMap U Λ F q`, the
  homology map of `finiteComparisonGlobalSections U Λ` at F[0]. Its only preceding
  factor is the inverse of `mapDerivedCategoryPlusIdIso`, removing the identity
  derived functor inserted by the existing base-change construction.
- The global-cohomology groups are `H^q(RΓ_U(F[0]))`, explicitly
  `DerivedCategory.Plus.homologyFunctor` applied to right-derived terminal evaluation.
  `siteComparisonEtaleSections` and `siteComparisonProEtaleSections` are transparent
  abbreviations for that exact evaluation expression, not alternative sections functors.
- Both edges use the inverse canonical Leray identification, then the existing
  `hypercohomologySpectralObjectFunctor` object's `.leftEdge q`, then
  `hypercohomologyLeftEdgeTargetIso q`. The Leray isomorphisms are constructed by
  `rightDerivedFunctorPlusCompIso'` from the established direct-image/sections
  isomorphisms and terminal-object identifications. Thus their normalization is the
  derived-unit normalization. This is the usual cocycle-to-cohomology-sheaf edge,
  not an arbitrary map having its endpoints. The existing generic
  `cochainHypercohomologyLeftEdge_cocycle` in `Sheaf.CategoryTheory.HypercohomologyEdgeCocycle`
  confirms this interpretation on nonnegative resolution complexes.
- The nonnegative-cohomology instances needed by the spectral edge are derived
  from the existing right-derived vanishing lemma; for A_U F[0], exact comparison's
  existing t-exactness supplies the input. They are construction terms, not added
  hypotheses, and do not assert that comparison preserves injectives.
- Pullback of the etale section A_V(s) is the terminal component of
  `finiteComparisonGlobalSectionsUnit V Λ`, i.e. the actual comparison-adjunction
  unit. Under the constant-unit identification this is precisely section pullback.
- The exact identification A_V H^q(Ru_*F) -> H^q(A_V Ru_*F) is explicitly the `.hom`
  component of `mapDerivedCategoryPlusHomologyFunctorIso q`, evaluated on Ru_*F.
  This factor precedes homology of the named b, both evaluated on V_proet.
- The conclusion quantifies over `(x : H^q(RΓ_U(F[0])))` and equates exactly
  `siteComparisonProEtaleEdge ... (siteComparisonCohomologyMap ... x)` with
  `siteComparisonHigherImageSectionMap ... (siteComparisonEtaleEdge ... x)`.
  The right helper expands to A_V(s), the exactness identification, then Γ H^q(b).

Dependency declarations used:

| Node / module | Declarations and role |
| --- | --- |
| `def-weil-pbc-derived-categories`; `WeilConjectures.AlgebraicGeometry.DerivedCategories` | The recorded `DerivedCategory.Plus` and cohomology conventions on fixed-ring etale sheaves. |
| `def-weil-pbc-proetale-modules`; `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules` | The constant-ring/fixed-ring module realization used by the comparison APIs. |
| `def-weil-pbc-site-comparison-morphism`; `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison` | `AlgebraicGeometry.ProEtale.comparisonUpperStar`, `comparisonAdjunction`. |
| `lem-sf-comparison-pullback-exact`; `Sheaf.Paper.ComparisonPullbackExact` | `AlgebraicGeometry.comparisonPullbackExact` and the exact comparison structure, used through the existing exact-functor homology and t-exactness APIs. |
| `lem-weil-pbc-comparison-direct-image-canonical-mate`; `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate` | `fixedComparisonDirectImageMatePlus`, its qcqs invertibility and its specified counit normalization. |
| `lem-weil-pbc-comparison-global-cohomology`; `Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized` | `finiteComparisonGlobalSectionsUnit`, `finiteComparisonGlobalSections`, `isIso_finiteComparisonGlobalSections`. |
| `def-weil-derived-cohomology-sheaves`; Mathlib `Algebra.Homology.DerivedCategory.HomologySequence` | The recorded `DerivedCategory.homologyFunctor`, restricted by `DerivedCategory.Plus.homologyFunctor`. This dependency is already a Mathlib leaf and requires no replacement record. |
| Added landed `def-pc-hypercohomology-left-edge`; `Sheaf.CategoryTheory.HypercohomologyLeftEdge` | `Functor.hypercohomologySpectralObjectFunctor`, `Functor.hypercohomologyLeftEdgeTargetIso`, and the first-quadrant instance. |
| Etale and pro-etale `UpperLowerStar.GlobalSections` upstream modules | `Etale.lowerStarCompGlobalSectionsIso`, `ProEtale.globalSectionsLowerStarIso`; `Scheme.Etale.isTerminalMkId`, `Scheme.ProEt.isTerminalMkId`. |
| Upstream derived-composition and exact-functor APIs, available through those imports | `Functor.rightDerivedFunctorPlusCompIso'`, `Functor.mapDerivedCategoryPlusIdIso`, `Functor.mapDerivedCategoryPlusHomologyFunctorIso`, and t-exactness. |

The fixed-coefficient pro-etale operations used in Step 2 are already in the upstream public imports.
The etale direct-image module is already imported by the public global-sections module.
The proof-only imports for comparison-pullback coherence, universe-general K-injective
resolutions, and adjunction mates were removed during repair because they were not used
by the statement and pushed the library file over the per-file timeout; all declarations
needed by the statement remain supplied by the public imports.
The recorded proof-only
`WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension` and
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` cannot coexist
with the required finite-coefficient imports: the wrapper reports both Iso modules
already declaring `AlgebraicGeometry.ProEtale.upperStarIsoLowerStarInv`. I removed these
proof-only imports as authorized by the launcher's duplicate-import repair instruction.
The terminal-evaluation comparison is already supplied in the compatible public
`ComparisonGlobalCohomologyFiniteNormalized` interface used here. No live file or
recorded dependency was edited.

Edge cases checked before writing and again on rereading: q=0 (the spectral edge and
its target identification include zero); zero sheaf; the zero commutative ring (no
`Nontrivial` hypothesis); f the identity (no invertibility or nonidentity exclusion);
empty U and empty V where a morphism exists (no points or nonempty coverings chosen).
The construction applies to arbitrary sheaves, without local constancy or
constructibility. There is no boundedness assumption beyond the actual F[0] and its
right-derived images. No statement fault or dispute was found.

Searches, performed with the prescribed tools:

- `msearch.py ... leanfinder`, query: "Etale pro etale comparison of higher direct
  images commutes with the Leray edge map to sections of the cohomology sheaf."
  Eight hits concerned general site restriction/sheafification, none this comparison.
- `msearch.py ... loogle`, query: `"edge", "comparison"`: zero hits.
- `msearch.py ... grep`, query: `edge.*[Cc]ohomology|[Cc]ohomology.*edge|[Ll]eray`
  in Mathlib `CategoryTheory`: zero hits.
- `msearch.py ... leansearch`, query: "Etale pro etale comparison preserves the edge
  map from global cohomology to sections of higher direct images."
  Eight hits concerned formally etale algebras, etale morphisms, their base-change
  instances, and `Scheme.Etale`; no edge comparison statement.
- `rg` in the old upstream `WeilConjectures`, shared `lean/Sheaf`, and upstream-name
  index for edge, Leray, and comparison names: no matching statement. The upstream
  node-id search likewise returned no declaration. Shared generic hypercohomology
  edge definitions were found and reused. The shared Leray edge modules for
  `RingedSpace.moduleCohomology` concern Zariski structure-sheaf modules, not this
  etale/pro-etale fixed-ring comparison; they are not a match. Exact new helper
  names were also searched in Mathlib, both project source trees and the upstream
  name index, with no collisions.

Validation uses only `scompile.py`, first for API probes under `scratchpad/`, then for
the delivered module. The final dry run and delivery use `deliver2.py`. No global
build, direct Git command, prohibited preflight invocation, or shared-file edit was made.

## Second reading by Q83

Per the dispatcher instruction, no other agent was started. This section records a
separate self-review with the node, source and completed module open; the maintainer's
independent delivery review remains the independent check.

I reread each hypothesis and every displayed map in the node against the signature
and unfolded helpers. The finite coefficient and qcqs assumptions are all present;
no extra hypothesis is present. I checked the direction of each Leray isomorphism
(the inverse goes from cohomology on U to the composite on V), the direction of the
exact-homology isomorphism (A_V H^q -> H^q A_V), and that homology is taken of the
recorded counit-mate component, rather than an unspecified isomorphism. The global
comparison removes the derived identity by its inverse before applying the recorded
unit-based map. Both sides consequently have exactly the pro-etale higher-image
section target. The element binder gives the node's every-x assertion directly.

Rereading found no mathematical statement mismatch. Compilation exposed a duplicate
proof import, an invalid line break in field notation, and two unused bound-index
names; these were repaired without changing the statement. I checked that the only
`sorry` is the named main theorem and that all helper definitions have actual data.
The generic edge is reused, not redefined; the added statement dependency records it.
The report does not claim a proof of the stage-2 theorem or a separate-agent review.

Final compile result after the timeout repair: the prescribed `scompile.py Q83 lem-pur-site-comparison-edge-section`
check passed for the delivered file, with sandbox compilation (29.3 s) and library-path
confirmation (60.5 s), with no errors or warnings. These are file-only wrapper checks.
