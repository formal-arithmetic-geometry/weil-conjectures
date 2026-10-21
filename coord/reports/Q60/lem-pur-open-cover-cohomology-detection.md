## Worker report

The module `Sheaf.AlgebraicGeometry.OpenCoverCohomologyDetection` states the complete
node as ten named theorem clauses, all with `sorry` proofs. Its primary declaration
is `AlgebraicGeometry.OpenCoverCohomology.cohomology_detection`. The other declarations
are transparent dispatchers to existing site/module constructions, actual canonical
isomorphisms, and exactness instances obtained by projecting named exactness theorems.
No definition has postponed data. Every postponed theorem belongs to this node and
has a source and the corresponding natural-language proof in its docstring.

### Hypotheses and clauses

- The scheme is `T : Scheme.{u}`. `b : Bool` selects exactly the two sites: `false`
  is `T.Etale` with `T.smallEtaleTopology`, and `true` is `T.ProEt` with
  `Scheme.ProEt.topology T`. `Site`, `siteCategory` and `topology` dispatch directly
  to those recorded definitions, without reconstructing either site or topology.
- The coefficient ring is `A : Type (u + 1)` with `[CommRing A] [Finite A]` in the
  theorem clauses involving coefficients. `coefficients` is the recorded
  `constantSheaf` applied to `CommRingCat.of A`; `rings` forgets only commutativity.
  The constant sheaf is therefore actually sheafified, never the constant presheaf.
- All coefficients and section modules use the common universe `u + 1`.
  `siteEssentiallySmall` is inherited from each site. No equality of the site object
  universe `u + 1` with its morphism universe `u` is imposed. The common-universe
  sheafification and abelian instances are synthesized from these standard sites.
- `Modules` and `LocalModules` are the dependency's `ringedSiteModules`, hence
  precisely Mathlib's `SheafOfModules`, over `rings` and its `Sheaf.over` restriction.
  In the derived clauses the binders are
  `[HasDerivedCategory.{w} (Modules T b A)]` and
  `[∀ U : T.Opens, HasDerivedCategory.{w} (LocalModules T b A U)]`.
  These choose the ordinary unbounded localization in the stipulated size universe;
  they do not assert boundedness, constructibility or injective resolutions.
- An arbitrary set-indexed open cover is `{I : Type v} (U : I → T.Opens)` and
  `(hU : ∀ x : T, ∃ i : I, x ∈ U i)`. In particular `v` is independent of both
  the scheme universe `u` and the derived morphism universe `w`. There is no
  `Finite I`, `Nonempty I`, quasi-compactness, separation or characteristic assumption.
- For every open, `localization T b U` is exactly the recorded equivalence from the
  slice to the small site of U: `Scheme.Etale.overEquiv` or `Scheme.ProEt.sliceEquiv`.
  Its inverse is the functor named in the node, sending an object over U to its
  composite over T with its factorization through U. In `site_and_coefficients`,
  the first conjunct identifies covering sieves, the second identifies the
  underlying-scheme functor on objects AND arrows, and the third identifies the
  composite structural morphism. `HEq` there only accommodates the definitionally
  different domain presentations; the preceding functor equality identifies them.
- The fourth conjunct is the equality of the two functors into the slice for
  nested opens: the direct inverse localization followed by `Over.map` equals
  composition of `siteMap (T.homOfLE h)` and inverse localization at U. This states
  the iterated site identification, including its specified actual functors.
- `coefficientComparison` and `nestedCoefficientComparison` are real constructions:
  the existing `pushforwardContinuousSheafificationCompatibility` evaluated at the
  constant presheaf. The fifth conjunct is its unit equation at every slice object,
  so each constant section a is unchanged. The sixth gives the actual coefficient
  isomorphism on the small site of U, with its underlying presheaf identified with
  the restricted coefficient sheaf and the same unit normalization at every object.
  The seventh is the equality of the direct coefficient comparison and the nested
  composite, using `Sheaf.pushforwardOverMapIso` for the canonical scalar transport.
- `restriction` is precisely `SheafOfModules.overFunctor`. Its target is the
  localized ringed site. This is the chosen slice presentation of the small site
  of U under `site_and_coefficients`, not another module category. Consequently
  these are exactly the r_U of the node under its explicitly stated identification
  of sites and coefficients. `restriction_sections` states additivity, preservation
  of finite limits and colimits, literal equality of section modules at V/U, and
  equality of sectionwise linear morphisms. The actions and presheaf maps are those
  of the existing restriction definition, so no independent scalar structure is chosen.
- `furtherRestriction` is the existing `SheafOfModules.overMap` along `nestedArrow`.
  `furtherRestriction_exact` states its exactness for nested opens.
  `restriction_nested` says that the existing `overFunctorMap` relocalization
  comparison is sectionwise the identity. The corresponding instances use these
  proof-valued exactness facts; they introduce no arbitrary module or map.
- `covering` states the open family covers the terminal site object. Its next
  conjunct states that the actual site pullback family covers EVERY site object V.
  The third states that the preimage Zariski family covers on the small site of
  the underlying scheme of V. The fourth states that the same pullback family,
  as objects over V, covers in the localized topology at `Over.mk (𝟙 V)`.
  These are scheme-theoretic pullbacks through the existing site's finite limits.
- `derivedRestriction` is exactly `(restriction ... U).mapDerivedCategory`, the
  dependency's termwise functor on the unbounded localization.
  `chi` is the actual existing `mapDerivedCategoryHomologyFunctorIso` in direction
  r_U H^a → H^a D(r_U). It is a natural ISO, never a bare existence of unrelated
  component isomorphisms. `cohomology_comparison` explicitly gives naturality for
  EVERY derived morphism and its four-factor normalization on EVERY complex C:
  homology factors through Q, the inverse kernel/image/quotient comparison,
  inverse target homology factorization, and the termwise-functor factorization.
  The kernel/image/quotient comparison is the existing canonical upstream
  `mapHomologicalComplexHomologyIso`, read in the same exact-functor module.
- `derivedNestedIso` is the composite of the inverse derived composition iso with
  the derived image of the actual sectionwise `overFunctorMap`. `cohomology_nested`
  equates the composite comparison for U followed by W/U, transported by this iso,
  to the direct comparison for W transported by the ordinary relocalization iso.
  It quantifies over all integers and all derived K.
- `module_detection` is exactly `IsZero F ↔ ∀ i, IsZero ((restriction ... (U i)).obj F)`.
  `cohomology_detection` applies the same criterion to the genuine derived
  `homologyFunctor` in each integer degree a. Its right side is the cohomology
  sheaf of the derived restriction, not just the ordinary restriction of an
  unspecified representative.
- `empty_modules` explicitly states that every module sheaf is zero when
  `[IsEmpty T]`. Empty covering families are already allowed in both detection
  statements, without a separate nonemptiness assumption.

### Dependency declarations used

The full signatures and docstrings of the recorded interfaces were read from the
read-only Lean sources.

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms.
- `Mathlib.AlgebraicGeometry.Sites.Etale` (and Morphisms.Etale):
  `Scheme.Etale`, `Scheme.smallEtaleTopology`, open-immersion etaleness and the
  jointly-surjective covering description.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`,
  `Scheme.etalePrecoverage_le_proetalePrecoverage`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  its category and abelian structures remain the Mathlib structures.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`, `DerivedCategory.homologyFunctorFactors`.
  The general construction is the dependency node's recorded Mathlib match.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous` and
  `Mathlib.CategoryTheory.Sites.Over`: `SheafOfModules.overFunctor`, `overMap`,
  `overFunctorMap`, `GrothendieckTopology.over`, `Sheaf.over`, `pushforwardOverMapIso`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`:
  `Scheme.Etale.overEquiv`, its concrete inverse and topology instances.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`:
  `Scheme.ProEt.sliceEquiv`, its actual `sliceFrom`, and `weaklyEtale_localization`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`:
  `SheafOfModules.localizedSystemExact`, at site universes u+1,u and coefficients u+1.
- `Mathlib.CategoryTheory.Sites.CoverLifting`:
  `Functor.pushforwardContinuousSheafificationCompatibility` and its unit equation;
  `Mathlib.CategoryTheory.Sites.Sheafification`: `toSheafify`, the universal property.
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`: the canonical
  homology comparison of an exact functor.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `mapDerivedCategoryHomologyFunctorIso`, its complex normalization,
  `mapDerivedCategoryCompIso`, `mapDerivedCategoryNatIso`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: the recorded general site/covering
  interface retained as a proof import.

### Sources and edge cases

Read the local Stacks source at sites-modules.tex, definition-localize-ringed-site
04IX, especially (4), and the following restriction/extension descriptions; and
sites.tex, definition-sheaf-sets 00VM, definition-sheaf 00VR and the adjacent
empty-cover remark. The node's eight proof steps are distributed among the theorem
docstrings: covering; localization; coefficient sheafification and its unit;
sectionwise exactness; localization of the homology comparison; nested coherence;
sheaf equalizer zero detection; application to cohomology and the empty scheme.

Checked T empty with I empty, U empty, U=T, nested equal opens, repeated and empty
cover members, arbitrary infinite covers of a non-quasi-compact scheme, the zero
coefficient ring, arbitrary unbounded complexes, negative/zero/positive degrees,
and all derived morphisms (including inverse quasi-isomorphisms). None requires
an extra hypothesis or a statement correction. The arbitrary index universe was
made independent of the derived morphism universe during the self-check.

### Searches

All services were invoked through the authorized batch2 `msearch.py` wrapper.

1. LeanFinder: `Restriction of module sheaves to an open cover of etale and proetale
   sites is exact commutes with derived cohomology and detects zero sheaves`.
   Eight hits, including MayerVietorisSquare exactness and SheafOfModules.instAbelian;
   no combined statement for both ringed sites and coherent normalized comparisons.
2. Loogle: `DerivedCategory.homologyFunctor, SheafOfModules.overFunctor`.
   Zero hits. The relevant declarations were then read directly from their sources.
3. Mathlib grep: `overFunctor|mapDerivedCategoryHomologyFunctorIso` in
   Algebra/Category/ModuleCat. Five hits: overFunctor, over, Hom.over and
   overFunctorMap in Sheaf/PushforwardContinuous. These are reused directly.
4. LeanSearch: `Exact restriction of module sheaves on etale and proetale sites
   commutes with unbounded derived cohomology and detects zero on every Zariski
   open cover`. Eight hits, mostly Scheme.Modules.restrict and its composition
   API (structure-sheaf modules on the Zariski site), plus SheafOfModules.over and
   hasLimitsOfShape. No exact match for this node.
5. `rg` of the upstream WeilConjectures and project Sheaf trees for open-cover,
   localization, overEquiv and vanishing/restriction patterns found the existing
   EtaleOver and ProEtaleWeaklyEtaleLocalization interfaces and the upstream
   ProEtale/FiniteCoefficient/Derived/OpenCover. The latter proves pro-etale
   sheaf/complex zero detection for coefficients in an abelian category; it does
   not state the two-site ringed/module coefficient comparison and coherence
   assertions here. Its general canonical derived-homology API is reused.
6. Direct search for the blueprint node id in WeilConjectures found no declaration.
   The chosen namespace and declaration names do not occur in the read library.

No STATEMENT-DISPUTED flag and no change to the item statement, proof or dependency
lists. No new independent notion is needed: all helper definitions dispatch to
existing constructions for the same objects already named in this node.

Validation: the module was compiled cleanly through `scompile.py`, both as the
server sandbox module and with its actual library module name. Final delivery
preflight and per-file compilation passed in the final dry run.

## Dependency record retained

`def-weil-derived-cohomology-sheaves` is restored byte-identically to the live
repository. Its landed `lean` record remains owned by N5 and points to
`Sheaf.Paper.SfCommonStageWeilCohomology`, with all twelve declarations retained.
This item directly uses the node's existing `mathlib_match`,
`DerivedCategory.homologyFunctor`, together with `homologyFunctorFactors` from
`Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`. The item's `lean.note`
records this use. No dependency record is rebound and no dependency module is added.

## Second reading by Q60

This is the isolated worker's clause-by-clause self-check; the dispatcher's brief
reserves the independent delivery review to the maintainer and forbids starting
another agent. No independent worker reading is claimed.

Reopened the node statement and all 491 lines of the delivered module. Verified
both Boolean branches use the recorded categories and topologies, all site and
coefficient identities are actual specified constructions, and both direct and
nested comparisons retain their normalization. Checked that the restriction
codomain is the explicitly identified slice presentation of the requested small
site with its restricted constant ring. The pullback-cover theorem has separate
clauses for the site over T, the small site over V, and the localized site. The
cohomology isomorphism is a canonical natural iso with its representative formula,
and the nested equation contains both ordinary and derived relocalization
transports. Both directions of both detection criteria and the empty-scheme
assertion are present. The helper exactness theorem is proof-valued and gives no
hollow data. The adjustments in this reading were separating the index
universe v from the derived morphism universe w and adding `include hFinite`
to retain the explicit finite-ring hypothesis in the derived theorem clauses
even when Lean would otherwise omit that unused section instance. The general
cohomology functor used here is already in the dependency node's mathlib_match;
its landed primary interface is retained unchanged.

The first deliver2.py --no-push preflight passed with clean compilation. A final
binder audit then retained `[Finite A]` explicitly using `include hFinite`; the
final dry run validated that version: OK, commit 0123f7e7112, preflight and
all compiles clean. The item node differs from the read repository only in `lean`; the dependency
node copy is byte-identical to live.

## Returned-delivery repair

For the H13/H4 return on immutable head `300f659a9d5f`, restored the complete
`def-weil-derived-cohomology-sheaves.json` byte-for-byte from live, retaining N5's
landed module and twelve owned declarations. Added the explanation of direct
Mathlib-match use only to the item's `lean.note`. The item module is unchanged.
The previous record replacement is withdrawn.

For advisory H9, re-read the proof dependencies and the module's plain imports.
`Sheaf.CategoryTheory.SiteCoveringAxioms` is the recorded proof-plan interface
for `def-weil-pbc-sites-and-cohomology`. `CoverLifting`, `Sheafification`, and
`ShortComplex.PreservesHomology` supply the recorded canonical coefficient and
homology comparison interfaces. `AffineEtale` supplies the site size and topology
infrastructure. The unchanged module, including all these plain imports, passed `scompile.py`
under both the sandbox module name (9.6 seconds) and the library module name
(16.3 seconds), with no errors or unexpected warnings. The saved-packet initial
dry run also passed; the final dry run checks the restored dependency metadata.
