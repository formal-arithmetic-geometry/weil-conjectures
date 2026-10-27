## Worker report

The main module states Stacks Tag 09T6 (perfect-lemma-argument-proves), exactly
with the unit normalization specified by the DAG. Nothing is proved: the main
theorem and the dependency-interface closure theorem have `sorry` proofs. The
auxiliary declarations are actual full-subcategory lifts, inherited
additivity, and canonical termwise composition isomorphisms. They belong to the
owning node's inclusions and direct-image notation, not independent notions.

Clause-by-clause correspondence:

- A scheme X is `X : Scheme.{u}`; quasi-compact and quasi-separated are
  `[CompactSpace X] [QuasiSeparatedSpace X]`. The latter is equivalent to
  quasi-separatedness of the structure morphism by Mathlib's
  `quasiSeparated_iff_quasiSeparatedSpace`.
- For every T, A_T is the existing
  `(SheafOfModules.isQuasicoherent T.ringCatSheaf).FullSubcategory`, not a
  copied category. Its inherited addition and abelian structure are Mathlib's
  `ObjectProperty` full-subcategory structures. The dependency repair exposes
  closure under ambient kernels, cokernels and finite products and exactness of
  the inclusion. Those are established conclusions for arbitrary schemes,
  not extra hypotheses of this criterion.
- The two families `[HasDerivedCategory.{wA} ...]` and
  `[HasDerivedCategory.{wM} ...]` choose unbounded localizations with independent
  morphism universes; their objects are the given full subcategory and ambient
  module-sheaf category. There is no boundedness assumption.
- I_T is always the exact full inclusion's `.mapDerivedCategory`. The conclusion
  uses `(schemeDerivedQCohProperty X).lift` to corestrict that same functor,
  with `h` certifying quasi-coherence of its cohomology. The resulting functor's
  `.IsEquivalence` is precisely the requested equivalence, not merely existence
  of some equivalence between the categories.
- Affine opens and their inclusions are `U : X.affineOpens` and `U.1.ι`.
  `RingedSpace.moduleDirectImage U.1.ι.toLRSHom.toShHom` is the actual module
  direct image, and `schemeDerivedDirectImage U.1.ι` is its recorded unbounded
  K-injective right derived functor.
- Hypothesis (a) is `hQC`. `quasiCoherentModulePushforward` restricts that
  very functor using `ObjectProperty.lift`; its additivity instance is inherited.
- Hypothesis (b) is the family `hDerived`, whose witnesses in
  `DerivedInclusionSquareData` contain `Phi`, `eta`, and `universal`. For every G the function sending beta to
  `eta ≫ Functor.whiskerLeft DerivedCategory.Q beta` is bijective. This is
  the universal property in def-sfb-right-derived-functor, expressed on complexes
  as in this item's statement (equivalently on the homotopy category). It does
  not assume K-injective resolutions in A_U and does not substitute the
  resolution-dependent definition for an arbitrary universal pair.
- Hypothesis (c)'s natural isomorphism is the `comparison` field. For every complex F,
  its `compatible` field starts at Q of the underlying j_*F; the inverse exact-inclusion
  factorization, the image of eta, c, and the exact-inclusion factorization
  at U give its comparison to Rj_* of the localization of the underlying F.
  This composite equals Q of `quasiCoherentPushforwardComplexIso` followed by
  `moduleDirectImageDerivedComparison`. The first is the canonical termwise
  full-inclusion interchange. The second is defined, with actual data, from the
  recorded rightDerivedFunctorUnit, transported from the homotopy category via
  mapHomotopyCategoryFactors and quotientCompQhIso. For every ambient resolution
  s:F -> J, naturality of that unit, and its invertibility at K-injective J,
  identify this map with Q(j_*s) followed by the inverse canonical computation
  isomorphism. Thus this is precisely the resolution-normalized map in (c),
  expressed without an unnecessarily unfolded K-injective target. No arbitrary
  map, isomorphism choice or resolution hypothesis on A_U is introduced.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Mathlib.Topology.Defs.Filter: CompactSpace.
- Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated: QuasiSeparated and
  quasiSeparated_iff_quasiSeparatedSpace.
- Sheaf.AlgebraicGeometry.CoherentFiniteType: exposes
  SheafOfModules.IsQuasicoherent / isQuasicoherent from Mathlib, as recorded in
  pqf-def-coherent; finite type and coherence are not imposed here.
- Sheaf.CategoryTheory.RingedSiteModules: ringedSiteModules is exactly
  SheafOfModules, whose standard scheme specialization is used here.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory,
  HasDerivedCategory, Q and quotientCompQhIso.
- WeilConjectures.AlgebraicGeometry.DerivedCategory: schemeDerivedCategory,
  schemeDerivedQCohProperty and schemeDerivedQCohCategory (publicly reexported
  through SchemeDerivedDirectImage).
- Mathlib.AlgebraicGeometry.OpenImmersion: IsOpenImmersion; the canonical
  open-subscheme inclusion is U.1.ι.
- Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions: read the
  universal property of rightDerivedFunctorOfQuasiIsoResolutions and its Unit,
  universal, unique and ObjIso declarations. Here the same universal property
  is imposed directly on Phi, because the item explicitly assumes no
  K-injectives in the quasi-coherent subcategory.
- WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage:
  moduleDirectImage, derivedModuleDirectImage and its resolution computation;
  WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage:
  schemeDerivedDirectImage; the latter is the exact ringed-space specialization.
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective:
  Functor.rightDerivedFunctorObjQIso, whose definition is the inverse derived
  unit at a K-injective, with quotient/Qh comparisons.
- WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel:
  Scheme.Modules.isQuasicoherent_kernel;
  WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage:
  Scheme.Modules.quasiCoherent_cokernel_image;
  WeilConjectures.AlgebraicGeometry.Cohomology.QuasicoherentExtension:
  Scheme.Modules.isQuasicoherent_biprod.
- Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor:
  Functor.mapDerivedCategory, mapDerivedCategoryFactors, their integer-shift
  structure and triangulated instances; this is the recorded mathlib_match of
  lem-weil-pbc-exact-functor-derived-factorization.
- Sheaf.AlgebraicGeometry.QuasiCoherentGrothendieckGenerators:
  quasiCoherent_grothendieck_generators and the exposed induced-structure clauses.

The stated proof dependencies are plain imports: SchemeDerivedCoheratorAdjunction,
SupportedOpenUnitConeProperties, DerivedOpenRestrictionMaps, the Mathlib triangle
isomorphism theorem and finite affine-cover theorem. The flat coherator interchange
and affine coherator nodes have no Lean record or mathlib_match in this checkout;
they are proof-only prerequisites, so no fictitious imports or restatements were
added. The full seven-step proof plan is in the main theorem's docstring.

Edge cases checked: empty X and empty affine opens are included; no nonempty
binder or chosen cover is assumed. Zero complexes and identity resolutions are
included, with no monomorphism required of a resolution. All degrees are integers and all
complexes and derived functors are unbounded. X need not be separated, affine,
Noetherian or have affine intersections. The two localization universes are
independent; all scheme and sheaf carriers use the project's fixed universe u.
No added geometric hypothesis or statement correction is needed.

Searches for an existing statement (2026-10-24):

- msearch.py leanfinder: "The derived inclusion of quasi coherent modules is an
  equivalence if compatible with derived pushforward from every affine open".
  Eight hits: derived localization/essential-surjectivity, quotientCompQhIso,
  exact-functor factorizations, isQuasicoherent and affine Zariski sheaf
  equivalence. None is this geometric criterion.
- msearch.py loogle: "Functor.mapDerivedCategoryFactors,
  SheafOfModules.IsQuasicoherent" reported unknown identifier for the unqualified
  first name; repeated with `"Quasicoherent", "equivalence"`: zero hits.
- msearch.py grep: `coherator|quasi.?coherent.*derived`: zero Mathlib hits.
- rg in lean/WeilConjectures and lean/Sheaf for the item id: no hits. Searches
  for coherator / derived quasi-coherence found the derived-cohomology full
  subcategory, ambient coherator constructions, unrelated algebraic-space
  versions, and the newly landed Grothendieck and derived coherator interfaces.
  Read those relevant modules; none states the affine-open criterion.
- rg for all four proposed declaration names in Mathlib, upstream, Sheaf and
  dag/lean_names_upstream.json: no conflicts.

## Dependency modules

lem-sfb-qcoh-grothendieck-generators: its existing theorem returns an existential
`Abelian` witness and exactness, but does not expose closure instances or identify
that witness's preadditive structure definitionally with ambient addition. Using
an arbitrary witness produced incompatible zero-morphism structures in the
complexes and prevented additive inclusion inference. Under §1(B), preserve its
existing declaration verbatim and expose the induced-abelian closure/exactness
clauses of the very same node as `quasiCoherent_inducedAbelianClosure`, together
with projection instances. Mathlib then constructs the induced abelian structure
with the standard ambient addition. This is not a new mathematical assumption,
a second category, or a choice from an undetermined existence theorem. The item
adds this already-landed node to stmt_deps. Only lean changes in that dependency's
node record. Both files are compiled separately through scompile.py.

## Second reading by Q117

Author self-check only: the dispatcher explicitly prohibits starting another
agent; the maintainer supplies the independent mathematical review. Re-read the
DAG, Tag 09T6 and the final signatures. The qcqs binders, entire universal
unbounded pair, all affine opens, natural c, resolution-normalized equation and
exact lifted inclusion equivalence correspond clause for clause as above.
The initial arbitrary abelian-structure binders and closure hypotheses were
removed by exposing the induced structure through the dependency interface.
The canonical right-derived unit and explicit termwise composition isomorphisms
replaced costly implicit unfolding;
these insert canonical identities, not new assumptions. The statement and
proof fields of both nodes remain unchanged. No STATEMENT-DISPUTED flag.

The final signature packages the pointwise normalization equation in
`DerivedInclusionSquareCompatible`, which is defined by precisely the equation
printed above and introduces no extra field or hypothesis. The `hDerived` family asserts existence of the universal pair and comparison
for every affine open, exactly as hypotheses (b) and (c) do. The
`DerivedInclusionSquareData` fields are `Phi`, `eta`, `universal`, `comparison`,
and `compatible`; no resolution assumption is added. The supplied parameters
are the actual termwise inclusion, direct image, exact localization comparisons,
Phi, eta, c, and canonical module-derived comparison. The helpers
`quasiCoherentDerivedInclusion`, `quasiCoherentDerivedInclusionFactors`, and
`quasiCoherentAmbientDerivedPushforward` transparently name the already recorded
functors and isomorphism, with explicit independent localization universes. They
avoid expensive inferred definitional equalities; they do not replace any existing
construction by arbitrary data. Every helper is recorded in lean.declarations.

Validation: scompile.py compiled both delivered modules separately, including
library-name compilation of the main module (37.5 seconds) and dependency
(9.5 seconds). The final interface retains all mathematical hypotheses and
uses transparent abbreviations for existing functors to keep elaboration within
the fixed time limit. No test or global build was run.
