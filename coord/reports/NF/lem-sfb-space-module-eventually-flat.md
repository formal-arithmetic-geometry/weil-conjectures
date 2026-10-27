## Worker report

Stated `AlgebraicGeometry.AlgebraicSpace.module_eventually_flat_of_affineLimit` in
`lean/Sheaf/AlgebraicGeometry/SpaceModuleEventuallyFlat.lean`. Its only postponed proof
is the whole named theorem (`sorry`); there are no new definitions, helper axioms,
new nodes, dependency-module repairs, or mathematical statement corrections. The node copy changes
`lean` and adds the landed definition owners to `stmt_deps` as expressly requested
by the maintainer return. No theorem is proved in this stage.

Read Stacks `spaces-limits.tex`, Situation 084W (situation-descent-property), lines
1449–1457, and Tag 08K0 (lemma-descend-flat), lines 1752–1800. This is its module
assertion specialized as the node specifies to affine bases and a finitely presented
source morphism. The conclusion at every later stage is the persistence clause of
Tag 05VW, or directly the persistent conclusion of the affine descent lemma in the
accepted node proof. No Noetherian assumption is introduced.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Schemes, algebraic spaces and small étale structure modules: `Scheme.{u}`,
  `AlgebraicSpace`, and `X0.Modules`, using the recorded framework. The ambient scheme
  is explicitly `Spec (.of (ULift.{u} ℤ))`. The lift realizes Spec Z in the scheme
  universe and imposes no characteristic assumption. The ring sheaves are the actual
  existing regular-function sheaves, never substituted coefficient objects.
- Size convention: explicit universe `u`, with `I : Type u`, `Scheme.{u}` and the
  existing small-site/module encodings. No independent too-small index universe,
  test universe, or equality of site object and morphism universes is imposed.
- Small nonempty directed set: `[Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]`.
  The preorder presentation permits the usual partially ordered directed sets and
  equivalent repeated indices. No total ordering or countability is assumed.
- Inverse system of affine schemes: `D : Iᵒᵖ ⥤ Over (Spec (.of (ULift.{u} ℤ)))`,
  with `haff : ∀ i, IsAffine (D.obj i).left`. Its transition arrows go from later
  indices to earlier ones: `D.map (homOfLE hij).op`.
- Affine transitions: `htrans` requires `IsAffineHom (D.map a).left` for every arrow.
  This is the hypothesis expressly given by the node (also automatic between affine
  schemes), not a transition-flatness or transition-surjectivity assumption.
- Limit T: `c : Cone D` and `hc : IsLimit ((Over.forget _).mapCone c)` specify the
  actual scheme limit, with underlying scheme `c.pt.left` and its cone projections.
  A scheme limit is used, rather than assuming a potentially weaker pointwise limit.
- Initial index: `i0 : I`; initial source and morphism: `X0` and
  `f0 : X0 ⟶ schemeSpace (D.obj (op i0))`.
- Finite presentation of f0 is expanded into exactly its three parts: `hqc` is
  `MapIsQuasiCompact f0.hom.hom`; `hqs` is `MapIsQuasiSeparated f0.hom.hom`, the landed predicate for
  quasi-compactness of its relative diagonal;
  `hlfp` is `MapIsLocallyOfFinitePresentation f0`. These use the existing predicates
  on scheme tests and étale charts. In particular, no separatedness is substituted
  for quasi-separatedness. `MapIsQuasiCompact` uses quasi-compactness of the point
  space, equivalent to existence of a quasi-compact scheme atlas for an algebraic
  space. The diagonal is representable because X0 and its target are spaces.
- Initial quasi-coherent finitely presented module: `M0 : X0.Modules`,
  `hMqc : M0.IsQuasicoherent`, and `hMfp : M0.IsFinitePresentation`. Both are Mathlib's
  existing sheaf-module predicates, with the slice instances supplied by the recorded
  quasi-coherent-module dependency. The latter means an étale-local finite free
  presentation, and not merely finite generation of global sections.
- The stages Xi and maps fi and p are indexed by `{i : I // i0 ≤ i}`. `sq i` is the
  presheaf `IsPullback` square whose bottom arrow is exactly
  `yoneda.map (D.map (homOfLE i.property).op)`. Thus these are the specified
  X0 ×_{T_i0} T_i, with the two actual projections, up to their unique canonical
  isomorphism. The square conditions are universal properties, not arbitrary maps.
  The stage i=i0 and identity transition are included.
- Likewise `X`, `q`, `f`, and `sqLimit` specify X0 ×_{T_i0} T and its projections,
  using precisely `yoneda.map (c.π.app (op i0))` as the bottom arrow.
- Mi and M are written directly as `(moduleTensorPullback (p i)).obj M0` and
  `(moduleTensorPullback q).obj M0`. These are the recorded canonical tensor
  pullbacks with their specified direct-image adjunction, not independently chosen
  modules or derived pullbacks. There is no extra isomorphism hypothesis on them.
- Limit relative flatness is exactly
  `hflat : ModuleIsFlatOver f ((moduleTensorPullback q).obj M0)`, using the landed
  predicate from `def-sfb-space-flat-proper-coefficient`. Its definition quantifies
  over every compatible pair of étale scheme charts of the source and target and
  requires the Zariski restriction of the module to be flat over the target chart.
  For quasi-coherent modules this is equivalently relative geometric-stalk
  flatness, as recorded in that definition node and Stacks 05VU. No separately
  spelled-out chart predicate occurs in this theorem's signature.
- Conclusion: `∃ (j : I) (hij : i0 ≤ j), ∀ (k : I) (hjk : j ≤ k), ...`. In each
  occurrence the stage is exactly `⟨k, hij.trans hjk⟩`. The conclusion is
  `ModuleIsFlatOver (fi ⟨k, hij.trans hjk⟩)
    ((moduleTensorPullback (p ⟨k, hij.trans hjk⟩)).obj M0)`.
  The same landed predicate is applied to the stage's second projection and the
  tensor pullback along its first projection. This says geometric-stalk flatness
  over T_k for every k≥j, with one common j.

Dependency declarations used (read their full declarations and accompanying docs):

- `def-pc-scheme`: Mathlib.AlgebraicGeometry.Scheme,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-trf-algebraic-space`: Sheaf.AlgebraicGeometry.AlgebraicSpace,
  `AlgebraicGeometry.AlgebraicSpace`, `IsAlgebraicSpace`, `IsRepresentableWith`,
  `EtaleSite`, `structureSheaf`, and `Modules` in its namespace.
- `def-weil-size-convention`: metatheoretic convention, rendered by the explicit
  universe and index choices; its record correctly has no object declaration.
- `def-trf-space-quasi-coherent-module`:
  Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule,
  `AlgebraicGeometry.AlgebraicSpace.QCoh` and its named slice sheafification instances;
  the theorem uses its underlying Mathlib `SheafOfModules.IsQuasicoherent` and
  `SheafOfModules.IsFinitePresentation`, not a private replacement or second QCoh.
- `def-trf-space-etale-module-functors`:
  Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations,
  `AlgebraicGeometry.AlgebraicSpace.moduleTensorPullback`, whose left adjoint is
  determined by `ModuleDirectImageModel` and retains `moduleTensorAdjunction`.
- Existing auxiliary interfaces are reused: `schemeSpace` from
  Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite; `MapIsQuasiCompact` from
  Sheaf.AlgebraicGeometry.ProperCurveModuli; `MapIsLocallyOfFinitePresentation` from
  Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties; `schemeRestriction`
  from Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction; and
  `AlgebraicGeometry.Scheme.Modules.IsFlatOver` from
  WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic. The last two are
  used inside the landed relative-flatness definition, rather than being expanded
  in the signature. All their owners are explicitly retained in stmt_deps as the
  maintainer requested.
- `def-sfb-space-flat-proper-coefficient`:
  Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperCoefficient,
  `AlgebraicGeometry.AlgebraicSpace.ModuleIsFlatOver`, used for both limit and stage
  relative flatness. The owning module is publicly imported.
- `def-sfb-stack-qcqs-morphism`: Sheaf.AlgebraicGeometry.StackQcqsMorphism,
  `AlgebraicGeometry.AlgebraicSpace.MapIsQuasiSeparated`, used for hqs. The owning
  module is publicly imported. Its body is exactly the former diagonal
  quasi-compactness condition, without a stronger separation hypothesis.
- The definition owners of the other reused interfaces are now explicit stmt_deps:
  `def-sfb-proper-curve-moduli` (MapIsQuasiCompact),
  `def-sfb-space-morphism-properties` (MapIsLocallyOfFinitePresentation), and
  `def-trf-scheme-algebraic-space` (schemeSpace). The two underlying flatness owners
  `def-trf-space-module-scheme-restriction` and `def-pc-scheme-module-flat-over` are
  also included, as named in the return. These are existing landed nodes;
  no definition node or declaration is copied or redefined.

All currently stated proof dependencies have their modules imported without `public`,
including the Mathlib matches `LocallyOfFinitePresentation.finitePresentation_appLE`
and `pullbackSpecIso`. Imports also include SpaceLocalPropertiesChartTest,
AlgebraicSpaceModulePullbackQuasiCoherent, SpaceChartTensorRealization,
SchemeZariskiEtaleQuasiCoherentEquivalence, QuasicoherentFiniteTypeAffine,
AlgebraicSpaceFibreProductsEtaleCovers, LimitAffineTransition,
ModulePullbackAffineSections, AffineChartRelativeFlatCriterion, and
AffineFlatModuleDescent. The proof-only nodes
`lem-trf-space-qc-finite-affine-atlas-refinement`,
`lem-sfb-scheme-etale-module-exact-finiteness-comparison`, and
`lem-sfb-space-module-flat-chart-test` have no Lean attachment or Mathlib match in the
read repository, so there is no module for them to import yet. They are not notions
needed to type this statement; their accepted proof steps remain verbatim in the
node and are included in the theorem's natural-language proof docstring.

Edge cases checked before writing: a one-element directed set; k=j and j=i0;
empty source/empty atlases; zero module; zero base ring/empty affine scheme;
non-surjective and non-flat transitions; arbitrary non-Noetherian stage rings;
and mixed or positive characteristic. Empty sites give vacuous chart conditions,
matching the vacuous geometric-stalk condition. With the zero module, all module
flatness conditions hold. No nonemptiness of a scheme or nonzero ring is assumed.
There is no empty-index-system case in the node, which explicitly assumes nonempty I.

Searches for an existing declaration:

- `msearch.py ... leanfinder`: “A finitely presented quasi coherent module on an
  algebraic space over an inverse limit of affine schemes is relatively flat at all
  sufficiently late stages”. Eight hits: scheme `Flat`, `flat_iff`, flat stalk-map
  criteria, algebra smoothness and the module equational factorization criterion.
  None concerns module flatness on algebraic-space inverse limits.
- `msearch.py ... loogle`: `"Flat", "FinitePresentation"`. Eight hits include
  `Module.Flat.projective_of_finitePresentation`, flat-module factorization, and
  faithfully flat algebra-presentation descent. None is this assertion.
- `msearch.py ... grep`, subdirectory AlgebraicGeometry:
  `eventually.*[Ff]lat|[Ff]lat.*[Ll]imit|AlgebraicSpace`. One unrelated Proetale
  flatness hit; no module-flatness descent statement for spaces.
- `rg` in Mathlib, lean/WeilConjectures and lean/Sheaf for
  `module_eventually_flat_of_affineLimit|module.*eventually.*flat|eventually.*module.*flat`,
  and the broader `eventually.*flat|eventually_flat|module-eventually-flat`.
  Source results include `exists_eventually_isFlatOver_of_limit` in FlatModuleDescent
  (schemes, with Noetherian stage assumptions), chosen scheme-module/complex stage
  statements, and algebraic flat-module descent. These are not an algebraic-space
  theorem and do not have this statement's hypotheses. Reused the algebraic descent
  proof dependency instead of asserting these scheme statements are exact matches.
- The item id has no occurrence in lean/WeilConjectures. The chosen declaration name
  has no existing declaration in Mathlib, WeilConjectures, or Sheaf. Searches for
  `MapIsLocallyOfFinitePresentation`, `MapIsQuasiCompact`, `schemeSpace`,
  `schemeRestriction`, and `IsFinitePresentation` located the reused interfaces above.

No STATEMENT-DISPUTED flag or source fault was found. The mathematical statement
and proof plan are unchanged. Compilation and delivery checks use only the prescribed
server wrappers.

## Repair of returned delivery 2400f0af12cb

1. H4, relative flatness: replaced both the hypothesis and the conclusion by the
   landed `ModuleIsFlatOver` predicate. Read its full signature and definition in
   AlgebraicSpaceFlatProperCoefficient. It requires all compatible pairs of étale
   charts and uses the recorded scheme restriction and scheme flatness predicate;
   its node identifies this with the required geometric-stalk condition. Imported
   its owning module directly. This uses the same shared interface as siblings.
2. H4, quasi-separatedness: replaced the expanded diagonal quasi-compactness in
   hqs by `MapIsQuasiSeparated f0.hom.hom`. Read its definition in StackQcqsMorphism
   and imported that module directly. The predicate unfolds to precisely the old
   condition.
3. H2, ownership: added the seven existing definition nodes listed above to
   stmt_deps, including both predicate owners and all five owners named in the
   return. This dependency-only repair is explicitly authorized by the return;
   the natural-language statement, proof, proof_deps and all other node fields
   remain unchanged. Refreshed lean.statement verbatim from the revised signature
   and lean.note to identify this repair. No statement_change record is needed:
   neither the mathematical statement nor its source was corrected.
4. Compared the retained node with current main: all fields outside lean matched
   before this repair. The retained module was the returned signature, including
   the expanded flatness and diagonal conditions; the repaired diff changes these
   exact conditions and their imports. The delivery wrapper builds the repaired
   commit on the current main branch.

## Second reading by NF

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
