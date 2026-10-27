## Worker report

Stage-2 statement of `lem-sfb-space-relative-finite-free-locus-base-change` in
`Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativeFiniteFreeLocusBaseChange`.
The current item is split and reviewed at stage 1, has no Lean binding, and is listed
at stage 2 in coord/queue.tsv. There is no released repair note. The inherited ending
concerned an unchanged stage-1 delivery, not a stage-2 refusal. The accepted statement,
proof, proof dependencies, and review are preserved.

Source read: literature/stacks-project/spaces-more-morphisms.tex, lines 5988–6017,
Tag 0CZT, lemma-finite-free-open, including its proof. Its hypotheses and its two
conclusions agree with the node. The module gives the locus actual data and states
one theorem with `sorry`; it proves nothing.

Clause-by-clause correspondence:

- A scheme S: `{S : Scheme.{u}}`, with arbitrary universe u.
- Algebraic spaces X,Y over S: `{X Y : AlgebraicSpace S}`; the existing category is
  the full subcategory of fppf sheaves with representable diagonal and an étale atlas.
- The structural map p: `(p : X ⟶ Y)`.
- Local finite presentation of p on étale charts:
  `(hp : MapIsLocallyOfFinitePresentation p)`. This existing predicate tests every
  compatible pair of representable étale scheme charts, exactly as the node requires.
- A quasi-coherent module on the small étale ringed site: `(F : X.QCoh)`.
  Its underlying module is `F.obj`, with Mathlib's `IsQuasicoherent` as `F.property`.
  This is not a module on the Zariski site or a constant-coefficient module.
- Finite presentation: `(hF : SheafOfModules.IsFinitePresentation F.obj)`.
  Mathlib defines this by locally finite presentations by free structure modules.
- Flatness over Y: `(hflat : ModuleIsFlatOver p F.obj)`. The existing definition
  restricts to every compatible pair of étale scheme charts and uses the established
  scheme-module relative flatness predicate, equivalent for quasi-coherent modules
  to the stated local-ring stalk condition. It does not require p to be flat.
- W(F): `finiteFreeLocus X F.obj`. Its defining membership quantifies over an object
  `U : X.EtaleSite`, requires `x ∈ pointImage U.obj.hom`, and requires an isomorphism
  between `(X.etalePullback U).obj F.obj` and
  `SheafOfModules.free (R := X.structureSheaf.over U) (ULift.{u} (Fin r))` for `r : ℕ`.
  Restriction to the localized étale site is the recorded étale pullback. A free
  module is Mathlib's coproduct of copies of the structure module. ULift only puts
  the finite basis in the coefficient universe. This helper directly constructs
  the locus already defined in this node; it is not an independent missing notion.
- Openness: `IsOpen (finiteFreeLocus X F.obj)` in the existing algebraic-space
  point topology.
- Every base change: `∀ (Y' : AlgebraicSpace S) (v : Y' ⟶ Y)`.
  No condition is imposed on v.
- Form X'=X×_Y Y', with its projection q: quantify X', q and p' with
  `IsPullback q p' p v`. This is the categorical universal property with the
  specified projections; it is equivalent to using the chosen sheaf fibre product
  by `fibreProduct_isAlgebraicSpace`. Quantifying over its realizations adds no
  mathematical hypothesis and does not replace the projection by an arbitrary map.
- The pulled-back module: `((moduleTensorPullback q).obj F.obj)`, the canonical
  tensor pullback from the recorded module-operations dependency.
- Equality of loci:
  `finiteFreeLocus X' ((moduleTensorPullback q).obj F.obj) =
    (mapPoint q.hom.hom) ⁻¹' finiteFreeLocus X F.obj`.
  Thus the conclusion is equality of the subsets on points, not one containment.
- There is no flatness assumption on p or v, no finite-presentation assumption on v,
  and no Noetherian, quasi-compactness, separatedness or nonemptiness assumption.

Dependency declarations used, with source signatures and docstrings read:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: AlgebraicGeometry.AlgebraicSpace,
  AlgebraicSpace.EtaleSite, structureSheaf, Modules, etalePullback; these keep the
  existing scheme-valued charts, ring sheaf and localized restriction.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties:
  AlgebraicSpace.MapIsLocallyOfFinitePresentation and its MapIsLocally chart test.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: AlgebraicSpace.QCoh;
  Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent:
  SheafOfModules.IsQuasicoherent, QuasicoherentData.IsFinitePresentation,
  SheafOfModules.IsFinitePresentation.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations:
  AlgebraicSpace.ModuleDirectImageModel, moduleTensorPullback and its specified
  adjunction to the chart-limit direct image. No replacement pullback is defined.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers:
  AlgebraicSpace.fibreProduct_isAlgebraicSpace, etaleCover_pullback and
  etale_fibreProduct_isScheme supply the recorded fibre-product interface.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperCoefficient:
  AlgebraicSpace.ModuleIsFlatOver, the existing chartwise relative-flatness predicate.
  Its owning, already landed node `def-sfb-space-flat-proper-coefficient` is added to
  stmt_deps under brief-stage2 §5 (statement dependencies may gain landed nodes).
  No dependency module or duplicate definition is needed.
- Sheaf.AlgebraicGeometry.ProperCurveModuli: AlgebraicSpace.mapPoint; and
  Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology: pointImage and
  pointTopologicalSpace, already available through the morphism-properties dependency.
- Mathlib.Algebra.Category.ModuleCat.Sheaf.Free: SheafOfModules.free, defined as
  the coproduct of copies of SheafOfModules.unit.

The stated proof dependencies are imported as plain imports: the affine étale cover,
quasi-coherent pullback, and finite-presentation module limit modules, and Mathlib's
finite presentation/base-change modules. Three proof nodes have no Lean binding yet
(local-properties-chart-test, pointwise-module-flat-base-change, fibre-flat-free-criterion);
they are not imported or assumed as extra hypotheses. The theorem docstring records
all four accepted proof steps, including the common-field fibre identification.

Edge cases checked before writing: r=0 is allowed (Fin 0 is empty and the coproduct
is the zero module); the zero sheaf therefore has the full finite-free locus. Empty
spaces and empty chart domains are permitted; no nonempty or positive-rank binder
was inserted. The identity base change and an arbitrary non-flat or non-finitely
presented v are included by the unrestricted base-change quantifier. The coefficient
universe remains u, the point set lives in u+1 as in the recorded point construction,
and ULift of Fin r does not restrict the rank or impose a universe equality.

Searches performed through the prescribed msearch.py wrapper (group Q13, this item):

- leanfinder: “The finite locally free locus of a finitely presented quasi-coherent
  module flat over a locally finitely presented algebraic space base is open and
  commutes with arbitrary base change”. Eight hits: scheme local-finite-presentation
  permanence/universal openness, Module.isOpen_freeLocus, and finite-presentation
  sheaf declarations. None state the algebraic-space relative base-change theorem.
- loogle: “Module.freeLocus, Module.isOpen_freeLocus”. One result:
  Module.isOpen_freeLocus, an absolute affine-module statement, not this theorem.
- grep: “freeLocus|finiteFreeLocus|FiniteFreeLocus”. Sixteen Mathlib hits, principally
  RingTheory/Spectrum/Prime/FreeLocus and imports. None give this sheaf-space theorem.
- leansearch: “For a relatively flat finitely presented quasi-coherent sheaf on
  algebraic spaces the finite locally free locus is open and commutes with arbitrary
  base change”. Eight hits: Module.isOpen_freeLocus, scheme universally open/flat
  base change, and SheafOfModules finite-presentation interfaces. No exact match.
- Local rg on lean/WeilConjectures and lean/Sheaf:
  “freeLocus|finite.free.*locus|locally.free.*locus|lem-sfb-space-relative-finite-free-locus-base-change”.
  Upstream hits concern affine modules, residue free loci, and isomorphism loci;
  no declaration for this node. The separate AlgebraicSpace*.lean search for
  “finiteFreeLocus|freeLocus|FiniteFreeLocus|IsFlatOver|FlatOver|FinitePresentation|LocallyFree”
  found the reusable ModuleIsFlatOver and finite-presentation interfaces.

No statement correction and no STATEMENT-DISPUTED flag. The displayed locus helper
and the theorem are both listed in lean.declarations. All variables and universes are
explicitly bound and autoImplicit is false.

Validation: scompile.py compiled the module separately as sandbox and library module
against the live server build, with no error or unexpected warning (6.3 s and 4.0 s).

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
