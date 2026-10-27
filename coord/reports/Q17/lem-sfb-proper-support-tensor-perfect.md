## Worker report

Q17 states `AlgebraicGeometry.AlgebraicSpace.properSupport_tensor_perfect` in
`Sheaf.AlgebraicGeometry.ProperSupportTensorPerfect`. Its proof is `sorry`.
The accepted stage-1 statement and proof plan are unchanged. Source checked:
Stacks spaces-perfect.tex, lemma-base-change-tensor-perfect (0A1P), including
its entire approximation proof; perfectness is the ringed-site definition 08G5.
The separate arbitrary-base-change assertion of 0A1P is not part of this node.
The obsolete inherited stage-1 unchanged-item refusal does not apply: this is
the stage-2 handoff and the input item has no Lean record.

Clause-by-clause correspondence:

- Base scheme and algebraic spaces: `{S : Scheme.{u}} {X Y : AlgebraicSpace S}`.
  These are the recorded algebraic-space objects, not a scheme specialization.
- Finite presentation of `f`: `_hfp` is `MapIsLocallyOfFinitePresentation f`,
  `MapIsQuasiCompact f.hom.hom`, and quasi-compactness of its diagonal. The
  last conjunct is quasi-separatedness, as required by the accepted split.
- The original sites and coefficients are the existing `X.EtaleSite`,
  `X.structureSheaf` and `X.Modules`, likewise for Y. Their site objects have
  universe u+1, morphisms u, and ring/module sections u. Q115's recorded
  `X.SmallModules` uses the equivalent small affine etale model, preserving
  the section universe; no equality of the original site universes is imposed.
- Unbounded derived objects: `E : X.DerivedModules`, exactly the recorded
  `DerivedCategory X.SmallModules`. The explicit binders
  `[HasDerivedCategory.{w} X.SmallModules]` and the corresponding Y binder
  select the common localization morphism universe required by the recorded
  `derivedDirectImage` API. This is the existing small-model calculus.
- Perfect E: `_hE : IsPerfectAtCoefficientSize X.smallStructureRings E`.
  This is the 08G5 representative-and-cover definition on that equivalent
  ringed site. Every local bounded complex has the existing
  `StrictPerfectCoefficientPackageOnSite`: degreewise inclusion and
  retraction to a finite power of the restricted structure module. Bounds
  and ranks may vary on the cover.
- Coefficient complex: `G : CochainComplex X.Modules ℤ`. `_hbounded` gives
  integers a,b and categorical zero objects outside [a,b], without bounding E.
- Quasi-coherence: `_hqc` uses Mathlib's existing `(G.X n).IsQuasicoherent`,
  the same predicate used by the dependency's QCoh subcategory.
- Finite presentation: `_hfinite` is `(G.X n).IsFinitePresentation` in every
  degree, Mathlib's local finite generators and relations condition.
- Relative flatness: `_hflat` uses `ModuleIsFlatOver f`. On every compatible
  pair of etale charts it uses the existing scheme module `IsFlatOver` after
  the recorded restriction to opens. For quasi-coherent modules affine-local
  flatness is equivalent to stalk flatness; etale localization on both sides
  gives precisely the geometric-stalk condition in the item. This quantifies
  over all compatible chart maps, not an arbitrary selected atlas.
- Proper support: `_hproper` uses `HasProperAnnihilatorSupport f` in every
  degree. A representing closed immersion has, on every scheme chart and
  affine open, ideal exactly `Module.annihilator` of the restricted sections.
  `MapIsProper (i ≫ f)` is separated, finite type and universally closed, using
  the existing morphism-property definition. No arbitrary proper carrier is
  substituted for the annihilator closed subspace.
- The tensor is `moduleDerivedTensorComplex X E G`: the categorical total
  left derived functor of total tensor on `X.SmallModules` with the termwise
  restriction `((X.smallModuleRestriction.mapHomologicalComplex (.up ℤ)).obj G)`.
  The ordinary tensor is the existing sheafification of sectionwise tensor.
  The named K-flat existence obligation determines the derived functor by
  its universal property; no arbitrary representative is chosen.
- The direct image is `(derivedDirectImage f).obj ...`, imported from
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`. Its actual body is
  `(smallModuleDirectImage f).rightDerivedFunctor`, where the ordinary functor
  is `X.smallModuleEquivalence.inverse ⋙ moduleDirectImage f ⋙
  Y.smallModuleRestriction`. Thus it uses the canonical chart direct image
  conjugated to the equivalent small module categories.
- Conclusion: `IsPerfectAtCoefficientSize Y.smallStructureRings` of that
  image, and `Y.derivedQCohProperty` of exactly the same image. The latter
  tests every cohomology sheaf after the recorded inverse module equivalence,
  using Mathlib `IsQuasicoherent` on the original Y module category.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `etaleTopology`, `structureSheaf`, `Modules`, `etaleForget`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`,
  `derivedDirectImage`, `derivedQCohProperty`, `smallModuleDirectImage`.
  Its imported `AlgebraicSpaceSmallRingedModel` supplies `SmallModules`,
  `smallStructureSheaf`, `smallStructureRings`, `smallModuleRestriction`,
  and `smallModuleEquivalence`; their data are reused unchanged.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleDirectImage`
  (the compatible-chart-section limit construction), and its tensor-pullback
  adjunction. The derived image uses that exact direct image.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, whose
  object property is Mathlib `SheafOfModules.IsQuasicoherent`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `Q`.
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence` supplies homology.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `MapIsLocallyOfFinitePresentation`, `MapIsProper`; the imported algebraic-space
  framework supplies `MapIsQuasiCompact` and representable closed immersions.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`: `schemeRestriction`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `Scheme.Modules.IsFlatOver`; `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`:
  `Scheme.Hom.ker` and its affine `ideal`.
- `Sheaf.Paper.StrictPerfectPackageOnSite`:
  `StrictPerfectCoefficientPackageOnSite`, with real inclusion/retraction data.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality` and its imports:
  `siteSheafTensorRight`, `siteSheafTensorRightMap`, the existing sheafification
  of the sectionwise ordinary module tensor.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs`:
  `Functor.rightDerivedFunctor`; Mathlib's `Functor.totalLeftDerived` and
  `HasLeftDerivedFunctor` give the corresponding universal property.
- The available proof-dependency modules `Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat`
  and `Sheaf.Paper.StrictPerfectRingedPullbackModel` are plain imports. The other
  proof nodes have no recorded usable Lean module, and are not imitated here.

Edge cases checked: the zero coefficient module has annihilator the unit ideal
and empty closed support, which is proper; zero complexes and empty spaces are
allowed. Bounds need not be ordered and may describe the zero complex. Finite
rank zero is allowed by the existing package. E is unbounded as an ambient derived
object; perfectness is local and no uniform global rank or amplitude is added.
Neither f nor X must be proper: a skyscraper coefficient on affine space has
proper support and is admitted. Non-quasi-compact charts are not excluded; support
is tested on every affine open. Flatness and support are termwise, not merely
conditions on cohomology. No Noetherian, separated-base, characteristic, or field
hypothesis has been added. Universes c,v,r,u,w and every variable are explicitly bound.

Searches: launcher msearch LeanFinder query "Perfect complex tensor bounded relatively
flat finitely presented properly supported complex on algebraic spaces has perfect
derived direct image" returned flat morphism/module facts, no exact statement.
Loogle `AlgebraicGeometry.AlgebraicSpace, DerivedCategory` reported unknown identifier
and no hit; Mathlib grep `AlgebraicSpace|IsPerfectOnRingedSite|properSupport.*perfect`
in AlgebraicGeometry returned zero. LeanSearch "Perfect complexes on algebraic spaces
tensor proper support direct image" returned scheme pushforward, proper morphism
and complex-support facts. New-notion LeanSearch and LeanFinder queries and their
actual response summaries are retained in the new nodes' mathlib_searches. The original project
rg of `ModuleIsFlatOver|HasProperAnnihilatorSupport|moduleDerivedTensorComplex|moduleDerivedDirectImage`
in both WeilConjectures and Sheaf returned no declaration at that earlier search time; grep of the item id in
WeilConjectures returned no match. DAG searches and blueprint_refs searches found
no exact owning definition. Existing scheme/ringed-space direct images have different
sites; the fixed-ring pro-etale derived tensor has different coefficients and endpoints.
The proper Quot node describes support and flatness in prose but does not export
these predicates or specify the annihilator ideal as an independent interface.

The saved small-model repair passed the initial `deliver2.py --no-push`:
commit `7dd28cbb9ae`, all three modules compiled separately on the server and
preflight passed. The final delivery rechecks that same Lean source after this
report update. The current source search finds Q115's calculus and small-model
modules; these are now cited and imported instead of duplicated.
Every new theorem has only `sorry`; every definition has actual data. No statement
correction or STATEMENT-DISPUTED flag is needed.

## New nodes

`def-sfb-space-derived-module-operations` now owns only the derived tensor
with a coefficient complex on the existing small model. Its statement specifies
termwise `smallModuleRestriction` of G, sheafified sectionwise tensor, total
complex differential, functoriality and zero-map obligations, and existence of
the categorical left derived functor via K-flat resolutions. Its ten recorded
declarations contain no direct-image construction, additivity instance for
direct image, or Grothendieck/K-injective instance. The calculus node owns the
ambient D(O_X), D_QCoh and Rf_*; both this new tensor node and the item cite it.
Sources: 03EK, 06YS, 06YU, 079P. The original searches predate the calculus landing;
the current review locates and reuses that landed interface.

`def-sfb-space-flat-proper-coefficient` owns relative flatness and the annihilator
closed-subspace proper-support predicate required by 0A1P. It reuses the canonical
scheme restriction and affine-local scheme flatness. Its support condition equates
ideals on all chart affine opens, so is stricter than merely identifying a support
point set exactly as required by this item. Sources: 0A1P, relative flatness, 0CZI.
Searches found ordinary module flatness and scheme support facts, no declaration
for an algebraic-space structure-module annihilator support. The proper Quot node
has a different owning notion and no exported predicate to use here.

## Returned-delivery repair (H13)

The independent review of immutable head `1e5b0a6783b4` found that the two
stage-3-proved dependency records had been rebound to new wrapper modules. Both
`def-pur-sheaf-tensor-product` and
`def-weil-pbc-strict-perfect-coefficient-package` are now byte-identical to the live
repository: Q46's `CochainTensorUniverses` and Q15's
`StrictPerfectCoefficientPackageOfUniverses` retain their original ownership,
statements, declarations and reviewed-proof records. No dependency is rebound.

As the return directs, all declarations formerly in `SiteTensorAtCoefficientSize`
are moved into `AlgebraicSpaceDerivedModuleOperations`, owned and listed by
`def-sfb-space-derived-module-operations`. Its self-contained statement now
explicitly covers currying and identity/composition/zero preservation of the
existing sheafified sectionwise tensor at the actual coefficient universe.
All moved docstrings identify that owning node. The separate tensor wrapper is
removed; the operations module publicly imports the live recorded tensor module.

The two predicates formerly in `SitePerfectAtCoefficientSize`,
`SheafOfModules.IsLocallyStrictPerfectAtCoefficientSize` and
`SheafOfModules.IsPerfectAtCoefficientSize`, are now helpers in the item module,
listed in its `lean.declarations`, with item-tagged source docstrings. The item
publicly imports the live recorded perfect-package module and uses its actual
`StrictPerfectCoefficientPackageOnSite`. The separate perfectness wrapper is
removed. The predicates' bodies and all hypotheses and conclusion clauses of
`properSupport_tensor_perfect` are unchanged. These are the helper placement and
ownership changes specifically authorized by the return; no new node is needed.

The advisory about four available proof routes is recorded: stage 2 still leaves
its named new proof obligations as `sorry`; this repair changes their ownership,
not the existing live proofs. The two plain proof-route imports correspond to the
item's recorded proof dependencies and remain as required by stages/2-statements.md
§3.7; they are not claimed as statement dependencies or as proofs of this theorem.

## Returned-delivery repair (H12/H4)

The return of immutable head `477245d8e265` identifies Q115's already landed
`def-sfb-space-derived-module-calculus` as the owner of D(O_X), D_QCoh and Rf_*.
The retained sandbox repair adds that node to both the item's and tensor node's
`stmt_deps`, and publicly imports `AlgebraicSpaceDerivedModules`. The theorem now
binds E in `X.DerivedModules` with `HasDerivedCategory.{w}` on SmallModules;
perfectness uses `X.smallStructureRings` and `Y.smallStructureRings`, and its
conclusion uses the imported `derivedDirectImage f` and `Y.derivedQCohProperty`.
G and its boundedness, quasi-coherence, finite-presentation, relative-flatness and
annihilator-support predicates remain in the original `X.Modules`.

The operations node and module are reduced to tensor on `X.SmallModules` with
termwise `smallModuleRestriction` of G. The duplicate `moduleDerivedDirectImage`
and all its supporting direct-image/Grothendieck instances are absent. The
`lean.declarations` list contains precisely the ten surviving tensor declarations,
and `lean.statement` is the new `moduleDerivedTensorComplex` signature verbatim.
The item's three declarations and new signature are likewise recorded verbatim.
No item statement correction is required: this is transport to the already
recorded equivalent small model, exactly as the return requests. The two proved
dependency node files still compare byte-for-byte with the current read clone.
The item differs from its current live node only in `lean` and `stmt_deps`.

## Second reading by Q17

I reopened all three current sandbox modules, their node records, Q115's
`AlgebraicSpaceDerivedModules` and `AlgebraicSpaceSmallRingedModel`, and Stacks
0A1P, 08G5 and 08JL. The saved repair already contained the requested Lean
changes; this session corrected the report's stale descriptions of those changes.
The initial dry run passed, so the Lean source is retained.

The item's S, X and Y binders give arbitrary algebraic spaces over a scheme.
`_hfp` gives lfp + qc + qs, the accepted finite-presentation interpretation.
E is in the existing unbounded small-model derived category; `_hE` is the
08G5 cover/strict-perfect-representative predicate on its structure ring.
`G : CochainComplex X.Modules ℤ` and `_hbounded` retain bounded original-site
coefficients. `_hqc`, `_hfinite`, `_hflat` and `_hproper` separately require each
term's quasi-coherence, finite presentation, compatible-chart relative flatness
and proper annihilator closed subspace. The total tensor restricts G by the
specified equivalence, derives the sectionwise tensor and returns an object of
that same ambient category. Both conclusion clauses apply to exactly
`(derivedDirectImage f).obj (moduleDerivedTensorComplex X E G)`: the first uses
08G5 on Y's small structure rings; the second transports cohomology back by the
recorded inverse equivalence and tests the existing quasi-coherence predicate.
Thus all hypotheses and both conclusion clauses remain those of the node.

The zero coefficient complex and empty spaces are still admitted; rank zero,
locally varying bounds/ranks and an unbounded ambient E remain admitted. Proper
support of zero is empty, and the predicates add no properness hypothesis on f.
All universe and term variables are explicitly bound. All fifteen delivered
names are listed by their owning nodes; the five tensor helper theorems and the
item theorem have whole `sorry` proofs, while every definition has real data.
No duplicate direct image or supporting instances survive. The H13 ownership
repair remains intact. The dispatcher prohibits additional agents; this is the
worker self-check, with independent review supplied by the maintainer.
