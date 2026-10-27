## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceClosedPushforwardRelativeFlatness` states
`AlgebraicGeometry.AlgebraicSpace.space_closed_pushforward_relative_flatness` with
`sorry`. It has no helper declarations or new definitions. The node statement,
proof and proof dependencies are unchanged. Three already-landed statement dependencies
are added to cite the existing flatness predicate, its ordinary scheme restriction,
and the scheme-as-space construction; no new nodes or dependency repairs are needed.

Clause-by-clause correspondence:

- The scheme base is `{S : Scheme.{u}}`; its scheme `T` over S is `(T : Over S)`.
  `schemeSpace T` is the actual represented fppf sheaf of T, not an arbitrary
  algebraic space isomorphic to a scheme. There is no independent smaller test universe.
- The two spaces are `{X Z : AlgebraicSpace S}`. Their arrows are
  `(f : X ⟶ schemeSpace T)` and `(i : Z ⟶ X)`. The composite to T is `i ≫ f`.
- The closed immersion hypothesis is
  `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom`.
  This quantifies over every scheme test and requires a representing closed immersion;
  it imposes no finite-presentation condition.
- The module is `(G : Z.Modules)` and its only module hypothesis is
  `[G.IsQuasicoherent]`, the recorded Mathlib site-presentation predicate, specialized
  using `AlgebraicSpaceQuasiCoherentModule`.
- `moduleDirectImage i` is exactly the dependency's compatible-chart-section direct
  image, with its prescribed scalar action; no arbitrary map or functor is supplied.
- The first conjunct is
  `ModuleIsFlatOver (i ≫ f) G ↔ ModuleIsFlatOver f ((moduleDirectImage i).obj G)`.
  This uses the existing relative-flatness predicate, not a new private definition.
- The second conjunct is
  `MapIsFlat (i ≫ f) ↔ ModuleIsFlatOver f ((moduleDirectImage i).obj
  (SheafOfModules.unit Z.structureSheaf))`. Thus its left side is exactly chartwise
  flatness of Z → T, and its right side is relative flatness of i_*O_Z.
- No Noetherian, finite-presentation, flatness of i or flatness of f assumption occurs.

The existing `ModuleIsFlatOver` tests every compatible source and target étale chart,
whereas the node spells out the equivalent base-local-ring test for the scheme T.
The identity target chart recovers the latter condition. Conversely, on a target
chart B → T the Zariski chart module's stalk already has its O_{B,b}-action, and
`etale_local_ring_flatness` identifies its flatness over O_{B,b} and O_{T,t}.
The affine-local predicate in `Scheme.Modules.IsFlatOver` equals this stalk test
for quasi-coherent modules (01U4). This is the same equivalence used in the node's
last proof step, not a new hypothesis. Ordinary Zariski stalks are used throughout.

Dependency declarations read and used (namespace `AlgebraicGeometry.AlgebraicSpace`
unless otherwise indicated):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`,
  `EtaleSite`, `structureSheaf`, `Modules`; `IsEtale` and `etaleForget` underpin charts.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, publicly available through the chart-property
  dependency. Its full signature and docstring were read in the pinned Mathlib.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently `SheafOfModules`; the module is publicly imported as recorded.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh` and its
  slice instances for `SheafOfModules.IsQuasicoherent`, publicly imported through
  `AlgebraicSpaceFlatProperCoefficient`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleDirectImage`,
  with `ModuleDirectImageModel`, its limit universal property and normalized projection
  identities. The actual definition and its supporting theorem docstrings were read.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic`:
  `AlgebraicGeometry.Scheme.Modules.IsFlatOver`, publicly available through
  `AlgebraicSpaceFlatProperCoefficient` (affine opens and actual scalar restriction).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`,
  `MapIsFlat`, publicly imported through `AlgebraicSpaceFlatProperCoefficient`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperCoefficient`:
  `ModuleIsFlatOver`. Added its existing node `def-sfb-space-flat-proper-coefficient`
  to stmt_deps. Its unused proper-annihilator-support predicate imposes no assumption.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`: `schemeRestriction`,
  real precomposition with Zariski opens and the canonical structure-ring comparison.
  Added its existing node `def-trf-space-module-scheme-restriction` to stmt_deps.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`, owned by the
  existing definition node `def-trf-scheme-algebraic-space` (existing:true record,
  also listing `schemeSheaf_isAlgebraicSpace`). This definition node is added to
  stmt_deps. The module import is retained; its actual representable-sheaf construction
  is used directly.
- `def-weil-size-convention` is a metatheoretic convention, implemented here by the
  explicit universe u and the dependency sites and module carriers, without a binder.

All recorded proof modules are imported with plain `import` unless already public
statement dependencies. These are: `Mathlib.AlgebraicGeometry.Morphisms.Etale` (Etale),
`Mathlib.AlgebraicGeometry.Morphisms.Flat` (Flat),
`WeilConjectures.Topology.ClosedPushforwardAbelianStalks`
(`TopCat.closedPushforwardAbelianStalks`),
`Sheaf.TraceFormula.EtaleLocalRingFlatness` (`AlgebraicGeometry.etale_local_ring_flatness`),
`Sheaf.AlgebraicGeometry.RelativeFlatnessSourceCover`
(`AlgebraicGeometry.relative_flatness_source_cover`),
`Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence`
(`AlgebraicGeometry.Scheme.Modules.scheme_zariski_etale_quasiCoherent_equivalence`),
`Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction`
(`etale_module_pushforward_restriction`),
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`
(`fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, `etale_fibreProduct_isScheme`),
and `Sheaf.TraceFormula.ZariskiEtaleFunctorComparisonSquare`
(`AlgebraicGeometry.Scheme.Modules.zariski_etale_functor_comparison_square`).
`lem-sfb-space-closed-immersion-quasi-coherent-modules` has no Lean record locally,
so its future proof import is omitted and left for maintainer bookkeeping; it is not
a missing notion needed to state this theorem. The five-step proof in the docstring
retains that input and all other steps of the accepted split.

Sources read: local `spaces-morphisms.tex`, lemma-stalk-push-closed (0DK1), including
its known interchanged source/target subscripts; `quot.tex`, lemma-hilb-is-quot (0D00),
both the omitted forward flatness argument and its reverse; `flat.tex`,
lemma-etale-flat-up-down-local-ring (05BA). The node already corrects the 0DK1 typo.

Edge cases checked before writing: Z empty makes the pushforward zero and both
structure-module flatness tests true; i = identity gives the identity equivalence;
G = zero gives relative flatness independently of f. For Spec F_2 → Spec Z with
T = X = Spec Z, O_Z and its pushforward are both nonflat over T; thus the theorem
does not assert that a closed immersion is flat. Over a field base both relative
flatness tests hold. Nonreduced closed subspaces retain their full structure module;
there is no reduction, finite-type restriction, or characteristic restriction.
Empty X and T are permitted. All tests use the same universe as the base scheme,
and the imported sites retain their object/hom universe distinction.

Searches actually run on 2026-10-24:

- msearch leanfinder, `Closed immersion algebraic space direct image quasi coherent
  module flat over base if and only if`: 8 hits on flat scheme morphisms (Flat,
  flat_iff, Flat.instOfIsOpenImmersion, etc.); no relative module pushforward theorem.
- msearch loogle, `"IsFlatOver", "pushforward"`: 0 hits.
- msearch grep, `flat.*pushforward|pushforward.*flat|FlatOver`: one hit in
  Mathlib/RingTheory/Flat/FaithfullyFlat/Algebra.lean about ideals, not this theorem.
- msearch leansearch, `Relative flatness of a quasi coherent module preserved and
  reflected by closed immersion direct image`: 8 hits on localization, scheme
  flatness and scalar restriction; no exact theorem.
- rg on lean/WeilConjectures and lean/Sheaf for IsFlatOver, FlatOver,
  pushforward/flat combinations and the item id: ordinary scheme flatness,
  constant-coefficient closed pushforward, and other finite pushforwards differ
  from this structure-module statement. No exact existing declaration was found.
- rg on AlgebraicSpace*.lean found the existing `ModuleIsFlatOver` in
  AlgebraicSpaceFlatProperCoefficient and its uses; its DAG record was opened,
  and the notion is reused. The proposed full declaration name has no matches.

Validation: prescribed scompile.py checked the final file in sandbox and library
module mode; both succeeded (17.8 s and 20.6 s), with no errors or unexpected warnings.
No statement dispute or correction is necessary.


## Repair of returned delivery 67cc3843cb85

H2: replaced the added theorem dependency
`lem-trf-space-enlarged-etale-ringed-site-model` by the existing definition owner
`def-trf-scheme-algebraic-space`. Read its live node and existing:true Lean record:
`AlgebraicGeometry.AlgebraicSpace.schemeSpace` and `schemeSheaf_isAlgebraicSpace`
in `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`. The report dependency paragraph
now cites this owner. The Lean file and its import are unchanged, as requested.
The sandbox node was compared with current main and its unaffected fields refreshed
from main; the delivered theorem statement is unchanged. The return's only requested
repair is this dependency correction; every other clause was independently accepted.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
