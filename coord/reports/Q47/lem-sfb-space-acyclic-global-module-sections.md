## Worker report

The item is stated by `AlgebraicGeometry.AlgebraicSpace.isIso_acyclic_global_module_unit`
in `Sheaf.AlgebraicGeometry.SpaceAcyclicGlobalModuleSections`. Its proof is `sorry`, as
required in stage 2. The informal statement and proof are unchanged.

The conclusion is invertibility of a specified natural transformation in A-modules,
not an existence claim for abstract module isomorphisms. It is the unit of the composite
of the affine associated-module/global-sections adjunction and `moduleTensorAdjunction p`.
Thus its component at M has source M, target Gamma(X,p^* tilde(M)_et), and is natural
in every A-linear map. The affine associated-module adjunction inserts the canonical
section of M, and the p-adjunction inserts the unit tensor. Consequently this composite
is exactly the map in the node, under the canonical affine section identification.

Hypotheses and clauses, individually:

* The universe convention is `universe u`, with schemes, rings and module carriers in u,
  the presented small etale site in u+1, and `HasExt.{u+1}` for its additive sheaves.
  `HasSheafify` and `HasExt` record the structures used to form the specified cohomology,
  not a geometric condition on X. These are the same sizes as the landed 07V0 sibling.
* X over Spec Z is `X : AlgebraicSpace (Spec (CommRingCat.of (ULift.{u} ℤ)))`.
  The lift realizes the integers in the same universe as all test schemes.
* Quasi-compactness of the point space is `hqc : CompactSpace (Point X.obj.obj)`.
* Absolute quasi-separatedness is `hqs : IsAbsolutelyQuasiSeparated X`, the existing
  affine-scheme-test criterion equivalent to quasi-compactness of the absolute diagonal
  (Stacks 0AHR). This also imports the actual point topology, not an atlas surrogate.
* H1 vanishing for EVERY quasi-coherent module is `hH : ∀ (F : X.Modules)
  (_ : F.IsQuasicoherent), Subsingleton (Sheaf.H
  ((SheafOfModules.toSheaf X.structureSheaf).obj F) 1)`.
  This uses the underlying additive sheaf, not module-valued derived sections.
* A = Gamma(X,O_X) is given by `A : CommRingCat.{u}`, the cone `πA` on the diagram
  `X.etaleForget.op ⋙ Scheme.Γ`, and its limit proof `hA`. Compatible regular functions
  on all etale charts are precisely global functions. This specifies any representative
  of the global-function ring by its universal property, without requiring a huge
  product of all charts to be a u-small type by definition.
* The morphism to Spec A is `p : X ⟶ schemeSpace (Over.mk
  (specULiftZIsTerminal.from (Spec A)))`.
* Its identity action on A is `hp`: each cone leg is exactly the chart pullback along p
  composed with `(Scheme.ΓSpecIso A).inv`. In particular hA is not just an unrelated
  abstract isomorphism between A and global functions.
* The ordinary tilde construction is `tilde.functor A`, from the recorded Mathlib module.
  The associated etale MODULE on the represented scheme uses `evaluationZariskiExtension`, now owned in place by the new definition node;
  its affine specialization is the item-owned `affineEtaleAssociated A`.
* M tensor_A O_X is `(moduleTensorPullback p).obj ((affineEtaleAssociated A).obj M)`.
  It uses the existing canonical tensor pullback, with its specified unit.
* The canonical map u_M is the component at M of
  `((affineEtaleAssociatedAdjunction A).comp (moduleTensorAdjunction p)).unit`.
  The right adjoint is `moduleDirectImage p` followed by restriction to Zariski opens
  on Spec A and `moduleSpecΓFunctor`. Evaluating the latter on the whole affine is
  exactly compatible global sections on X, with the A-action induced by p.
* `IsIso` of this natural transformation asserts that EVERY component is an isomorphism
  of A-modules and that the component maps are natural. It does not claim the entire
  sheaf adjunction unit is an isomorphism, nor replace u_M by an unrelated map.
* There is no binder restricting M: the source functor category is all `ModuleCat.{u} A`.
  No finite generation, Noetherianity, or flatness binder occurs.
* The zero ring, zero module and empty space are permitted by the actual categories
  and predicates. No `Nontrivial A`, `Nonempty X`, or nonzero-module hypothesis occurs.

Dependency declarations read and used:

| DAG node | Module and declaration |
| --- | --- |
| def-weil-size-convention | Metatheoretic convention: explicit u and u+1, no Lean object |
| def-pc-scheme | Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom` |
| def-trf-algebraic-space | Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicSpace`, `EtaleSite`, `etaleForget`, `structureSheaf`, `Modules` |
| def-a1-space-point-topology | Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology: `pointTopologicalSpace`, on the existing `Point` |
| def-weil-pbc-sites-and-cohomology | Sheaf.CategoryTheory.SiteCoveringAxioms; existing Mathlib `Sheaf.H`, with the node's unchanged cohomology convention |
| def-trf-space-quasi-coherent-module | Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: `QCoh`, using Mathlib `SheafOfModules.IsQuasicoherent` and the published slice instances |
| def-weil-affine-spectrum | Mathlib.AlgebraicGeometry.Scheme: `Spec`, `Spec.map` |
| lem-weil-pbc-spec-module-tilde-sections | Mathlib.AlgebraicGeometry.Modules.Tilde: `tilde`, `tilde.toOpen`, `tilde.functor` |
| def-sc-etale-qcoherent-module | Upstream WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf: `Scheme.Modules.etaleTensorSectionsSheaf`; record and declaration unchanged |
| def-trf-space-etale-module-functors | Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations: `moduleDirectImage`, `moduleDirectImageModel`, `moduleTensorPullback`, `moduleTensorAdjunction`, `moduleTensorSection` |
| lem-trf-space-chart-adjunction-tensor-realization | Sheaf.AlgebraicGeometry.SpaceChartTensorRealization: `space_chart_adjunction_tensor_realization`, its `unitEquation` and `chartTensor` fields |
| def-sfb-space-absolute-quasi-separated | Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated: `IsAbsolutelyQuasiSeparated` |
| def-sfb-represented-scheme-zariski-etale-modules | Existing Sheaf.TraceFormula.GradedEvaluationZariskiEtaleComparison: `evaluationZariskiExtension`, `evaluationZariskiRestriction`, `evaluationZariskiAdjunction`, and their supporting site functor, instances, and proof context |

The absolute quasi-separatedness interface is an existing landed definition node.
The represented-scheme interface is the new definition node described below.
The theorem node `lem-trf-graded-evaluation-zariski-etale-comparison` is absent from
the item stmt_deps: none of its comparison conclusions is used in the signature.

Already stated proof dependencies are imported: Mathlib.AlgebraicGeometry.Modules.Tilde
(`tilde.adjunction`), Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
(`scheme_zariski_etale_quasiCoherent_equivalence`), Mathlib.CategoryTheory.Adjunction.Limits
(`Adjunction.leftAdjoint_preservesColimits`),
WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
(`moduleSheaves_colimits_forgetful`), and
WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
(`ShortComplex.ShortExact.exists_rightDerived_full_long_exact`).
The chart tensor module is already a public statement import. The two proof-only nodes
`lem-sfb-space-qcoh-kernels-colimits` and `lem-sfb-space-cohomology-filtered-colimit` have
neither Lean record nor Mathlib match in the read clone; no absent module was imported.
Their uses remain explicitly in the proof docstring for stage 3.

Edge cases checked before writing: M = 0; an empty free basis; arbitrary infinite-rank
free modules; A/I without a flatness assumption; X empty, whence A = 0 and every unital
A-module is zero. For affine X this recovers the usual affine section calculation.
A general projective space is not a counterexample: H1 of all quasi-coherent modules
need not vanish. The proof does not incorrectly require the free-presentation map
F1 -> F0 to be injective. The conclusion is natural in all module maps, including
identity maps and maps between zero modules.

Searches actually run (2026-10-24):

* msearch.py, leanfinder: “For a qcqs algebraic space with H1 vanishing for every quasi
  coherent module, the adjunction unit from M to global sections of M tensor O_X is an
  isomorphism”. Eight hits include Gamma-Spec affine isomorphisms, scheme open-restriction
  adjunctions and the general sheaf pullback-of-unit result. None states 07UZ for spaces.
* msearch.py, loogle: `SheafOfModules.unitHomEquiv`. Six hits give Hom(O,-)/section
  bijections and their compatibility with pushforward; none proves the required unit
  invertible under H1 vanishing.
* msearch.py, grep: `AlgebraicSpace|cohomologically.affine|vanishing.compute`, Mathlib
  AlgebraicGeometry. Zero hits.
* msearch.py, leansearch: “The canonical global section unit M to Gamma of M tensor O on
  a cohomologically affine algebraic space is an isomorphism”. Eight hits concern affine
  Gamma-Spec and `PresheafOfModules.unitHomEquiv`; none is the statement.
* rg in lean/WeilConjectures and lean/Sheaf for the item id, acyclic global modules,
  `vanishing.compute`, `cohomologically.affine`: only the landed 07V0 proof's citation of
  the present item. No existing declaration of the item.
* rg through algebraic-space modules for global sections, affine associated modules,
  scheme restriction, adjunctions and quasi-separatedness located the published helpers
  used here. `Scheme.Modules.affineEtaleAssociatedFunctor` in
  Sheaf.AlgebraicGeometry.AffineEtaleDerivedModuleRealization was read: its codomain is
  `SmallEtaleModules (Spec A)` on the SCHEME site, not `(schemeSpace ...).Modules`, and
  therefore it is not an interface for `moduleTensorPullback p`.
* The original full-name-suffix searches did not locate the differently named
  represented-scheme extensions. The returned review identified them; the repair search
  below supersedes that incomplete construction search.

## Repair of returned delivery 45fa0bda24d9

H2: the item previously cited the graded-evaluation theorem node merely to name
plain definitions from its module. The repaired item cites
`def-sfb-represented-scheme-zariski-etale-modules` instead. This new definition
node owns the existing definitions in place, including the supporting continuity
and equivalence instances and the proof-only `evaluationContext`. The module import
is unchanged because those are the published declarations being used. The full
item Lean file, both affine helpers, theorem signature, statement and proof are
byte-identical to the returned version. No conclusion of the graded-evaluation
theorem is a statement prerequisite.

The new node records `existing: true` rather than moving or copying declarations:
brief-stage2 §5 explicitly permits an existing module to receive a definition-node
owner in place. The module remains
`Sheaf.TraceFormula.GradedEvaluationZariskiEtaleComparison`; there are no duplicate
names or new functor constructions. The ordinary scheme-site structures separately
retain their existing owner `def-sfb-scheme-zariski-etale-module-constructions`.
The item's original clause audit above therefore remains valid.

The earlier H13 repair is preserved: the sandbox copy of
`def-sc-etale-qcoherent-module` is byte-identical to current live and contributes no
delivery delta. E1's `etaleTensorSectionsSheaf` record is not rebound. The alternate
`representedSchemeModuleExtension` in
`Sheaf.AlgebraicGeometry.AffineEtaleNaiveCotangentPresentation` was also considered:
it has target `SmallModules`, whereas the current pullback uses `Modules`.

## New nodes

`def-sfb-represented-scheme-zariski-etale-modules` defines the Yoneda inclusion from
the ordinary small etale site of a scheme T/S into its represented algebraic space's
site, restriction of module sheaves along this inclusion, the existing proof-only
Zariski/etale context, and represented-scheme Zariski restriction, tensor extension,
and their specified composite adjunction. It records all eight declarations:
`evaluationSchemeEtale`, `evaluationSchemeEtale_continuous`,
`evaluationEtaleRestriction`, `evaluationEtaleRestriction_isEquivalence`,
`evaluationContext`, `evaluationZariskiRestriction`, `evaluationZariskiExtension`,
and `evaluationZariskiAdjunction`. The unit is the unit of that actual composite,
which inserts a unit tensor; it is not an arbitrary natural transformation.

Its sources are Stacks Descent 03FH, the ringed-site tensor-pullback interpretation,
03DX, the small-etale quasi-coherent comparison, and 0GN7, whose proof identifies
restriction on opens and its adjunction. The local source was read at
`remark-change-topologies-ringed-sites`, `proposition-equivalence-quasi-coherent`,
and `lemma-fully-faithful-associated`. The site equivalence is Yoneda's identification
of the same etale scheme charts with unchanged rings and covering families.

Every informal clause is rendered by the recorded declarations: S and T/S are the
explicit `variable {S : Scheme.{u}}` and `(T : Over S)`; the ordinary and represented
sites are the domain and codomain of `evaluationSchemeEtale`; its `obj` and `map`
are Yoneda maps; continuity is `evaluationSchemeEtale_continuous`; ring restriction
is `SheafOfModules.pushforward ... ⟨𝟙 _⟩` in `evaluationEtaleRestriction`; its
presentation equivalence is `evaluationEtaleRestriction_isEquivalence`. The context
has only the two proof fields from the existing ordinary-site definition node.
`evaluationZariskiRestriction` is `evaluationEtaleRestriction T ⋙
(evaluationContext T).restriction`; extension is `(evaluationContext T).extension ⋙
(evaluationEtaleRestriction T).asEquivalence.inverse`. The adjunction is the ordinary
context adjunction composed with the inverse equivalence adjunction, retaining both
unit and counit. All module sections remain in u while the presented site objects
are in u+1. No extra hypotheses occur. The unit tensor interpretation follows from
the ordinary tensor pullback and equivalence adjunction used in its definition.
For arbitrary modules the extension is sheafified tensor pullback; quasi-coherent
modules have the usual tensor-section description by descent.

Searches recorded in the new node: LeanSearch for represented-scheme Zariski/etale
extension and its unit returned eight scalar-change or ordinary restriction results;
LeanFinder for the same adjunction returned eight ordinary scheme-module results;
msearch grep for `zariskiEtale|evaluationZariski|representedSchemeModuleExtension`
in Mathlib AlgebraicGeometry returned zero. Project rg located the eight existing
declarations in the graded-evaluation module, no upstream copies, and no definition
node owning these represented-site constructions. Blueprint searches and a search
of the DAG definition files found the ordinary-site owner and affine-basis variant,
but no exact represented-site owner. The full queries and results are in
`mathlib_searches`. Hence the declarations are reused as existing, while the missing
DAG definition owner is supplied. `blueprint_refs.py ancestor` reports no imported
ancestor for this item; the new node preserves its null ancestor and prepends the
item to the existing via chain, with the Tag 07UZ construction place identified.

New-node edge cases checked: arbitrary S and T/S, empty T, zero coordinate rings,
non-quasi-coherent modules, and coefficients in universe u on the site with object
universe u+1. Continuity, site equivalence and existence of the ordinary tensor
adjoint are included among the existing supporting proof obligations; no module,
functor or map data are supplied by a sorry. The existing context has only proof
fields, and all chosen adjoints/equivalence inverses are fixed by their stated
universal properties. A graph traversal checks that the new definition's dependencies
do not reach the item.

The unchanged item module is compiled through the prescribed scompile.py; the new
node records existing declarations and delivers no copied Lean file. The prescribed
dry run and delivery wrapper verify the packet. There are no disputed statements,
source corrections, dependency-record repairs, direct git commands or live edits.

## Second reading by Q47

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
