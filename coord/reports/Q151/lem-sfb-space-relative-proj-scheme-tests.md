## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceRelativeProjSchemeTests` states
`AlgebraicGeometry.AlgebraicSpace.exists_space_relativeProj_scheme_tests` with `sorry`.
The conclusion is the existence of a normalized coefficient system `C` and a
`SpaceProjSystem C`. The auxiliary structures spell out this single theorem's
coefficient objects, comparison arrows and equations. They are conclusion data,
not additional assumptions. No new independent notion or dependency repair is needed.
The accepted Q73 stage-1 split, its statement and dependencies are preserved.
The previous worker's stage-1 unchanged-split refusal does not apply: this is the
stage-2 statement assignment described in brief-stage2 §0.

Hypotheses and every clause:

- A scheme S is `(S : Scheme.{u})`; X ranges over `AlgebraicSpace S`. There is one
  explicit universe `u`, as in the recorded algebraic-space interface. Schemes,
  section rings and tests have the same `u`; the large sites and categories retain
  their existing object and morphism universes. No smaller test universe is used.
- A commutative unital graded small-etale algebra is `SpaceProjInput.piece` with
  `SpaceProjInput.algebra : EtaleGradedModuleAlgebra piece`. Its degreewise
  quasi-coherence is `SpaceProjInput.quasiCoherent`, the existing
  `SheafOfModules.IsQuasicoherent` predicate. Bundling these assumptions does not
  add or discard a hypothesis. No existence of a coproduct of sections is assumed.
- Tensor pullback is precisely `moduleTensorPullback f`. `SpaceProjPullback`
  supplies products and units on these fixed homogeneous modules, with local
  formulas `(b tensor s)(c tensor t)=bc tensor st` and the scalar unit formula.
  `SpaceProjPullback.input` merely bundles these actual modules and operations.
- Degreewise Zariski passage is the existing `evaluationZariskiRestriction W`,
  composed with tensor pullback along the scheme test g. The affine presentation
  in `SpaceProjSchemeAlgebra` identifies each homogeneous piece by a linear
  equivalence to sections of exactly this module. Its `mul`, `unit` and
  `restriction` equations retain the given algebra operations and restrictions.
  Thus its affine graded algebra is the usual Zariski algebra, rather than an
  arbitrary chosen algebra with a similar Proj.
- `SpaceProjCoefficients` simultaneously supplies these normalized pullbacks and
  scheme algebras. `identity_degree`, `composition_degree`,
  `isoPullback_degree`, `schemeIso_degree`, `schemeComposition_degree` and
  `schemeBaseChange_normalized` fix every comparison on the existing tensor
  modules or actual homogeneous sections. The scheme base-change normalization
  tests the actual restricted scheme map on every pair of affine opens. `HEq`
  handles the canonical chart identifications, without identifying universes.
- The algebraic space P and its map p are `SpaceProjRealization.space` and
  `.projection`. `.representable` is the recorded `IsRepresentable` predicate
  on the actual presheaf map, meaning representable by schemes, with all tests.
- For every S-scheme W and g:W to X, `.compare W g` maps the ordinary relative
  Proj to P. `.cartesian W g` is the scheme-test comparison: its other projection
  is `yoneda.map (spaceProjSchemeProjection W ...)`, the actual relative-Proj
  structural morphism. The pullback universal property gives the requested
  W-scheme isomorphism (in the opposite direction by inverse). The scheme Proj
  is the dependency's `Scheme.GradedAlgebraData.relProj`, on the normalized
  affine presentation. It never assumes degree zero equals the structure sheaf.
- Commutation with every further scheme base change is `.naturality a g`.
  The map on its left is `spaceProjSchemeBaseChange` of the ordinary normalized
  `GradedAlgebraData.PullbackData`; it is the published ordinary scheme-Proj
  comparison. `.cartesian` specifies both projections, including the map to W.
- Unique characterization is `SpaceProjSystem.unique`: for every second
  realization Q there exists exactly one isomorphism preserving p and every
  scheme comparison. It does not claim an unrestricted unique isomorphism.
- For every morphism f:Y to X, `.baseChange f A` and `.baseChange_cartesian f A`
  give the cartesian square with P_Y(f-star A) as its vertex. The definition
  `SpaceProjSystem.baseChangeIso` extracts the actual algebraic-space isomorphism
  to `baseChangeTarget`, whose underlying sheaf is `Y times_X P_X(A)`.
  The fibre-product algebraicity proof is the recorded `fibreProduct_isAlgebraicSpace`.
- Compatibility with scheme tests is `.baseChange_test`; the ordinary-Proj
  comparison comes from `.schemeComposition`, normalized degreewise by the
  inverse of `moduleTensorComposition`. Identity is `.baseChange_id`, using
  `.identity` normalized by the published `moduleTensorPullbackId`. Composition
  is `.baseChange_comp`, using `.composition` normalized by the published
  `moduleTensorComposition`. These arrow equations express precisely the usual
  projection-preserving identity and fibre-product associator compatibilities.
- For every graded algebra isomorphism e, `SpaceProjGradedIso` states degreewise
  module isomorphisms preserving the given products and unit. `.iso e` has
  direction P(B) to P(A). `.iso_over` puts it over X; `.iso_test` identifies it
  on every scheme test with the ordinary `relProjIsoOfIso` induced by e.
  `.baseChange_iso` is the graded-isomorphism/base-change commutative square.
- No finite generation, flatness, Noetherian, separation, quasi-compactness or
  nonemptiness condition occurs on the inputs. The coefficient and comparison
  structures are existentially asserted in the conclusion for ALL inputs.

Dependency declarations used (source signatures and docstrings inspected):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, its small-etale
  `Modules`, `EtaleSite`, `structureSheaf`, and `IsRepresentable`.
- `def-weil-size-convention` is a convention, not a declaration. The explicit
  universe binders and the existing site's distinct sizes render it.
- `Sheaf.TraceFormula.EtaleGradedModuleAlgebra`: `EtaleGradedModuleAlgebra`,
  including its homogeneous multiplication, scalar, restriction and unit laws.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: the slice
  instances for Mathlib's `SheafOfModules.IsQuasicoherent`; this is the predicate
  underlying `AlgebraicSpace.QCoh`, with no private copy.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `moduleTensorPullback`, `moduleTensorSection`, `ModuleChart`, `moduleChartScalar`.
- `Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence`:
  `ZariskiEtaleModuleContext.restriction` and
  `scheme_zariski_etale_quasiCoherent_equivalence`.
- `Sheaf.TraceFormula.GradedEvaluationZariskiEtaleComparison`:
  `evaluationZariskiRestriction`, `evaluationSchemeEtale`, `evaluationSchemeMap`.
  These are the already normalized realization of that same scheme equivalence,
  retaining the actual ring map and restrictions, not a second equivalence.
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic` and `GradedAlgebraData`:
  `Scheme.GradedAlgebraData`, `relProj`, `relProjHom`, `relProjι`.
  The recorded affine presentation is used directly. The dependency's sheaf-input
  bridge module `Sheaf.AlgebraicGeometry.RelativeProjAffineRestriction` is imported.
- `WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange`:
  `GradedAlgebraData.PullbackData`, `.relProjComparison`, `.isPullback`.
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality`:
  `GradedAlgebraData.relProjIsoOfIso`, its structural projection equation.
- `Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange`:
  `moduleTensorComposition`, with its tensor-normalized universal property.
- `Sheaf.AlgebraicGeometry.SpaceDerivedPullback`: `moduleTensorPullbackId`.
  This is the ordinary tensor identity from that module, not a new identity.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`.

Plain proof imports include the recorded quasi-coherent pullback theorem, ringed
module tensor comparison, invertible pullback/tensor theorem, module tensor
adjunction and preservation of colimits by left adjoints. The two proof nodes
`lem-sfb-scheme-proj-veronese-quotient-functor` and
`lem-sfb-presheaf-space-target-bootstrap` currently have no recorded Lean modules;
there are consequently no imports for them. They are proof prerequisites only,
and their exact uses are retained in the theorem's full proof docstring.

Edge cases checked against the source and signature:

- Empty X, empty scheme tests and empty P are allowed; no `Nonempty` input or
  point is required. `Nonempty (SpaceProjSystem C)` is the theorem's existence
  conclusion and does not assert nonempty points of its spaces.
- Algebras concentrated in degree zero (including the zero algebra) have empty
  Proj; no degree-one-generation or nonzero-ring condition is introduced.
- Degree zero may be any algebra, not O_X. The base projection uses the given unit.
- Infinite generation, non-quasi-compact spaces and non-separated spaces are
  allowed. The source proof's compatible families over quasi-compact opens
  avoid assuming quasi-compact intersections.
- Arbitrary base change includes nonflat maps and identities. Iterated pullback
  is compared by the existing normalized compositor, never by definitional equality.
- The graded isomorphism is contravariant on Proj, as the source requires.

Searches for an exact existing declaration:

- `msearch.py ... leanfinder "Relative Proj of a quasi-coherent graded algebra on
  an algebraic space with scheme tests and arbitrary base change"`: 8 results,
  all ordinary graded-ring Proj, its structure sheaf, charts, or structural map.
- `msearch.py ... loogle "AlgebraicGeometry.Proj, AlgebraicGeometry.Scheme"`:
  12 results, ordinary Proj and standard-open identities; none for spaces.
- `msearch.py ... grep "relativeProj|RelativeProj|relProj|AlgebraicSpace"
  AlgebraicGeometry`: zero results from the search wrapper.
- Local `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `AlgebraicSpace.*[Pp]roj|[Pp]roj.*AlgebraicSpace|space_relative[Pp]roj`:
  no matching theorem. Related hits are ordinary scheme relative Proj and the
  line-module canonical-map construction, which do not assert representability
  of relative Proj on an arbitrary algebraic space.
- Further source reads covered `RelativeProj/Basic`, `GradedAlgebraData`,
  `Functoriality`, `BaseChange`, the etale graded algebra and the scheme
  Zariski/etale comparison, to reuse the exact recorded constructions.

Sources read: Stacks `spaces-divisors.tex`, Situation 084A, the quadruple
construction, Tags 084B/084C and 085C and the intervening graded-isomorphism
diagram. The current blueprint `latest/.../sk-thm-sf-ctf-stability.proof.md`
retains the compactification/direct-image route served by this subordinate node.
No statement correction or statement dispute is needed.

Validation: the module is compiled only using `scompile.py`, under its normal
per-file limit. The final dry run and delivery use `deliver2.py`.

## Second reading by Q151

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
