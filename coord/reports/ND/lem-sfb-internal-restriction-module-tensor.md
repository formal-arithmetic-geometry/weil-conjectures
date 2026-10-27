## Worker report

The module `Sheaf.CategoryTheory.InternalRestrictionModuleTensor` states the node in
`CategoryTheory.InternalActionSite.internalRestrictionModuleTensor`, using the existing
small action sites and section-pinned module presentations. Its only postponed proof is
that theorem. Definitions have real data: three specification structures, a Prop-valued conjunction of pullback laws, the
existing monoidal unit map, a composition of section maps, and a proposition spelling
out diagonal tensor compatibility.
No mathematical statement correction is intended. The returned interface is repaired below.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The chosen V-small universe is `universe u`, with `C : Type u`, `SmallCategory C`,
  group sections `GrpCat.{u}`, ring sections `CommRingCat.{u}` and module sections in u.
  The base site is `J : Precoverage C`, `hJ : J.IsSiteForCoverings`; its sheaves use
  `J.toGrothendieck`. Finite limits are `[HasFiniteLimits C]`.
- K and L are the functors with `hK`, `hL` their underlying set-sheaf conditions.
  `θ : L ⟶ K` is the natural group homomorphism. R is the commutative ring sheaf.
- `Fθ`, `hθobj`, `hθmap` specify the action restriction functor on the existing
  action sites: same base objects, and `(f,a)` maps to `(f,θ(a))`. This is input
  notation for the specified restriction construction, not an arbitrary map.
  Object equalities require heterogeneous equality for arrow maps. There is no
  duplicate definition of the parent's already recorded `restrictionSite`.
- `PK` and `PL` are the dependency's actual `Presentation` records. They are
  universally quantified, so the statement works for every section-pinned presentation.
  Their existence is the already stated `presentation` theorem. `hp` and `hq` are
  the coefficient sheaf proofs supplied by those presentations. `hqR` records the
  identity coefficient identification after label substitution; it is definitional
  for the literal restriction functor. Scalar restriction along `eqToIso hqR` merely
  transports the category across this identity; it does not change coefficients.
- `p` and `q` are `InternalPrecompositionMorphism` records. Their `ringed` field
  uses the recorded `RingedToposMorphism`, and `inverse` specifies precomposition
  on objects AND maps. `structural` says its structural ring map is the identity.
  Thus geometric existence is a hypothesis, exactly as in the node.
- The conclusion supplies `P` and `Q : InternalExactTensorPullback` for these
  GIVEN geometric morphisms. Their `core.algebraic` fields use the existing
  `AlgebraicInverseImage`, including transport of every ring/module operation.
  The first conjunct of `InternalModulePullbackLaws` pins it to the given structural identity. `core.sections` and the second conjunct of `InternalModulePullbackLaws` pin section
  identifications to inverse image; its third and fourth conjuncts retain every
  restriction and every original component map.
- `core.pullback`, `core.objects`, `core.adjunction` give the actual module pullback with
  `R tensor_R f^{-1}M`, not an abstract exact functor. The natural isomorphism
  `core.unitor` identifies it with inverse image. The fifth law is `r tensor m ↦ r • m`
  and the sixth law is `m ↦ 1 tensor m`, using the existing scalar-extension
  sheafification helper `ringedComparisonScalarSection` and explicit object casts.
- The main theorem's two natural isomorphisms identify those pullbacks with the
  EXISTING `trivialSheafAction` and `inflateSheaf θ`, conjugated by `PK`, `PL`.
  They are supplied as `ep` and `eq`, with section equations specified below.
  No specialization to constant groups or injective/surjective theta is made.
- The final three pullback laws give additivity and preservation of kernels and
  cokernels (indeed all finite limits and colimits), hence exactness in the stated
  abelian module categories. The two `ActionForgetExact` conjuncts in the main theorem give creation of kernels
  and cokernels, the `sectionwiseKernel` evaluation comparison, and the
  `sheafifiedCokernel` comparison with module sheafification of the presheaf
  cokernel. Their induced actions and base sheaves are those of the presentation.
- `InternalDiagonalTensor` asserts a tensor object H with actual base and action-site
  tensor comparisons. Its first formula is precisely `a(x tensor y)=ax tensor ay`.
  Its second formula matches action-site pure tensors with base pure tensors through
  `internalPresentationSection`, the composition of `P.underlying` and `P.sections`.
- `comparison` is the EXISTING `CanonicalRingedTensorComparison`, with its
  generalized pure-tensor formula, scalar insertion, and simultaneous naturality.
  `tensor_pure` states the identity on presheaf pure tensors after the multiplication
  unitor. `ringedComparisonPure` explicitly uses presheaf tensor followed by module
  sheafification, so the comparison is not an arbitrary isomorphism.
- `coherence` supplies a monoidal structure with associativity, left/right unit
  coherence and naturality; its first equation ties exactly that monoidal structure
  to `comparison.mu.inv`, the
  direction `f*M tensor f*N → f*(M tensor N)` in the node. The second coherence equation is its braiding equation. The third says its regular
  coefficient unit comparison is identity, using `internalRegularUnitMap` (the
  existing monoidal unit map with the definitionally equal regular-module type).

Dependencies read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`.
- `Sheaf.CategoryTheory.InternalActionSitePresentation`: `Presentation`, `presentation`,
  `sections`, `underlying`, `sheafEquivalence`, `coefficientSheaf`, `projection`,
  `Object`, `Arrow`, `topology`, `baseRing`, and the existing action categories.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.CategoryTheory.RingedToposMorphism`: `CategoryTheory.RingedToposMorphism`.
- `Sheaf.CategoryTheory.InternalActionInflation`: `inflateSheaf`,
  `restrictLinearAction`, `ActionForgetExact` and `trivialSheafAction`, owned by
  the landed `def-sfb-internal-action-inflation` with existing:true. The original
  action theorem modules publicly re-export these definitions.
- `Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses` re-exports the applicable
  common-universe `SheafOfModules.AlgebraicInverseImage` without identifying any
  originally distinct universes: the node expressly fixes one V-small site and values.
- `Sheaf.Paper.RingedTopoiTensorComparisonData`: `CanonicalRingedTensorComparison`,
  `ringedComparisonPure`, `ringedComparisonScalarSection`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: the existing
  monoidal and symmetric sheaf tensor and its unit, not a new tensor definition.
- Mathlib `Algebra.Category.ModuleCat.Presheaf.Sheafification`: `sheafification`,
  `sheafificationAdjunction`; its `Presheaf.Colimits` provides sectionwise cokernels.
- Proof imports retain `module_pullback_pushforward_adjunction`,
  `tensor_bilinear_universal`, `tensor_trilinear_universal`. The set-action
  equivalence node currently has no Lean record; its future proof import is omitted.
  The parent `ActionToposGeometricRestriction` is not imported: its DAG proof depends
  on this item. Its existing restriction-site and coefficient definitions were read.

Searches (2026-10-24):

- `msearch.py ... leanfinder "Trivial inflation and restriction of internal group
  actions on module sheaves are exact symmetric monoidal"`: 8 hits, ordinary
  `Rep` adjunctions and `Action.leftRegularTensorIso`; none states this internal
  action sheaf/module normalization.
- `msearch.py ... loogle "SheafOfModules, CategoryTheory.Functor.Monoidal"`: 0 hits.
- `msearch.py ... grep "(tensor|Tensor).*(restrict|Restrict)|[Ee]xact.*(action|Action)"
  Algebra/Category/ModuleCat`: 3 hits on ordinary scalar restriction, no match.
- `msearch.py ... leansearch "Restriction of internal group actions on module
  sheaves is exact and symmetric monoidal"`: 8 hits on `Mod_.scalarRestriction`,
  `SheafOfModules.restrictScalars`, ordinary `Action.res`, `ContAction.res`, and Rep
  adjunctions; none gives the item.
- `rg` in `lean/WeilConjectures` for internal restriction/inflation, `InternalActionSite`
  and the node ID: no matching declaration; unrelated internal-Hom restriction hits.
- `rg` in `lean/Sheaf` finds the action-site presentation, existing inflation and
  trivial-action constructors and the parent's geometric restriction package.
  The parent package lacks the full regular unitor and coherence assertion of this
  item and depends on this item in the DAG, so it is not an existing exact match.
  Every reused owning node has been added to `stmt_deps` where needed.
- New public declaration names checked by `rg` in Mathlib, WeilConjectures and Sheaf:
  no collision. Before return, no new independent definition node was supplied: the local declarations
  merely expand this theorem's assertion and compose the recorded section maps.

Edge cases: K=L=1 gives ordinary identity pullback and regular-ring multiplication;
L=1 gives forgetting an arbitrary K-action; θ need not be injective or surjective.
R=0 makes every section module zero and retains the same unit/tensor formulas.
Empty covering families and non-subcanonical sites are handled by the existing
Grothendieck sheafification, without enough-points, flatness or stalk hypotheses.
The formulas quantify over every object and every local section, not only globals.
There is no characteristic restriction and no independent smaller coefficient universe.

Source inspection: current `literature/blueprint/latest/...direct-images.proof.md`
paragraph (3), and Stacks `sites-modules.tex` labels
`lemma-adjoint-pullback-pushforward-modules` (03D7),
`lemma-sheafification-presheaf-modules` (03CY), `lemma-abelian` (03DA),
`section-tensor-product` (03EK). The finer categorical infrastructure is the
agent-written node proof; all six steps are retained in the theorem docstring.

No STATEMENT-DISPUTED flag or statement correction.

## Second reading by ND

This is the worker's own second pass; the dispatch brief prohibits starting another
agent, and independent delivery review is the maintainer's responsibility. I checked
all clauses against the node and the actual dependency declarations. Corrections made
in this pass: added the explicit natural identifications with existing inflation and
restriction; pinned sections to algebraic inverse image; included both the normalized
canonical comparison and its monoidal coherence; made scalar insertion and the unit
comparison explicit; retained the action-site/base diagonal tensor formula. Avoided
redeclaring the parent module's restriction functor by specifying its complete object
and arrow formulas as data and transporting across its identity coefficient equality.

Compilation repair: record generation was expensive for a single dependent record
containing all pullback laws. Factored the data into `InternalModulePullback`, its
complete equations into the real Prop definition `InternalModulePullbackLaws`, and
the tensor comparison into `InternalExactTensorPullback`. Kept monoidal structure
irreducible after defining its regular-module unit-map interface. No compile time
limit was increased and no clause was removed. The final complete module compiled cleanly in sandbox mode (30.4 s) and library
mode (17.9 s), with only the expected sorry warning allowed. The delivery dry run
repeats compilation and runs the server preflight.

## Returned delivery repair

H2 is resolved by the landed maintenance extraction. The existing definition node
`def-sfb-internal-action-inflation` owns restrictLinearAction, inflateSheaf,
ActionForgetExact and trivialSheafAction in
`Sheaf.CategoryTheory.InternalActionInflation`. Their signatures and bodies,
including the already published naturality proof, are unchanged. Both original
theorem modules publicly re-export that module. The main module imports this
owning definition module directly and cites the definition node in stmt_deps.
The two theorem nodes are absent from stmt_deps; neither conclusion is needed.
This packet delivers only the consumer module and its node record. The extraction
and its existing:true ownership record are already on current main, and unchanged
copies of their nodes have been removed from the sandbox.

H3 is resolved by existential isomorphism data `ep` and `eq` with identity-on-sections
equations. For every base module M, base object X and pullback section m, the first
equation identifies `internalPresentationSection PK` of `ep.hom m` with
`P.core.sections M` of `P.core.unitor.hom m`. The second applies
`internalPresentationSection PL` to `eq.hom m`, then `PK.inverseSections M X`,
and equates this with `Q.core.sections M` of `Q.core.unitor.hom m`, transported
along the specified object equality hθobj. Scalar restriction changes no carrier.
Thus both isomorphisms are pinned to the identity on the specified sections.
No accepted pullback, tensor, exactness or coherence clause was changed.

The worker's second pass checked these equations against the full presentation
and algebraic inverse-image signatures. Trivial groups, identity theta, arbitrary
kernel of theta and the zero ring remain included. The natural-language statement
and proof are unchanged from current main. There is no new statement correction,
new definition node or dependency module in this final packet.

Validation: all four files of the original extraction repair compiled separately
through scompile.py. After maintenance landed that extraction, the live delivery
dry run passed preflight and compilation (e93157a4b52). The earlier proof-transfer
gate failure is resolved by that maintenance landing, without changing the published
proof. The final report and reduced packet are rechecked before delivery.
