## Worker report

The delivery states `WeilConjectures.fdCompletedCompositorNormalization` in
`Sheaf.Paper.FdCompletedCompositorNormalization`. Its only postponed proof is the
named main theorem. The seven-step proof docstring follows the node's proof.
The auxiliary structures specify the same comparison data appearing in this
node, not independent replacement operations. They are existential conclusions,
not assumed comparisons. All definitions contain real data; no definition uses
`sorry`. No statement correction or disputed mathematical claim is recorded.

Hypotheses and clauses, in statement order:

- The prime is `l` with `[Fact l.Prime]`. `Omega` has its field, Q_l algebra and
  `IsAlgClosure` instances. `E0 : Padic.FiniteCoefficientFields l Omega` selects
  exactly a finite coefficient subfield; `pbcFiniteField.{u}` is its existing
  size transport. `D : IntegralComparisonSystem.{u} l` specifies the existing
  normalized whole-system realization used for `c^s` and `u^s`; it is not an
  additional geometric assumption.
- `U V T : Scheme.{u}`, the three `IsNoetherian` instances, the three finite
  `topologicalKrullDim` facts and the three stalk-unit facts render precisely
  the geometric assumptions. The published `fdResidueInvertible` instance
  derives the residue-field inverses needed by the framework API from those
  stalk-unit facts. No residue-field assumption is added.
- `h : U ⟶ V`, `k : V ⟶ T` with `IsIso` instances render the composable scheme
  isomorphisms; `𝟙 T` supplies the identity case. There is no nonidentity or
  nonempty-scheme restriction.
- The fixed identity transport `I` is `integralDetailedTransport`, namely the
  derived restriction along `integralDetailedCoefficientComparison.hom`.
  `fdCoefficientTransport` and `fdCoefficientTransportFactors` expose its
  module and localization presentations without defining a new transport.
- `integralOperationsPullbackTowerFunctor` is the actual finite-reduction,
  finite-pullback and restricted tower, with its quotient transitions.
  Natural index `n` denotes positive exponent `n+1`, including the first
  quotient. Its whole Roos complex is `integralOperationsPullbackComplexFunctor`.
  `FdCompletedPullbackNormalization.tower` identifies the entire transported
  diagram with the PBC pulled reduction diagram `IntegralPullbackStrictRoos.cxT`.
  `towerGenerators` fixes this identification on quotient tensor-unit sections;
  being a natural isomorphism includes all transitions and all complex maps.
- `FdCompletedRoosNormalization.rho` is a natural isomorphism from the actual
  `roosF` to total derived limit. `inclusion` and `coordinates` use the existing
  `IsUnitNormalized`, whose degree formula is exactly zero in the shifted
  coordinate and the ordinary limit tuple in the other coordinate.
  `resolution` quantifies over every quasi-isomorphic tower map into a
  K-injective tower with injective terms. `epsilon.hom` is the localized
  inclusion, `delta` is fixed by the universal derived-limit unit and the
  resolution, and the last equality reads `H(q) ≫ epsilon.inv ≫ delta.hom`.
  This is the displayed normalized rho formula, with its derived-limit
  endpoint written explicitly.
- The framework and PBC presentations are not identified by definitional fiat.
  `ordinaryModules` is fixed by `ordinarySections`: on the canonical comma
  chart it sends the actual PBC tensor unit to the same section. The field
  `ordinaryComputes` fixes its derived lift on every good K-flat representative
  using the actual derived counit, with each component of its chain map equal
  to the module comparison. `ordinary` is consequently the specified ordinary
  pullback in the two coefficient presentations.
- `strict` and `strictUnit` identify the actual strict PBC reduction/limit
  formula with the actual completion reflector, preserving the actual unit on
  every ambient object. This is stated for isomorphisms, as in this node.
- `comparison` is `b^amb`, with the direction `F^s ⋙ I ≅ I ⋙ F^p`.
  Its `cone` comparison has both coordinates specified by `coneCoordinates`,
  using `mappingCocone.snd`, `mappingCocone.fst` and the product map induced by
  the entire tower isomorphism. `realization` fixes `b` on every good K-flat
  representative by the existing framework realization, coefficient descent,
  this whole-cone map, normalized rho, and the actual PBC reduction/pullback
  counits. It is not specified merely by equality of isolated reductions.
- `augmentation` is the unsuppressed equality `I(kappa^s) ≫ b = ordinary ≫
  kappa^p` for every ambient derived input, with no completeness condition.
  The maps are exactly `inverseImagePullbackComparisonDerived` and
  `pbcActualCompletedPullUnit`. `frameworkComplete` and `pbcComplete` assert
  their invertibility for every `IsDerivedCompleteUnrestricted` input.
- `fdCompletedPull` is the actual completed pullback restricted to complete
  subcategories. `fdCompletedDirect` uses actual derived direct-image maps.
  `FdCompletedAdjunction` concludes preservation and an adjunction whose
  `transpose` is exactly the ordinary derived Hom transpose after the actual
  completion unit. `FdCompletedConjugate` lifts the fixed actual direct-image
  compositor and identifies its adjunction conjugate with the inverse of the
  published `pbcActualCompletedPullCompIso`. Thus `c^p` is the actual conjugate,
  not an arbitrarily supplied isomorphism satisfying a formal coherence law.
- The first equation under `hK` identifies the ordinary sectionwise compositor
  with `pbcActualDerivedPullCompIso` through `bh`, `bk` and `bhk`'s ordinary
  transports. The latter is defined by its K-flat counit equation with
  `pbcActualModulePullCompComplexIso`; that module comparison is the conjugate
  of the fixed direct-image pasting. Its finite reductions are the termwise
  tensor-generator compositor, without changing the quotient transitions.
- The next conjunct is the framework equation
  `kappa^s_kh ≫ c^s = c^G ≫ kappa^s_h(G_k K) ≫ F^s_h(kappa^s_k)`.
  It uses the exact existing `integralInverseImageDerivedComposition.inv` and
  `integralComparisonComposition`, and explicitly applies `I`.
- The next conjunct is the PBC equation
  `kappa^p_kh ≫ c^p = c^G ≫ kappa^p_h(G_k I K) ≫ F^p_h(kappa^p_k)`.
  Here `c^p` is the inverse of the published forward compositor, and `hK`
  supplies its actual complete-domain object.
- The next conjunct is the unsuppressed integral compositor equation
  `b_kh ≫ c^p = I(c^s) ≫ b_h(F^s_k K) ≫ F^p_h(b_k)`.
  `K : sfIntegralConstructibleCategory ... T` is the full common integral
  category, and the conclusion `hK` identifies its transported object as PBC
  complete. Writing the equalities after the full inclusions states the
  restrictions `b^int` without introducing an additional comparison.
- The final three conjuncts are respectively the framework identity unit
  normalization, the PBC identity unit normalization, and
  `b_1 ≫ u^p = I(u^s)`. Their ordinary identity is precisely
  `pbcActualDerivedPullIdIso`, through `b1.ordinary`. The completed identity is
  `pbcActualCompletedPullIdIso`; the framework identity is exactly
  `integralComparisonUnit`.
- Ambient augmentation and complete-input invertibility are separate fields.
  Compositor and identity equalities use the published complete-domain maps.
  No inverse or cancellation of an ambient completion unit on an incomplete
  object occurs in the statement.

`HEq` is used only for equality of the explicitly written morphisms in the
canonically identical complex/localization presentations; it avoids expensive
elaboration of the presentations' definitional equality. It does not compare
isomorphism classes or weaken equality of maps. The same convention is used in
the existing finite comparison datum. Universes retain the actual small
pro-etale site, with object universe `u+1` and morphism universe `u`.

Dependency declarations used (including the newly cited landed owners):

- Mathlib `DerivedCategory.Basic`: `DerivedCategory`, `DerivedCategory.Q`;
  `HomotopyCategory.KInjective`: `CochainComplex.IsKInjective`;
  `Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`;
  `Adjunction.Mates`: `conjugateIsoEquiv` (the isomorphism version of
  `conjugateEquiv`).
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and its actual coefficient rings.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`, through the existing good
  complex predicate.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`, retained via the completed
  coefficient construction and its existing module imports.
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`:
  `integralStratifiedPerfectCharacterization`, `integralDetailedTransport`,
  `integralDetailedCoefficientComparison`.
- `Sheaf.Paper.DerivedPullbackTensorHom` and `IntegralDerivedOperationsOnSlices`:
  the existing `integralDerivedPullback`, `integralDerivedPullbackComparison`,
  `integralOperationsPullbackTowerFunctor`, and slice completion interface.
- `Sheaf.Paper.InverseImagePullbackComparisonDerived`:
  `inverseImagePullbackComparisonDerived`, `inverseImageIntegralModules`,
  `inverseImageIntegralDerived` and the specified augmentation.
- `Sheaf.Paper.IntegralPullbackComparisonRealization`:
  `IntegralComparisonSystem`, `integralComparisonComposition`,
  `integralComparisonUnit`.
- `Sheaf.CategoryTheory.StrictRoosComparison`: `strictRoosComparison`;
  `StrictRoosModel`: `roosF`, `roosχ`.
- `Sheaf.Paper.PbcQbarCompletedPullback` and its published actual interfaces:
  `pbcActualCompletedPull`, `pbcActualCompletedPullUnit`,
  `pbcActualDerivedPull`, `pbcActualDerivedAdjunction`,
  `pbcActualStrictCompletedPull`, `pbcActualStrictCompletedPullUnit`,
  `pbcActualModuleUnitSection`, `pbcActualPullComplexCounit`.
- `Sheaf.Paper.PbcActualRingedExchange`:
  `pbcActualDerivedPullCompIso`, `pbcActualDerivedDirectCompIso`,
  `pbcActualCompletedPullCompIso`, `pbcActualDerivedPullIdIso`,
  `pbcActualCompletedPullIdIso`.
- `Sheaf.Paper.CompletedPullbackAdjunction`:
  `CategoryTheory.ConstantCompletion.completedPullbackAdjunction`;
  `ConstantCompletionEquivalence`: `CategoryTheory.ConstantCompletion.equivalence`.
  These proof interfaces are retained; the statement spells out their
  completion-induced Hom transpose on the actual site universes.
- `Sheaf.Paper.FdCoefficientComparison`: `fdCoefficientTransport`,
  `fdCoefficientTransportFactors`; `FdPullbackComparison`: `fdResidueInvertible`.
- `Sheaf.Paper.IntegralInverseImageComparisonComposition`:
  `integralInverseImageDerivedComposition`.
- `Sheaf.Paper.IntegralPullbackStrictRoosNormalization`:
  `IntegralPullbackStrictRoos.kappaType`, `inclusionType`, `IsUnitNormalized`,
  `cxT`, `towerCounit`, `R`, `towerComplexes`.

All stated proof-dependency modules that have published interfaces are imported
non-publicly unless their declarations occur in the signature. The node's
unstated proof-only prerequisites are not assumed as hypotheses or restated
as unowned `sorry`s; their required arguments are included in the main proof plan.
Four landed declaration owners and the new definition-only Roos data owner used
by the signature were added to `stmt_deps`.
A read-only traversal of their statement/proof dependency closures found no path
back to this item. There is one new definition node, described below, and no dependency module replacement.

Edge cases checked: the first positive quotient is `n=0` in the existing
indexing; no exponent-zero quotient is accidentally introduced. Zero complexes
and zero sections satisfy the same coordinate specifications. Empty schemes
are allowed by all binders. Identity isomorphisms are explicitly covered,
including `h` or `k` equal to identity. The ambient normalization quantifies over
incomplete as well as complete objects; only the latter have an invertibility
conclusion. No finite-dimensional field is replaced by its algebraic closure.
The scheme/site universes are not identified. No arbitrary K-injective
resolution or finite representative is singled out in the normalization.

Searches: `msearch.py` leanfinder query “The completed pullback compositor is
normalized by the completion unit and agrees with the framework Roos tower
pullback compositor” returned 8 categorical pullback-map hits, none this
statement. Loogle query “CategoryTheory.conjugateEquiv, CategoryTheory.NatTrans”
returned no hits. Mathlib grep query
`completed.*(compositor|normalization)|conjugateEquiv` in CategoryTheory returned
25 generic adjunction hits, including `Adjunction.Mates`, but no geometric
comparison. Repository `rg` searches for completed compositors/normalizations
and the exact node id in `lean/WeilConjectures` found no exact existing statement.
`rg` of `lean/Sheaf` located the component interfaces listed above. They do not
assert the normalized framework/PBC whole-cone comparison and both unsuppressed
coherence equations together. Exact wrapper search outputs are retained in the
sandbox's `searches.jsonl`.

Validation: final module compiled through the prescribed `scompile.py` in both
sandbox and library modes with no errors or warnings reported (latest run:
65.0 s wrapper-reported sandbox wall time including scheduling; 46.6 s library).
The Lean invocations retain the tool's 60-second limit. No local/global build,
shared-repository edit or direct git command was run.

## Second reading by Q93

The dispatcher expressly forbids starting other agents, so this is a separate
self-review pass, not a claim of independent worker review. The maintainer's
independent review remains required. I reopened the node and full module and
checked each hypothesis and clause against the mapping above. I added the
ordinary-compositor transport equation, which was initially only implicit in
the representative normalizations. I retained ambient augmentation as an
unrestricted statement and the actual complete-domain compositors in the final
equalities. I checked that the cone comparison fixes both coordinates, rho is
normalized on every injective-term K-injective resolution, the completed
adjunction is pinned by its actual Hom transpose, and coefficient transport is
the existing quotient-normalized restriction. No mathematical statement change
was made. There is one named theorem with `sorry`, and all helper definitions
have concrete bodies.


## New nodes

`def-sfb-integral-pullback-strict-roos-data` owns the existing definition-only
interface in `Sheaf.Paper.IntegralPullbackStrictRoosNormalization`, recorded with
`lean.existing: true`. It lists exactly `siteSmall`, `datum`, `R`,
`towerComplexes`, `kappaType`, `inclusionType`, `limitProduct`,
`IsUnitNormalized`, `pullR`, `redR`, `towerPullR`, `T`, `cxT`, and `towerCounit`
in namespace `WeilConjectures.IntegralPullbackStrictRoos`. The primary signature
is the unchanged `IsUnitNormalized` definition. Its source is the first
paragraph and Stacks comparison of blueprint `det-lem-int-tensor-pullback`.
The node defines the small-site convention, finite adic datum and completed ring,
the tower-complex and comparison/inclusion types, the projection/product map,
the two unit-normalization equations, actual module pullback and quotient tower,
their levelwise/degreewise composites, and the composite representative counit.
It asserts no existence theorem or invertibility theorem. All listed declarations
have concrete bodies; no data or property is selected from the normalization
theorem. Generic tower and Roos notions are cited through their existing
separate definition nodes.

The three wrapper searches were run again for this ownership repair: LeanSearch
query `Strict quotient pullback tower Roos cone ordinary limit inclusion unit
normalization` returned eight unrelated generic pullback-limit results; Loogle
query `CategoryTheory.roosF, CategoryTheory.completedRlim` returned zero hits
with the explicit note `unknown identifier 'CategoryTheory.roosF'`; Mathlib grep
query `IsUnitNormalized|IntegralPullbackStrictRoos|completedReductionModuleTowerFunctor`
returned zero hits. Direct `rg` in `lean/WeilConjectures` returned no matches;
`lean/Sheaf/Paper/IntegralPullbackStrictRoosNormalization.lean` supplies the exact
existing definitions. DAG grep found them listed only on the theorem node
`lem-sfb-integral-pullback-strict-roos-normalization`; blueprint search `strict Roos`
returned zero nodes. Thus the declarations exist, but a definition node owning
this interface was missing. Search outputs are retained in `searches.jsonl` and
in the new node's `mathlib_searches`.

## Return repair and self-check by Q93

The immutable-head return `75788871c907`, point H2, is repaired by replacing
`lem-sfb-integral-pullback-strict-roos-normalization` in the item's `stmt_deps`
with `def-sfb-integral-pullback-strict-roos-data`. The new node is an existing
binding, so no Lean file or definition is duplicated. The returned item's Lean
module remains byte-identical, as requested. Its mathematical statement, proof
plan and proof dependencies remain unchanged. The other flagged dependency,
`lem-trf-integral-inverse-image-comparison-composition`, remains cited: its map
is selected from the stated unique-existence theorem, as the return confirmed.

I read the listed definitions' complete signatures, docstrings and bodies,
including `IsUnitNormalized`, `limitProduct`, and both factors of `towerCounit`,
and matched every new-node clause to these declarations. The site universes
remain distinct, index zero is the first positive quotient, and the definitions
accept arbitrary complexes and scheme maps. The normalization predicate states
both cone-coordinate and universal-unit equations; it does not assume they hold.
The original theorem's edge-case checks and hypothesis/clause mapping above
therefore remain valid. This is an in-thread self-check under the dispatcher's
explicit prohibition on other agents; independent maintainer review is required.


Repair validation: the explicit `scompile.py` invocation passed in sandbox and
library modes (65.0 s and 46.6 s wrapper wall times, including scheduling). The
first repaired dry run compiled its two checks but required the new node's
`import_flags` key; it is now the empty list. The dry run's theorem-dependency
message for `lem-trf-integral-inverse-image-comparison-composition` is advisory:
the independent return explicitly passed that dependency because its map is
chosen from the matching unique-existence theorem. The suggested `sfb` node
prefix is retained from the return, in the item's required chapter directory.
The initial saved-packet dry run also passed before the requested ownership
repair. No compiler diagnostic required a Lean change.
