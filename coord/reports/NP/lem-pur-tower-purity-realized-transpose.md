## Worker report

The module `Sheaf.Paper.TowerPurityRealizedTranspose` states
`AlgebraicGeometry.ProEtale.RealizedTowerPurity.realized_tower_purity_transpose`.
Its only postponed proof is this theorem. The other 18 declarations construct its
canonical maps, exact restrictions, or normalization predicates from published data.
The node's mathematical statement, proof and proof dependencies are unchanged.
The repair adds thirteen statement-dependency edges recording definition ownership.

The source read is the current `literature/blueprint/latest/blueprint/sec-smooth-purity/`
`sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gamma.proof.md`, clauses (1)–(3),
together with the node's ten-step proof. The theorem docstring carries all ten steps,
including the order of cofinal restriction, the open-unit normalization, the same-b
projection square, and recovery of integral equality by simultaneous reduction.

Hypotheses and clauses are rendered as follows.

- The geometric and coefficient setting is `D : FiniteFieldDatum`,
  `C : D.CoefficientDatum`, `E : IntermediateField (Padic C.l) C.Qbar` with
  `FiniteDimensional (Padic C.l) E`. Thus the residue characteristic differs from
  `C.l`, and E lies in the fixed algebraic closure.
- X and Y carry their `Over (Spec (.of D.k))` structures, `IsSeparated`,
  `LocallyOfFiniteType` and `QuasiCompact` structure morphisms. The fixed
  compactification is written `j : X ⟶ Z`, `p : Z ⟶ Y`, with open/proper instances;
  `SpTowerGamma.factorization j p` is the corresponding compactification of f.
  Its composite is over k, quasi-compact and compactifiable. The latter two are
  source-implied property certificates required by the recorded tower interfaces,
  not restrictions on the geometry. `d : ℕ` and `SmoothOfRelativeDimension d (j ≫ p)`
  render smoothness of pure nonnegative relative dimension. No nonemptiness,
  positive dimension, connectedness, or unramified-coefficient assumption is added.
- Completed coefficients, finite ell quotients, and simultaneous reduction use
  `SpReductionTower`, `SpNormalizedEquivalence` and the actual coordinate equivalence
  `SpTowerCalculus.realization`. `b`, `o`, `q`, `w`, `hF`, `Gb`, `ab`, `lv` are the
  recorded strict-system operations and their finite normalized realizations.
  The theorem existentially supplies the integral realization `r`, just as the
  recorded integral-adjunction result does; it does not assume its purity conclusion.
- The domain is exactly `finiteTorConstructibleIntegralCategory`. Its existing
  predicate includes completeness, constructible reductions and a single common
  finite Tor interval. `hP` and `hH` are conclusions certifying restriction of the
  actual support and actual realized exceptional functors to this full category.
  The Noetherian structures used by `r.purity` come from `r.noetherianX/Y` in
  `letI`; they are not extra geometric hypotheses.
- `support` is a full-subcategory lift of the literal
  `CompleteCompactificationLimit.image`. `restrictedRight` restricts the literal
  `SpIntegralAdjunction.right`. `restrictedAdjunction` uses Mathlib's fully faithful
  adjunction restriction, so its unit/counit are inherited from `r.adjunction`.
  G is universally quantified with any specified `support ⊣ G`; it is not chosen
  or defined using the purity morphism.
- `realized` is the actual reconstruction unit followed by total limit of the
  source comparison and `SpTowerGamma.gamma`, with the coordinate equivalence's
  unit maps. `component` then composes with
  `(restrictedAdjunction ...).rightAdjointUniq adj`. This is precisely Gamma and
  the unique counit-preserving delta, before any finite evaluation.
- The first conclusion is `∀ K, IsIso (component ... K)`. The separate naturality
  equation uses `SpTwistedPullback.source.map` and `(G.map u).hom` for every arrow.
  Thus these are natural isomorphisms on the full common finite-Tor domain.
- `componentReduction` is simultaneous reduction of delta inverse followed by the
  actual reconstruction-counit comparison `r.rightComparison`. The whole-system
  equation is `reduction.map Gamma ≫ componentReduction =
  r.sourceComparison.hom.app K ≫ SpTowerGamma.gamma ...`. This is an equality in
  the derived category of entire strict coefficient systems, with every transition
  retained. `r.purity.finite_levels` is the recorded comparison with the exact
  `PurityFiniteSetting.smoothPurityMap`, not just an endpoint isomorphism.
- The uniformizer assertion is also explicit: for every n, reduction of
  `s.hom ≫ Gamma ≫ e.hom`, followed by `purAdicTargetReduction`, is exactly
  `purAdicSourceReduction ≫ (purAdicFiniteArrow ... n).hom`. Index n means exponent
  n+1, so all positive uniformizer exponents occur, including levels outside the
  ramification-index subsequence.
- Neither s nor e is arbitrary. `SourceNormalized` fixes s on every K-flat
  representative by exact sheaf twist, the site tensor isomorphism, the total-single
  collapse and the published integral tensor model. `FiniteNormalized` fixes every
  finite right comparison by the ordinary étale Hom transpose, through the actual
  proper/open and derived site comparison maps. `finiteReduction` is then the
  canonical coefficient mate with those finite comparisons. The equation for e's
  finite reductions uses this map after the inverse unique-adjoint comparison for
  `specifiedAdjunction`. Its left comparison `specifiedLeft` is exactly `S.left`,
  lifted through the full inclusion. These normalization equations are independent
  of Gamma and finite purity. The canonical `purAdicTargetReduction` is the actual
  reduction/limit counit followed by its specified evaluation comparison.
- `line` is the shifted degree-zero integral Tate line T. `sourceUnit` uses the
  normalized completed pullback unit and the tensor unitor to identify the source
  at `1_Y` with T. Hence a is literally `sourceUnit.inv ≫ component ... 1_Y` and
  omega is `(G.obj 1_Y).obj`; both formulas use that same component and specified
  adjunction. `core.admissibleY.1` supplies membership of the actual coefficient
  unit, so the finite-reduction assertion applies at the unit as well.
- `reassociation` is sigma: ordinary tensor's closed-structure identification,
  the actual tensor completion augmentation and the inverse signed second-slot
  shift comparison. Its `IsIso` is a conclusion. `muX/Y` are fixed by the existing
  `PurUnitTrace.IsUnitNormalized` representative equations, not arbitrary unit
  identifications.
- `inverseProjection` is the inverse of
  `CompactificationBProjection.alpha`. Its two identifications are precisely the
  actual `sourceUnit` and `innerUnit` completion augmentations. Their invertibility
  and that of the right-unit augmentation are conclusions. The projection's
  invertibility itself, `hpT/hpW`, is assumed exactly on the two displayed inputs,
  as the node requests. `alpha` uses the proper/open projection and its two
  specified tensor symmetries.
- The final two equations are the displayed counit identities, written in Lean's
  left-to-right composition order: P(Gamma) then epsilon equals P(sigma), then
  P(id tensor a), then inverse projection at omega, then id tensor epsilon_unit,
  then the actual completed right unitor; and equals P(sigma), inverse projection
  at T, id tensor (P(a) then epsilon_unit), then that same right unitor. These are
  integral morphism equalities. They are not predicates about separate evaluations.

Dependency declarations used (the declared module interfaces and full signatures
were read, including the `mathlib_match` for the adjunction-uniqueness node):

| Node or role | Module and declarations |
| --- | --- |
| coefficient conventions | `Sheaf.Paper.PurityFiniteSetting`: `FiniteFieldDatum`, `CoefficientDatum`, `PurityFiniteSetting` |
| geometric properties | Mathlib `Scheme`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, `IsOpenImmersion`, `IsProper`; `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `SmoothOfRelativeDimension` |
| completed coefficients | `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: actual completed ring, projections and constant-to-completion cone |
| ell towers | `Sheaf.Paper.SmoothPurityCoefficientTowers`: `spCoefficientRings`, `sp_completed_coefficient_limit` |
| complete constructibility | `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`, `sfIntegralConstructibleCategory` |
| common finite Tor | `Sheaf.Paper.FiniteTorAmplitude` / exported sites interface: `finiteTorConstructibleIntegral`, `finiteTorConstructibleIntegralCategory` |
| completed operations | `Sheaf.Paper.IntegralDerivedOperationsOnSlices` and its exported calculus: `integralDerivedPullback`, `integralCompletedTensor`, `calculus` |
| twists | `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: `integralTwistLine`, `integralComplexTwist`, exact integral twist |
| compactification | `WeilConjectures.Compactification.RefinementCategory`: `Compactification` and refinement interface |
| actual support | `Sheaf.Paper.QcqsCompactSupportRealization`: `sfQcqsCompactSupportRealization`; actual `CompleteCompactificationLimit.image` and `CompleteProjectionDescent.integralImage` |
| specified exceptional adjunction | `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: `RingSystem`, `Operation`, `Scalar`, `Comparison`; `RingSystem.left` and normalized coefficient mates |
| realized adjunction | `Sheaf.Paper.IntegralAdjunctionBijection`: `SpIntegralAdjunction.Realization`, `right`, `reduce`, `limit`, `support`; its actual comparisons, unit/counit and purity fields |
| unique right comparison | `Mathlib.CategoryTheory.Adjunction.Unique`: `Adjunction.rightAdjointUniq`, with `rightAdjointUniq_hom_app_counit` |
| projection | `Sheaf.Paper.ExchangeProjectionSuppliedDomains`: supplied-domain mate construction; `Sheaf.Paper.CompactificationBProjectionReduction`: `alpha`, `sourceUnit`, `innerUnit`, actual signed symmetry |
| whole-system realization | `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`: `RingedModels`, `calculus`, canonical operation comparisons |
| diagonal tower purity | `Sheaf.Paper.SmoothPurityTowerGamma`: `factorization`, `Purity`, `FiniteLevels`, `gamma` |
| finite purity | `Sheaf.Paper.SmoothPurityMap`: `PurityFiniteSetting.smoothPurityMap`; existing adic `purAdicFiniteArrow`, `purAdicSourceReduction`, `purAdicTargetReduction` from the exported adic interfaces |
| normalized tensor/unit coordinates | `Sheaf.Paper.AdicUnitTraceTensorCoordinates`: `unitComplex`, `IsUnitNormalized`, chain/site tensor conventions |
| fixed finite left presentation | `Sheaf.Paper.ConstructibleExceptionalCompositorData`: `constructibleFiniteImageIso` |
| full restriction | Mathlib `Adjunction.restrictFullyFaithful`, `ObjectProperty.fullyFaithfulιOfLE` |

The proof-dependency modules are also imported: completed-operation tower
substitution, open tensor normalization, cofinal quotient projection cocone,
cofinal finite-reduction constructibility, integral reconstruction comparisons,
strict arithmetic restriction comparison, twisted pullback reduction, and reduction
compatibilities. The completed-projection module is public because its specified maps occur in
the statement. Those definitions are now owned by the new
`def-pur-completed-projection-coordinates`; the projection theorem remains only
a proof dependency. The plain proof-dependency imports are retained to express
the stage-3 proof plan, as required by stages/2-statements.md, section 3 rule 7;
this addresses the advisory H9 rather than treating planned proof imports as
statement definitions.

Edge cases checked before and after writing: d=0; identity f and identity quotient
arrows; zero K; empty X or Y; ramification index greater than one and uniformizer
levels not divisible by that index; arbitrary bounded finite-Tor intervals; and
changing the specified right adjoint while preserving its counit. No finite-level
faithfulness is assumed for derived tower arrows. The integral equation is stated
in the ambient derived category and its proof uses full faithfulness of simultaneous
reduction. There is no STATEMENT-DISPUTED flag or source-based statement correction.

Searches: prescribed `msearch.py leanfinder` query "realization of tower smooth purity
isomorphism with projection counit adjunct in integral derived category" returned
8 unrelated Mathlib hits (GammaSpec counit, derived adjunction counits, restriction
counits); none states this result. `msearch.py loogle` query
"Adjunction.rightAdjointUniq, Adjunction.homEquiv" returned zero hits with an unknown
identifier diagnostic; direct source search located Mathlib's exact declarations.
`msearch.py grep` query `rightAdjointUniq_hom_app_counit`, subdirectory
`CategoryTheory`, returned the declaration in `Adjunction/Unique.lean:127` and one
use in locally cartesian closed categories. `rg` of both `lean/WeilConjectures` and
`lean/Sheaf` for the item name, `RealizedTowerPurity`, and the realized integral
projection-counit formulation found no existing theorem; the prescribed item-id
`grep -rn` in `lean/WeilConjectures` also found none. The project search found the
recorded tower gamma, adjunction, compactification projection and adic reduction
interfaces used here. No duplicate operation or coefficient category is introduced.

Validation: all compiler invocations used the prescribed `scompile.py`. The full
statement and all 18 helper definitions compiled in both sandbox and library module
mode, without errors or warnings after line wrapping (48.3 s / 30.3 s in the clean
run). No local build or direct Git command was run in the shared repository.

## Repair of returned immutable head 216a51084463

H2: added `def-pur-completed-projection-coordinates`, an existing:true re-export
of nine published definitions in `Sheaf.Paper.CompactificationBProjectionReduction`.
The item cites this definition owner, while the theorem
`lem-pur-compactification-b-projection-reduction` remains in proof_deps. There is
no new Lean construction and no arbitrary projection map. The main theorem
signature was compared byte-for-byte with the returned lean.statement and is
unchanged, including every hvT/hhT/hvW/hhW/hu and hpT/hpW binder.

The twelve additional requested existing owners are now explicit stmt_deps:

| Definition owner | Published module and statement use |
| --- | --- |
| `def-pur-compactification-reduction-models` | `Sheaf.Paper.CompleteProjectionMateDescent`, re-exporting `CompleteProjectionDescent.DescentModels` and `integralImage` from `CompleteProjectionDescentMaps`: m and the literal proper/open P |
| `def-pur-completed-unit-pullback-data` | `Sheaf.Paper.CompletedUnitPullbackData`: `CompletedUnitPullback.Core`, the pinned pullback-unit map and actual unit membership |
| `def-pur-adic-purity-objects` | `Sheaf.Paper.AdicPurityObjects`: `purAdicSource`, `purAdicTarget`, `purAdicFiniteArrow`, at exponent n+1 |
| `def-pur-adic-exceptional-reduction` | `Sheaf.Paper.AdicPurityExceptionalReduction`: `purAdicTargetReduction`, counit followed by normalized evaluation |
| `def-pur-adic-source-reduction` | `Sheaf.Paper.AdicPuritySourceReduction`: `purAdicSourceReduction`, exact shift, twist/restriction, pullback counit and finite source identification |
| `def-pur-unit-trace-tensor-coordinates` | `Sheaf.Paper.AdicUnitTraceTensorCoordinates`: `PurUnitTrace.unitComplex`, `IsUnitNormalized`, which pin muX and muY on every K-flat representative |
| `def-sp-twisted-pullback-reduction-data` | `Sheaf.Paper.TwistedPullbackReductionData`: `SpTwistedPullback.source`, ordinary signed Tate tensor after completed pullback, then shift |
| `def-sf-integral-system-canonical-bridge` | `Sheaf.SixFunctors.IntegralSystemCanonicalBridge`: `RingedModels`, ordinary tensor/pullback and their representative comparisons in m.integral |
| `def-pur-integral-operation-shift-data` | `Sheaf.SixFunctors.IntegralOperationShiftData`: `tensorShifts`, the normalized signed second-slot comparison in sigma |
| `def-sf-finite-exceptional-compositor-maps` | `Sheaf.Paper.ConstructibleExceptionalCompositorData`: normalized finite support comparisons used in `finiteLeft` and finite Hom normalization |
| `def-sf-finite-tor-integral-inclusion` | `Sheaf.Paper.IntegralCompactSupportCoefficientComparison`: `PurCompactSupport.finiteTorIntegralInclusion`, forgetting only the finite-Tor certificate |
| `def-weil-integral-derived-reduction` | `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`: `scalarReductionDerivedExtension`, actual positive derived quotient functor |

Their existing module interfaces are public imports, directly when not already
present. The live node's mathematical fields were compared with the sandbox:
statement, proof and proof_deps match; stmt_deps only gain the required owners.
No dependency node is overwritten. The delivery wrapper performs rebasing and
comparison against current main in its isolated worktree.

## New nodes

`def-pur-completed-projection-coordinates` records coefficient-first ordinary and
completed inner/source objects, their actual tensor and pullback augmentation
maps, the signed ordinary projection and its transport across supplied source
and inner isomorphisms. It owns exactly `integralSymmetry`, `ordinaryInner`,
`ordinarySource`, `completedInner`, `completedSource`, `innerUnit`, `sourceUnit`,
`ordinaryAlpha`, and `alpha` in the existing module
`Sheaf.Paper.CompactificationBProjectionReduction`. It asserts no invertibility.
Its source is current blueprint integral-adjunction-direct-image proof (3) and
tower-geometric-gamma proof (2). The node retains alpha's general v,h interface;
canonical v,h are asIso of the two actual augmentation maps when invertible.
The item uses only those canonical choices. Thus it is the accepted be8a style
existing:true ownership fix, with no parallel definition or theorem owner.

The three prescribed searches used the same plain query, “Completed
compactification projection with ordinary signed tensor symmetry and canonical
tensor and pullback completion units.” LeanSearch returned eight topological
completion/pullback results, none about this construction. LeanFinder returned
`AdicCompletion.ofTensorProduct` and its functoriality lemmas, ordinary graded
commutativity and Pi tensor results; none provides these maps. Mathlib grep for
`ordinaryAlpha|CompactificationBProjection|completedInner` in CategoryTheory had
zero hits. The same rg in WeilConjectures had no hits; Sheaf located the nine
published definitions above. DAG ownership grep found only the theorem node,
not a definition owner, and blueprint_refs.py search completed-projection found
zero blueprint nodes. The related existing
`def-pur-compact-support-completed-projection-data` was opened: its model is
image-first ordinary tensor and completion of ordinary pullback, whereas the
present definitions use coefficient-first tensor and separately completed
pullback with its augmentation. It does not record these declarations. Searches
and outcomes are also stored in the new node's mathlib_searches. The new node's
blueprint ancestor is prop-weil-operations, obtained from blueprint_refs.py
ancestor, and its via prepends this item to the item's existing via.

## Second reading by NP

Reopened the DAG statement and the delivered Lean file together, including the
new definition node and the full source of each newly cited interface. This
reading checks the following clauses rather than relying on the earlier audit.
The dispatched constraint against starting agents is respected; no independent
person is claimed here. The maintainer's independent immutable-head review has
already checked the mathematics, and this reading checks the actual repair.

1. Setting: the node's algebraic closure of the finite field, ell distinct from
   p, fixed coefficient algebraic closure and finite extension are exactly D,
   C, E and FiniteDimensional in `realized_tower_purity_transpose`. The Over,
   separated, locally-finite-type and quasi-compact structure morphism instances
   encode separated finite-type X,Y. j,p give the fixed open/proper
   compactification and f is their composite; SmoothOfRelativeDimension d is
   required for that same composite with d natural. No new hypothesis was added.
2. Categories and coefficients: `finiteTorConstructibleIntegralCategory` retains
   completeness, constructible reductions and one common finite-Tor interval.
   RX/NX and RY/NY are the actual simultaneous reduction/reconstruction
   presentations. b,o,q,w and hF,Gb,ab,lv are the specified tower operations,
   twist and adjunction/finite-level data, not unrelated replacement categories.
3. Realization and arbitrary specified adjunction: the existential r is the
   realized tower adjunction H; hP and hH certify its actual common finite-Tor
   restrictions. G and adj remain universally quantified after these witnesses.
   `restrictedAdjunction` is the fully faithful restriction and `component`
   composes `realized` with its `rightAdjointUniq adj`. This is exactly delta
   after Rlim gamma, with the unique counit-preserving comparison, not a new
   purity-defined right adjoint. Noetherian witnesses are taken from r, not
   supplied as extra premises.
4. Naturality and invertibility: the first conjunct is IsIso of component for
   every K. The explicit naturality conjunct compares the source functor's map
   of u followed by Gamma at K' with Gamma at K followed by G.map u. Both sides
   use the same component and the full finite-Tor inclusion; no naturality of
   unrelated endpoint maps is substituted.
5. Whole towers: `componentReduction` is simultaneous reduction of the inverse
   right-adjoint comparison followed by r.rightComparison. The displayed
   equality reduces Gamma and then applies this map, yielding
   r.sourceComparison followed by the literal SpTowerGamma.gamma. Its equality
   is in the derived category of entire systems, retaining all transitions.
6. All positive uniformizer levels: e and s are existentially supplied but
   pinned. `SourceNormalized` fixes s by every K-flat representative, exact
   sheaf twist, total-single tensor and the recorded tensor model.
   `FiniteNormalization.hom_normalized` fixes the finite right comparisons by
   ordinary etale Hom transpose. The e equation uses the inverse unique-right
   comparison for specifiedAdjunction and the canonical scalar mate
   finiteReduction. The final finite equation is red(s.hom then Gamma then
   e.hom) then purAdicTargetReduction equals purAdicSourceReduction then the
   actual purAdicFiniteArrow. All n are natural and mean exponent n+1; this
   covers levels outside the ell-power cofinal subsequence as the node asks.
7. Unit and a: `line` is the shifted single Tate line T. `sourceUnit.inv` then
   Gamma at the actual integralConstantCoefficientObject is the node's a.
   `core.admissibleY.1` certifies that actual unit's membership. omega is exactly
   its G image. muX and muY are constrained by IsUnitNormalized on all K-flat
   representatives; they cannot be arbitrary unit identifications.
8. Sigma: `reassociation` is the ordinary closed tensor comparison followed by
   tensor completion and inverse signed second-slot shift. Its IsIso is a
   conclusion under the existential completion witnesses, not an assumption
   inserted to make the theorem easier.
9. Projection coordinates and quantifiers: hvT,hhT,hvW,hhW and hu are
   existential conclusions certifying the actual source/inner tensor and
   right-unit augmentations. hpT and hpW remain universally quantified IsIso
   assumptions on alpha at (K,T) and (K,omega), exactly the node's stipulated
   projection invertibility. `inverseProjection` takes inv of this alpha, so
   its direction is P(completed inner) to completed source. The new definition
   node records the same alpha, sourceUnit and innerUnit with ordinaryAlpha
   and integralSymmetry; its signature was copied verbatim from published
   source. It introduces no extra existence or invertibility assertion.
10. First counit equality: read the actual Lean composite in application order.
    It is P(Gamma_K), epsilon_K on the left, and P(sigma_K), P(id tensor a),
    inverse projection at omega, id tensor epsilon_unit, actual completed
    right unitor on the right. This matches the first displayed equation and
    uses the same G, adj and a as above.
11. Second counit equality: the left side is the same. The right is P(sigma_K),
    inverse projection at T, id tensor (P(a) then epsilon_unit), then the same
    right unitor. Thus it is exactly the second displayed equation, in the
    right order, as an integral morphism equality before finite evaluations.
12. Ownership comparison: the nine new-node names were checked against their
    published definitions. ordinaryAlpha is the two signed swaps around the
    actual proper/open projection, innerUnit is chi then tensor of the actual
    pullback unit, sourceUnit is chi, and alpha is v.inv then ordinaryAlpha then
    P(h.hom). The twelve requested owner nodes were read and cited by their
    current recorded modules. No definition has been replaced or duplicated.

Findings and changes: H2 was a missing definition-ownership boundary, repaired
by the new existing:true node and the twelve existing owner edges/public
imports; the theorem signature and all helper bodies remain unchanged. H11 was
the non-reading disclaimer, replaced by the explicit twelve-point comparison
above. Advisory H9 is answered by the documented stage-3 proof-import rule.
The edge cases d=0, zero objects, empty schemes, arbitrary common finite-Tor
intervals, ramified E, n=0 meaning exponent one, identity quotient maps and
arbitrary counit-preserving specified G remain included. No mathematical
mismatch, false clause or statement correction was found in this reading.

## Earlier repair validation and upstream compiler failure

On 2026-10-25, the repaired module was sent to the prescribed scompile.py.
It stopped before compiling the delivered file, in the server's current published
source closure, with unknown identifier `completionMap_isIso` in
`Sheaf.SixFunctors.TensorAdjunctionReductionSquares` at lines 1128, 1227,
1320, 1571 (and consequent unsolved goals). The server source was read with
scompile.py --source and the import ordering was checked: that declaration is
in `Sheaf.SixFunctors.GeneratorReductionStatement`, which itself imports
TensorAdjunctionReductionSquares. The essential direct dependency
IntegralCompactificationSystemRealization imports IntegralExpressionCoefficientSquares,
which imports GeneratorReductionStatement. IntegralAdjunctionBijection and the
completed-projection definition owner also reach this path. Thus the failure
is not caused by the added public owner imports and cannot be removed by the
advisory plain-import cleanup. No shared source or launcher file was edited.

The prescribed `deliver2.py NP lem-pur-tower-purity-realized-transpose --no-push`
was also run. It returned `COMPILE FAILED on the server, nothing pushed` with
the identical upstream errors in snapshot
`d5eaf512fec2ec9adba5ad302055e887943f034609006b0f5d542c452da4fe18`.
It did not reach the item's own compiler or report an OK preflight. No delivery
push was attempted after that failed dry run. This failure supersedes the
historical successful-compile paragraph above: that paragraph describes the
returned head, not the current repaired module. The repaired node, module and
clause reading are retained in this sandbox for compilation after the upstream
import ordering is repaired. Editing unrelated published proof modules or
patching the compiler wrapper is outside this delivery's authorized repair.

## Resumed repair validation

The sandbox was compared again with current main: the mathematical statement,
proof and proof_deps still match, with exactly the thirteen intended extra
stmt_deps. The theorem signature and the new definition owner's alpha signature
both match their recorded source verbatim; the Lean file has one theorem sorry
and no line over 100 characters. The previously failing upstream import order
has now been changed: TensorAdjunctionReductionSquares publicly imports
GeneratorReductionStatement, and GeneratorReductionStatement no longer imports
TensorAdjunctionReductionSquares. The fresh prescribed server compile passed against that updated published
source closure: sandbox mode 47.5 seconds, library mode 35.3 seconds, no errors
or warnings. The prior failure above is
historical, not a reason to stop this retry.
