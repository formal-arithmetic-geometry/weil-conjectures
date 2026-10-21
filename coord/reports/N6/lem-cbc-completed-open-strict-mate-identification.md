## Worker report

The module `Sheaf.Paper.CompletedOpenStrictMateIdentification` states the actual
completed-ring strict open exchange's compatibility with the constant-A strict
open unit-mate. It also states the ordered completed inverse-limit formula,
the specified finite evaluation, and naturality of the actual exchange and the
four strict/completed endpoint comparisons. Both theorems have `sorry` proofs.
Every definition has actual data: a functor composite or a composite of already
specified canonical isomorphisms. There are no new mathematical hypotheses,
arbitrary endpoint choices, or evaluations used to define the strict exchange.
The item statement and all its existing fields except `lean` are unchanged.

Clause-by-clause reading:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Noetherian adic (A,I), torsion residue, finite perfect positive quotients | `A : Type (u + 1)`, `[CommRing A]`, `d : AdicCoefficientDatum A`; its inherited `ideal`, `noetherian`, `finitelyGenerated`, `quotientTorsion`, `quotientPerfect` and `quotientFinite` fields |
| Completed ring sheaves A_V, strict reduction towers | `d.completedRing`, `completedReductionTower V d`; actual inverse limits of the function coefficient sheaves, with index n denoting exponent n+1 |
| Cartesian open square (j,j',u,v) | `sq : OpenImmersionSquare v j' j g`; the node's bottom arrow u is named `g` to leave `u` for the universe |
| Both vertical arrows are open immersions | `[IsOpenImmersion j]`, `[IsOpenImmersion j']`; precisely the two properties already supplied by `sq.isOpenImmersion` and `sq.isOpenImmersion'`, not restrictions on g or v |
| j quasi-compact | `[QuasiCompact j]`; `cbcOpenMateQC sq` derives quasi-compactness of j' from the square |
| Exact localized ringed extension by zero | Existing `cbcDerivedOpenShriek` and `cbcStrictOpen`, using the direct-sum presheaf, module sheafification and exact localized adjunction; no replacement extension is introduced |
| K intrinsically complete | `K : (cbcCompleteProperty d U r a ha).FullSubcategory`; r,a,ha specify any finite tuple generating the datum's ideal |
| j!K complete | `_completeOpen : cbcCompleteProperty d T r a ha ((cbcDerivedOpenShriek d j inferInstance).obj K.obj)` |
| Canonical identification of reduction of j!K with J_j K_bullet | Existing `cbcRealizationReduction d j K.obj`, the inverse of the reduced open-unit transpose, used in `cbcOpenMateOmega` |
| r_V is restriction from completed to constant A coefficients | Existing `cbcRealizationRes d V` and `exchangeTowerRes d V`; both restrict along the datum's canonical constant-section map `exchangeScalar d V` |
| M = r_U K_bullet | `cbcOpenMateM d` is the composite of reduction and `exchangeTowerRes` |
| N = G_g J_j M, N' = J_j' G_v M | `cbcOpenMateN d` and `cbcOpenMateN' d`, using the recorded `ProEtale.StrictTower.G` and `.J` |
| Actual strict-tower objects Q and Q' | `cbcOpenMateSource d` and `cbcOpenMateTarget d`; Q reduces j!K first, while Q' applies actual derived strict pullback then strict extension |
| Actual strict isomorphism omega, induced simultaneously before evaluation | `cbcOpenMateOmega d sq`; apply actual `completedTowerPullback g d` to the quotient/open isomorphism, then use existing `cbcReductionStrictExchange d sq` |
| Inverse finite exchanges are the pulled-back open-unit transposes, compatible with strict transitions | The actual exchange is exactly `cbcStrictExchange` under reduction, whose `CbcStrictExchangeNormalization` and finite scalar normalization are supplied by the recorded `completedRingStrictFiniteExchange`; this construction retains those maps rather than choosing a new isomorphism |
| Canonical finite/scalar comparisons a and b | `cbcOpenMateA` and `cbcOpenMateB`, composing `cbcDatumTowerTransport`, `exchangeResPull`, and the existing quotient/open and tower scalar/open comparisons in their prescribed order |
| b r(omega) = beta a, before evaluation | First conjunct of `completedOpenStrictMateIdentification`: in Lean composition order, `r.map omega.hom ≫ b.hom = a.hom ≫ beta.hom` |
| beta is the actual constant-A strict open unit-mate | `cbcOpenMateBeta d sq K.obj` is `ProEtale.StrictTower.beta` evaluated at the specified M, with the square's chosen pullback and commutativity |
| Canonical completed comparison beta_comp | Existing `cbcDatumCompletedExchange d sq r a ha`, the recorded dependency's transport to `d.completedPull`, including its ordinary/completed unit normalization |
| L_V and the specified normalized lambda_j' | Existing `completedRlim` for constant coefficients and `cbcRealizationOpenLimit d j'`; this is the constant-diagram mate normalized on strict augmentations and resolutions, not a freely chosen comparison |
| Canonical completed endpoint identifications including completion units | `cbcOpenMateCompletedA` and `cbcOpenMateCompletedB`, using the existing `cbcRealizationPullLimit`, quotient/open comparison and derived scalar/open comparison |
| Ordered identity r(beta_comp) = lambda^-1 L(beta) in those endpoints | Second conjunct: `r.map beta_comp ≫ completedB.hom = completedA.hom ≫ L.map beta.hom ≫ lambda.inv.app ...`; postcompose by the inverse source endpoint to read the node's formula |
| Evaluation gives each specified finite open exchange | Last conjunct, `∀ n : ℕ, HEq ...`; it uses the dependency's exact `cbcSourceFiniteComparison`, `cbcTargetFiniteComparison`, `cbcFiniteExchange`, and `cbcFiniteReduction`, and explicitly includes the source quotient/open transport |
| All assertions natural in K | `completedOpenStrictMateIdentification_naturality` gives the five naturality squares for omega, a,b and the completed endpoints. The constant mate and completed comparison are already components of natural transformations; functorial Rlim then makes both equations natural |
| No etale origins, degree bound, or evaluation faithfulness | No such parameter, typeclass or condition occurs; all complexes and strict derived categories are unbounded |

The intrinsic completeness predicate is reused through the dependency's published
coefficient transport: `IntrinsicCompletion.intrinsicPresentationDatum` and
`intrinsicPresentationModules` transport to the recorded
`IsCompletedIntrinsicallyDerivedComplete`, and `IsDerivedCompleteIntrinsic`
is invertibility of that same transported Koszul unit. `cbcCompleteProperty`
uses the standard representative and its canonical realization. Thus it is the
recorded notion over the completed ring, rather than constant coefficients.

Dependency declarations read and used, or retained as proof imports:

- `Sheaf.Paper.AdicCoefficientDatum`: `AdicCoefficientDatum`,
  `completedReductionTower`, `completedReductionCoefficient`.
- `Sheaf.AlgebraicGeometry.OpenImmersionSquare`: `OpenImmersionSquare`.
- Mathlib `AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `LocallyOfFiniteType`, `QuasiCompact`, and stability under base change.
  Only quasi-compactness is assumed here, exactly as the node says.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`:
  `SheafOfModules.localizedSystemExact`, `localizedSystemAdjunction`.
- `Sheaf.Paper.IntrinsicCompletionCompleted`:
  `IsCompletedIntrinsicallyDerivedComplete`; the existing
  `Sheaf.Paper.IntrinsicCompletion` coefficient transport is used by
  `cbcCompleteProperty`.
- `Sheaf.Paper.ConstantCompletionEquivalence`:
  `CategoryTheory.ConstantCompletion.equivalence`, `finiteComparison`,
  `reductionTowerComparison`, `derivedLimitRestriction`, and the completion-unit
  comparisons. The actual site has objects in u+1 and morphisms in u; no equality
  of those universes is imposed.
- `Sheaf.AlgebraicGeometry.StrictConstantTowerOperations` and
  `.StrictTowerOpenExtension`: `ProEtale.StrictTower.G`, `.J`, `.jAdj`.
- `Sheaf.Paper.PbcQbarCompletedPullback` publicly retains
  `PbcActualStrictPullback`, `CompletedTowerPullback`, and `CompletedPullback`:
  `completedTowerPullback`, `AdicCoefficientDatum.completedPull`.
  Its specialized Qbar functor is not substituted for the integral functors.
- `Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars`:
  `ProEtale.StrictTower.FiniteOpenScalars.exchange_restrictScalars`.
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus` and its arrows module:
  `ProEtale.StrictTower.beta`, whose inverse is `betaInvApp`, and the
  recorded `normalizedProperOpenCalculus`.
- `Sheaf.Paper.CompletedOpenExchangeTransport`:
  `cbcDatumTowerTransport`, `cbcDatumCompletedExchange`,
  `completedOpenExchangeComparison`; its retained actual extension declarations
  come from `CompletedExtensionZeroComparison`.
- `Sheaf.Paper.ExactProductFunctorStrictLimit`:
  `CategoryTheory.exactProductFunctorStrictLimit`.
- `Sheaf.Paper.CompletedRingStrictFiniteExchange`:
  `cbcReductionStrictExchange`, `completedRingStrictFiniteExchange`,
  `cbcSourceFiniteComparison`, `cbcTargetFiniteComparison`, `cbcFiniteExchange`.
- Existing endpoint definitions in
  `Sheaf.Paper.CompleteProetaleStrictTowerRealization`:
  `cbcRealizationReduction`, `cbcRealizationQuotientOpen`,
  `cbcRealizationTowerScalarOpen`, `cbcRealizationDerivedScalarOpen`,
  `cbcRealizationRes`, `cbcRealizationPullLimit`, `cbcRealizationOpenLimit`.
  Their supporting `exchangeResPull` and `exchangeTowerRes` come from
  `Sheaf.Paper.StrictTowerExchangeMateNormalization`. These are the existing
  canonical constructions; none is redefined privately.

Import-cycle note for the maintainer: the realization module already owns these
endpoint definitions. This delivery imports it only to reuse them and never
invokes its `completeProetaleStrictTowerRealization` theorem. Its reverse proof
import of this item must be omitted under stages/2-statements.md section 3.7,
since it would close an import cycle. There is no reverse logical use of that
realization theorem in this statement or its proof plan. The unavailable
`lem-cbc-ringed-open-scalar-limit-coherence` remains an unimported proof node;
its equation is used only in the natural-language plan, not assumed as an input.
No source file in the shared library was modified.

Edge cases checked before writing:

- Empty open and empty schemes: none of the constructors or theorem binders
  requires a point or nonemptiness; the actual zero extension and its adjunction
  remain the selected ones.
- Identity and isomorphism squares: `sq.w` and the chosen pullback feed the
  existing normalized strict mate, not a separately chosen exchange.
- n=0 represents positive exponent 1. No level zero quotient is introduced.
- The empty generator tuple (r=0), the zero ideal, unit ideal and zero ring are
  admitted whenever the datum's actual hypotheses hold. No domain, nontrivial
  ring, prime, or positive-length generator assumption was added.
- Unbounded K and unrestricted g,v are allowed. No quasi-compactness of either
  ambient scheme or constructibility/etale origin is required.
- The finite evaluation formula is a consequence of the already fixed strict
  exchange; evaluation is not used to lift a map or detect equality.

Searches made:

1. `msearch.py ... leanfinder` query: "Completed open exchange equals the strict
   constant coefficient open unit mate before evaluation and derived inverse
   limit". Result: 8 hits about ordinary adic completion evaluations and quotient
   factors, none about module sheaf strict-tower mates.
2. `msearch.py ... loogle` query:
   `CategoryTheory.mateEquiv, CategoryTheory.Functor.map_comp`.
   Result: OK, 0 hits for the combined query. Existing mate API was read directly
   in the dependency source.
3. `msearch.py ... leansearch` query: "Canonical scalar restriction open extension
   inverse limit endpoint comparisons of completed pullback". Result: 8 hits
   about scalar restriction in topological algebra and multilinear maps, none
   supplying this exchange theorem.
4. `msearch.py ... grep` query `completed.*[Oo]pen|[Ss]trict.*[Mm]ate`,
   Mathlib `CategoryTheory`. Result: OK, 0 hits.
5. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
   `cbcStrictExchange|completedOpenExchange|CbcStrictExchange|cbcReductionStrictExchange`
   and the item's blueprint id. Result: no upstream match for the item;
   existing actual exchange was located and reused. The fresh shared checkout
   supplied `CompletedStrictOpenExchange`, `CompletedFiniteExchangeCoordinates`,
   `CompletedRingStrictFiniteExchange` and `CompletedOpenExchangeTransport`.
6. `blueprint_refs.py search 'strict mate endpoint'`: 0 blueprint nodes.
   Searching DAG records for `cbcRealizationPullLimit|cbcRealizationOpenLimit`
   located the already published realization helper definitions, which are reused.
   No extra definition node or dependency replacement was necessary.
7. The initial `scompile.py --source` requests for the two exchange modules
   reported them unavailable; subsequent checkout refresh made both existing
   modules available. Server source requests for `PbcQbarCompletedPullback`,
   `PbcActualStrictPullback`, `LocalizedModuleExactForSystems`,
   `CompletedExtensionZeroComparison`, and `CompletedPullback` succeeded.

Validation: the delivered module passed `scompile.py` against the published
server library, including private compilation of the freshly landed strict
exchange dependencies. After adding the naturality clauses and normalizing all
blueprint markers, it again compiled both as sandbox and as its actual library
module in about 7.4 seconds each, with no errors or warnings. Every variable and
universe is explicitly bound, `autoImplicit` is false, and all lines are within
100 characters. Both theorem proofs are exactly `sorry`.

Delivery dry run: `deliver2.py N6 lem-cbc-completed-open-strict-mate-identification --no-push`
printed OK: the commit passed the server preflight and per-file compilation.

## Second reading by N6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
