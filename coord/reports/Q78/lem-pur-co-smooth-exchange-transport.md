## Worker report

The item is stated by `AlgebraicGeometry.ProEtale.compactSupport_exchange_transport`
in `Sheaf.Paper.CompactSupportExchangeTransport`. Its proof is `sorry`; no theorem is
proved in this delivery. Four definitions expose the canonical comparison and its
source/target paths and the explicitly witness-transported map. Their data are actual
composites of published functors, natural isomorphisms and morphisms. No new mathematical
notion, arbitrary comparison, arbitrary exchange, or choice from existence is introduced.
The original statement and proof are unchanged. The statement dependency list gains the
already landed `lem-sf-class-compact-support-comparison`, so that its normalized comparison
is reused rather than constructed a second time.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
|---|---|
| Finite commutative ring Lambda | `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`. The constant fixed-scalar presentation needs no choice of topology; it represents the discrete coefficient sheaf. |
| Schemes T, U, U', T' | `{X' X Y' Y : Scheme.{u}}`, with X=T and Y=U. |
| u separated of finite type | `f : X ⟶ Y` with `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`. |
| Arbitrary v and its Cartesian base change | `g : Y' ⟶ Y`, `g' : X' ⟶ X`, `f' : X' ⟶ Y'`, and `sq : IsPullback g' f' f g`. There is no property instance on g, and no field base or separatedness assumption on the schemes. A supplied pullback square includes the literal fibre product as a special case and canonically identifies any other pullback. |
| Chosen compactification c=(j,p), pj=u | `c : Compactification f`, whose fields are `c.Z`, `c.i`, `c.g`, `c.comm`, `c.isOpenImmersion`, `c.isProper`. Quasi-compactness of `c.i` follows from `c.quasiCompact_openImmersion_iff` and `[QuasiCompact f]`; it is not omitted or imposed on g. |
| Base-changed compactification | `c.ofIsPullback sq`, with both upper and proper pullback squares supplied by the existing Compactification.BaseChange API. |
| Constant discrete module coefficients, etale and pro-etale categories | `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)` and `Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)`, respectively, and the analogous categories at every other corner. These are the existing six-functor fixed-scalar presentations of constant-ring module sheaves, canonically realized in the recorded ring-sheaf categories. The imported ProEtaleFiniteModules and RingedEtaleOriginWitness interfaces provide this realization; no ring sheaf or coefficient category is defined again. |
| Bounded-below input | `DerivedCategory.Plus` of the etale sheaf category. `DerivedCategory.Plus.ι` embeds it in the ambient derived category. Pro-etale outputs and operations are the ordinary unbounded ones, restricted to these inputs; no boundedness hypothesis is added to g and no completed operation occurs. |
| A_V and canonical a_v, a_w | `comparisonUpperStar ... V` and its `mapDerivedCategory`; `leftDerivedUpperStarComparisonIso g Λ` and the same at `g'`. These are degreewise comparison-pullback maps with the standard exact-pullback/left-derived identification. |
| F_u^e, F_u^p and their base changes | `Etale.rightDerivedLowerShriekOfCompactificationPlus ... c` and `ProEtale.rightDerivedLowerShriekOfCompactification ... c`; similarly at `c.ofIsPullback sq`. Their definitions are exactly exact degreewise open extension followed by proper derived direct image. |
| C_{c,L} | `compactExchangeTransportComparison Λ c`. It is the inverse of the existing normalized `compactSupportSiteComparison Λ c`, with the existing etale Plus-to-ambient compatibility inserted at the source. Its proper factor remains `fixedComparisonDirectImageMatePlus`; its open factor is the canonical adjunction comparison applied degreewise. |
| S_L=v^*C_c composed with a_v | `(compactExchangeTransportSource Λ g c).hom.app L`. Its body first applies `leftDerivedUpperStarComparisonIso` to F_u^e L, then whisks C by the pro-etale derived pullback. |
| T_L=F_{u'}^p(a_w) composed with C_{c'} | `(compactExchangeTransportTarget Λ sq c).hom.app L`. Its body applies C_{c'} after etale pullback, then whisks a_w by the base-changed proper/open functor. Explicit functor associators insert no extra maps of mathematical objects. |
| Specified etale exchange E_u^e | `Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap Λ sq c`, exactly the dependency's recorded declaration. |
| Specified ambient pro-etale exchange E_u^p | `rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat Λ) sq c`. This is exactly the second finite map returned by `finiteExchangeProjection` of def-exchange-projection: the proper unit-square-counit exchange followed by derived open base change. The smaller published finite-coefficient module is imported directly, avoiding the stale broad ExchangeProjection import which also loads duplicate retired modules. The input map g remains arbitrary. |
| Displayed equality for every L, natural in L | The first conjunct is an equality of natural transformations: `whiskerRight E^e (ι ⋙ A) ≫ T.hom = S.hom ≫ whiskerLeft (ι ⋙ A) E^p`. Components give precisely the displayed equation, and naturality is retained without a separate objectwise naturality assumption. |
| Retained etale-origin witness (L,alpha:A_T L≅N) | The second conjunct binds L, N and the actual isomorphism `alpha : (comparisonUpperStar ... X).mapDerivedCategory.obj L.obj ≅ N`. This is the pair itself in fixed-scalar coordinates, rather than a mere existence or a newly defined witness type. An ambient N is automatically bounded below because it is isomorphic to the exact comparison of L. |
| Witness transport identifies the exchanges | `compactExchangeTransportAtWitness Λ sq c L N alpha` is exactly `v^*F_u^p(alpha.inv) ≫ S.inv ≫ A(E^e) ≫ T.hom ≫ F_{u'}^pw^*(alpha.hom)`. The second conjunct equates it to `E^p.app N` for every such pair. |
| Identification unchanged under isomorphism of witnesses | Both witness-transported maps equal the same `E^p.app N`, which contains no witness. Thus any isomorphism of witnesses preserves the identification. This is stated through the stronger-looking, but explicitly requested, equality at each witness rather than an extra redundant conjunct. |

Dependency declarations read and reused:

- `WeilConjectures.Compactification.BaseChange`: `Compactification.ofIsPullback`,
  `isPullback_i_ofIsPullback`, `isPullback_g_ofIsPullback`; and
  `WeilConjectures.Compactification.Refinement`: `Compactification.Refinement` and the
  underlying `Compactification` definition.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `Etale.DerivedCategoryModule`, with the existing `DerivedCategory.Plus` inclusion.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: `FiniteCoefficientModules`,
  `finiteCoefficientRealization`, `finiteCoefficientComparison`; these supply the
  ring-sheaf representation behind the standard fixed-scalar six-functor encoding.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `Scheme.proEtaleSiteComparison` and
  its module inverse image; the six-functor name is `comparisonUpperStar`.
- `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange`:
  `comparison_derivedBaseChangeMap`; its current canonical comparison definitions are
  extracted into `Sheaf.SixFunctors.ProEtale.BaseChange.SmoothBaseChangeComparisons`,
  including `leftDerivedUpperStarComparisonIso` and the normalized proper comparison.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`:
  `openImmersionLowerShriekComparisonUpperStarIso` and
  `openImmersionLowerShriekComparison_coherence`.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`:
  `supportSiteComparisonCoefficientPullbackIso` and
  `supportSiteComparison_pullback_coherent`; the ordinary canonical coefficient
  comparison is derived by `leftDerivedUpperStarComparisonIso`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange`:
  `Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange`:
  `rightDerivedLowerShriekOfCompactificationBaseChangeMap` and its closing open
  base-change comparison. Read with `scompile.py --source`, including the unit-square-
  counit definition of the proper exchange and the inverse open-base-change factor.
- `Sheaf.Paper.RingedEtaleOriginWitness`: `Scheme.EtaleOriginWitness` and the retained
  pair fields in `ProEtale.EtaleOriginWitness`; we write that pair as explicit L/alpha
  binders in the fixed-scalar coordinates used by both actual exchanges.
- Added landed dependency `lem-sf-class-compact-support-comparison`, module
  `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`:
  `compactSupportSiteComparisonPlus`, `compactSupportSiteComparison`. The actual proper
  mate is `fixedComparisonDirectImageMatePlus` from
  `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`; the open comparison is
  `properOpenSiteExtensionIso` from `Sheaf.Paper.ProEtaleProperOpenComparison`.

Available proof dependencies are retained through the imported proper exchange module,
comparison modules, the exact-functor API, etale extension-by-zero definitions,
`Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange`, and
`Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized`. The proof-only node
`lem-fix-site-open-exchange` currently has no recorded Lean declaration and so has no
module to import; its precise use is documented in the theorem's proof docstring.
It is not needed to type the statement or construct its canonical maps.

Edge cases checked before writing: identity base change reduces to the normalized
identity comparisons; j=id gives proper direct-image exchange transport; p=id gives
open-exchange transport. Empty schemes and the zero coefficient ring are allowed by
all binders and functors. No nontriviality, nonemptiness, invertibility of a prime,
field, Noetherian, separated base-change, constructibility, finite Tor-amplitude,
completion, or degree restriction is introduced. The sheaf value universe is u+1,
with schemes in u, exactly the published six-functor site convention. No object/hom
universe identification is imposed. No STATEMENT-DISPUTED issue or statement correction.

Searches performed with the required wrappers:

- LeanFinder: `Comparison of etale and proetale compact support base change exchange
  under site comparison`. Eight results: etale site and etale-morphism facts, condensed
  sheaf constructions; no compact-support exchange-transport statement.
- Loogle: `CategoryTheory.NatTrans.exchange`. The generic horizontal-composition exchange
  law was found; it does not identify these two compact-support maps.
- Mathlib grep: `compactification.*[Cc]omparison|[Ee]xchange.*[Tt]ransport`. Zero hits.
- LeanSearch: `Etale proetale compact support exchange comparison natural transformation`.
  Eight results on generic NatTrans.exchange, sheaf pushforward natural transformations,
  product/coproduct comparisons and Dold-Kan; no exact statement.
- `rg` of the upstream source for this item id: no hit. Concept grep
  `comparison.*[Bb]ase[Cc]hange|[Cc]ompact.*[Cc]omparison|[Cc]omparison.*[Ll]owerShriek`
  found the proper-exchange transport and the older compact-support comparison.
  Reading the latter showed its arbitrary proper-isomorphism choice; it cannot be used
  for a normalized exchange identity. The already landed canonical site-comparison
  module supplies the correct mate and is reused.
- `rg` of Sheaf/Paper and Sheaf/AlgebraicGeometry for compact support, comparison,
  exchange and transport found the transported finite-level compact-support theorem,
  existing canonical comparisons and unrelated coefficient transport. No exact
  arbitrary-base-change identification with the specified ambient composite exists.
  All new declaration names were also searched with `rg`; no collision was found.

Validation: both delivered modules are compiled separately, in dependency order,
using scompile.py. The expected sole sorry is the item's named theorem. The sandbox
also repairs the existing canonical comparison's stale import, as described below.
Final single-file compilation passed without errors or warnings: canonical comparison 3.6 s,
item 13.3 s (sandbox confirmation 35.5 s), each within the default 60-second limit.
deliver2.py --no-push passed: commit ccb78828dd compiled both modules and passed
the server stage-2 preflight. The final push repeats those wrapper checks.

## Dependency modules

`lem-sf-class-compact-support-comparison`: the already landed normalized comparison
is needed for C; its recorded module imported the original
`WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriek` after its other imports had
loaded the migrated finite-coefficient declarations. scompile rejected the duplicate
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification`. Under section
1(B), replace only that direct import with
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek`. The module
still defines exactly the same two normalized proper/open comparisons, with every
signature and definition body unchanged. The dependency node changes only in `lean`,
including a precise `lean.note`. No source statement or mathematical hypothesis changes.

## Second reading by Q78

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
