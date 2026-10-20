## Worker report

The item is stated by `WeilConjectures.IntegralCompactificationBridge.integralCompactificationComparisonBridge` in `lean/Sheaf/SixFunctors/IntegralCompactificationComparisonBridge.lean`. Its two maps are separately constructed, using the published integral compact-support functor, actual strict semilinear adjunction, and normalized constant-tower word calculus. The conclusion is equality of integral derived-category morphisms and naturality. Every postponed proof is a named theorem with a source and proof plan; every definition has data. No equality of finite evaluations, arbitrary intertwiner, or hypothesis identifying the two maps replaces the conclusion.

Hypothesis and clause audit:

| Node text | Lean rendering |
| --- | --- |
| Algebraic closure of a finite field | `D : FiniteFieldDatum.{u}`, with base `D.k` |
| Prime ell different from the characteristic | `(l : ℕ) [Fact l.Prime]`, `(hl : l ≠ D.p)`; the named helper `coefficientPrimeUnit` supplies the unit needed by the published compact-support functor |
| Finite extension E/Q_ell and its valuation ring/uniformizer/quotients | `[Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`; `constantRing l E`, `scalarRings l E`, and the published `calculus l E T` use `Padic.coefficientExtensionIntegers` and the canonical uniformizer; evaluation at n is the positive quotient n+1 |
| Separated finite-type k-schemes and morphisms f,g | `Over` instances on X,Y,Z; `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` on their structure maps and on f,g, together with `f.IsOver` and `g.IsOver` |
| Small pro-etale sites and completed coefficient sheaves | The published `System`, `calculus`, `ringedOpen`, `ringedPush`, and `H` use the original pro-etale site and its small model; the added coordinate modules transport between these exact models without identifying site object and morphism universes |
| Strict semilinear reduction/total-limit adjunction, actual unit/counit | `(calculus l E T).reduction`, `coefficientSequenceLimit l E T`, `(calculus l E T).adjunction.unit/counit` |
| Derived-complete constructible K of finite Tor amplitude | `K : sfIntegralConstructibleCategory l E X`; `bridgeDomain` includes `Admissible`, whose definition includes `finiteTorConstructibleIntegral` |
| Compatible origins, normalized reductions, common finite windows at intermediate systems | `bridgeDomain ... lo hi torLo torHi`, expanded by `singleDomain` and `systemWordDomain`; `SystemAdmissible` is the dependency's predicate with `IsNormalizedCoefficientSequence`, retained `Origins`, finite-level constructibility and the same two intervals at every level |
| Compatible compactifications | `t : Compactification.Triangle f g`, with its open q, proper p, pullback square, and equations `i_q`, `p_g`; QC hypotheses on the three open factors and q |
| B_v = S_p J_j | `systemWord l E o c`; `o : Operations l E` and `r : Realizations l E D o` are the published normalized operation/realization interface, not a new private operation datum |
| Semilinear beta from Gamma and unital compositors | `systemBeta`: `r.properOpen.gamma`, `r.compositors.openComp`, `openCongr`, `r.compositors.pushComp`, then `t.p_g` |
| F_v is exactly the integral strict-quotient-tower compact-support functor | Every occurrence of F is `sfCompactSupportFiniteIntegralFunctor l D.k ... c E` |
| Direct single-compactification d | `directIdentification`: universal `r.realizationModel.push`, image of the actual `openReduction` followed by inverse completion unit, then `sfQcqsCompactSupportRealization`; it never uses `r.comparison` (the arbitrary expression-indexed family) |
| d and word comparisons are isomorphisms on the stated domain | `comparisons_isIso` records the three d maps and both required word maps as invertible; `inverseOrZero` merely extends inverses outside the theorem's domain to make ambient expressions typeable |
| Identity compactification normalization | The constructions use the actual adjunction units and normalized compositors. Their unital identifications identify F_id with L R and d_id with its identity; this is the identity case of the same formula, explained in Step 9 of the theorem's proof docstring. There is no hypothesis excluding identity factors |
| H is the complete-coefficient equivalence | `GeneratorReduction.H l E T`; `completedComparison_existsUnique` uses its full faithfulness on the two complete compact-support outputs |
| W_v, strict W_v, recursive normalized q | `word c : SfCbcWord`; its `.complete`, `.strict`, and `.a (constantDatum ...) (constantReducedUnits ...)` are the recorded word calculus, with `.a` exactly L(q) eta |
| Canonical coefficient/compact-support identifications in a_v | `wordCoordinates`: inverse published compact-support realization, `integralDirectScalarIso`, and `openSigmaHom`; `wordComparison` then applies the normalized `.a` |
| Concatenated a_g,f | `compositeWordComparison` uses the two canonical coordinate changes, `appendCompleteIso`, the concatenated word's `.a`, and `appendStrictIso` |
| Constant strict beta | `originalBeta` uses `ProEtale.StrictTower.gamma`, `jComp`, `jCongr`, `rComp`; `constantBeta` carries it through the exact site equivalence and normalized `wordTransport`, including both equivalence counits |
| Specified completed alpha coordinate equation | `constantComparison` is a_g,f followed by L(beta^T) followed by inverse a_h. `completedComparison` is its unique lift through H, selected by the existence-and-uniqueness theorem. This is determined by the node's coordinate equation, independently of the semilinear composite |
| Integral counit formula, in exactly its displayed order | `semilinearComparison`: inverse d_g, then L B_g R(inverse d_f), then L B_g(e), then L(beta), then d_h |
| Equality of actual integral maps before finite evaluation | First conjunct of `integralCompactificationComparisonBridge`; neither side is an evaluated or scalar-restricted map |
| Naturality in K | Second conjunct: for every morphism between two allowed inputs with common windows, F_g F_f(m) followed by the comparison equals the comparison followed by F_h(m). Via the first conjunct this is naturality of the specified completed alpha as well |
| Identity or empty opens, zero input | No nonempty, nonidentity, nonzero, or positive-dimension hypotheses occur. See the edge-case check below |

The `af`, `ag`, `ah` arguments present adjunctions between fixed model extension-by-zero and fixed pullback functors. They do not supply arbitrary operation comparisons. The open coordinate map and the transported constant beta use the same presentations; adjunction conjugation changes both compatibly. Thus the statement is uniform in these presentations. No `Nonempty` choice of such an adjunction is made.

Recorded dependency declarations read and used (directly or through the listed published interfaces):

| Module | Declaration/interface |
| --- | --- |
| `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` | `Padic.finite_coefficientExtensionRing`, and the recorded coefficient-ring constructions |
| `Mathlib.AlgebraicGeometry.Sites.Proetale` | `AlgebraicGeometry.Scheme.ProEt`, its topology |
| `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` | `WeilConjectures.coefficientDerivedSystemEvaluationCalculus`, the reduction calculus and total limit |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | `IntegralSystemRealization.Realizations`, `integralCompactificationSystemRealization`, its canonical bridge, proper/open, realization model and compositor fields |
| `WeilConjectures.Compactification.Refinement` and `.Triangle` | `AlgebraicGeometry.Compactification.Refinement`, `Compactification.Triangle` |
| `Sheaf.SixFunctors.AmbientProperOpenPasting` | `AlgebraicGeometry.ProEtale.AmbientProperOpen.ambientProperOpenPasting` and the normalized compositor/pasting interface |
| `Sheaf.Paper.QcqsCompactSupportRealization` | `WeilConjectures.sfQcqsCompactSupportRealization`; its underlying `sfCompactSupportFiniteIntegralFunctor` |
| `Sheaf.Paper.ConstantCompletionEquivalence` | `CategoryTheory.ConstantCompletion.equivalence` |
| `Sheaf.Paper.SfCbcCompactSupportCompositionLimit` | `AlgebraicGeometry.Scheme.sfCbcCompactSupportCompositionLimit`, `SfCbcWord.a`, append isomorphisms and fixed generator comparisons |
| `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus` | `ProEtale.StrictTower.normalizedProperOpenCalculus`, `R`, `J`, `gamma`, `jComp`, `rComp` and adjunctions |
| `Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison` | `GeneratorReduction.constantSemilinearGeneratorComparison`, `H`, `constantDirectUnderlying`, `integralDirectScalarIso`, `openSigmaHom` |
| `Sheaf.SixFunctors.GeneratorReductionStatement` | `GeneratorReduction.generatorReductionCoherence`, `SystemAdmissible`, `Admissible` |
| `Sheaf.SixFunctors.IntegralOpenReductionComparison` | `IntegralOpenReduction.integralOpenReductionComparison`, used through `RealizationModel.openReduction` |
| `Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison` | `CategoryTheory.ringedTowerPushforwardLimitComparison`, universal proper/limit normalization |
| `Sheaf.SixFunctors.SemilinearProperOpenMatePasting` | `ProEtale.SemilinearProperOpen.semilinearProperOpenMatePasting`, used through the realization package |
| `Mathlib.CategoryTheory.Adjunction.Mates` | `mateEquiv`, `mateEquiv_vcomp` and its composition rules |

`def-weil-scheme-morphism-properties` is a convention node; its named Mathlib property classes are used. The recorded `WeilConjectures.exchangeFunctoriality` in `Sheaf.Paper.ExchangeFunctoriality` was read: it states the large exchange-functoriality package, rather than exporting a component alpha for this exact integral subtype and coordinate formula. The owning-item helper `completedComparison` supplies that component canonically by the node's stipulated formula and the complete-category Hom bijection, as authorized for missing canonical helpers. It does not replace or restate that larger theorem.

Edge cases: n=0 in Lean denotes the first positive quotient, not R/(1). Prime ell different from D.p makes its cast a unit, with no extra characteristic assumption. The original small pro-etale site's object/morphism universes remain distinct; only exact site-model transport is used. Identity factors are admitted and use the normalized unitors and actual reduction/limit triangles. For an empty open, its extension is zero; both composites give the unique map between zero outputs. Zero K is admitted. No reduction evaluation is used as a faithfulness criterion. The finite interval bounds are inclusive integers; inconsistent windows are already excluded by the published domain's lo ≤ hi conditions.

Search audit: the sandbox `searches.jsonl` records the exact msearch results. LeanFinder for the item's full title returned normalization/condensed-counit results, not this equality. Mathlib grep `compactification.*[Cc]omparison|semilinear.*[Cc]ounit` in CategoryTheory returned 0. Loogle `Adjunction.counit, Adjunction.unit` reported unknown identifier (not counted as evidence of absence); the corrected `CategoryTheory.Adjunction.homEquiv` returned generic adjunction API. The two added-nodes' LeanSearch queries returned generic site-equivalence/sheaf pushforward or proper/open composition results; Loogle `CategoryTheory.Functor.whiskeringRightObjCompIso` found the generic whiskering comparison used here. LeanFinder for site transport and strict compactification composition found only unrelated condensed/adjunction results. Project and DAG searches inspected the existing semilinear operations, coefficient transport, strict-tower exchange normalization, and completed-coefficient pushforward nodes; none supplies this normalized original-site/small-model transport or assembled beta. Blueprint searches `constant tower site transport` and `compactification composition map` both returned no hit. Searches of `lean/WeilConjectures`, including the item id, and `lean/Sheaf` found no existing declaration of the target. Consequently no existing:true binding is appropriate.

Validation: the initial repair dry run reproduced the returned timeout in
`IntegralCompactificationBridgeCoordinates`; the server compiled the ordinary module
in 5.8 seconds. The repair reuses the published
`GeneratorReduction.DirectSquareNormalization` predicate instead of repeating its
large cochain equation inside `directModel_existsUnique`, and gives `directModel`
an explicit return type. Expanding that predicate gives the same two unit composites
and the same exact-localization factors; its homogeneous equality implies and is
equivalent to the former `HEq` because the endpoints coincide. Thus the unit
normalization and unique choice are preserved. No global build or direct repository
mutation was run. No statement correction or STATEMENT-DISPUTED issue is asserted.

## New nodes

`def-sf-integral-compactification-ordinary-site-transport` owns `IntegralCompactificationBridgeOrdinaryCoordinates.lean`: the exact termwise/derived site-model transport, and the ordinary direct-image comparison uniquely fixed by identity on underlying sections. Its source is the original site's canonical model equivalence (Stacks 00VC) and ordinary direct image (03D7), in the blueprint Step 5 comparison. The Mathlib, project and DAG searches above found generic site equivalence but no section-normalized direct square for these fixed coefficient and site models.

`def-sf-integral-compactification-site-transport` owns `IntegralCompactificationBridgeCoordinates.lean`: the termwise direct square, its unique derived-unit-normalized derived comparison, and the invertible pullback/open adjunction mates. The normalizations use the actual cochain universal unit and exact-localization factorization, rather than mere existence of an isomorphism. Sources: Stacks 0941, 0D6E, 07A4, 03DI and blueprint Step 5. The existing strict-tower operations do not export transport to the small-model word calculus; the searches above exclude a duplicate specialized interface.

`def-sf-integral-compactification-word-comparisons` owns `IntegralCompactificationBridgeWords.lean`: the two-letter words, their normalized transports, and the independently assembled semilinear and constant strict beta maps. Sources: the blueprint Step 5 and the proper/open calculus (Stacks 0F7B--0F7F). This is composition for a supplied compactification triangle, not the existing exchange-pasting theorem or change-of-coefficient comparison. Its own search records retain the actual LeanSearch, LeanFinder, Loogle and grep results.

## Second reading by Q03

This was a solo dispatched worker; no separate worker or subagent was started, in accordance with the dispatch instructions. A final self-audit compared every clause with the node and rejected an abstract arbitrary-map interface: the delivered version uses the actual compact-support functor, explicit normalized transports, actual recursive words, strict beta maps and counit. The maintainer's independent review remains independent; this paragraph does not claim a second person's review.

## Repair of immutable head 494c4ff8bd68

The return concerned file-only compilation of the ordinary and derived coordinate
modules. The retained packet was tested first, as requested, and its dry run
reproduced the derived timeout. Compiler profiling of a scratch copy identified slow asynchronous kernel
checks of `directModel_existsUnique`, a generated `directModel` instance proof,
and `directModel` itself; the end-of-file linter was waiting for these checks. The repaired delivered module uses the existing generic normalization
predicate and an explicit result signature rather than repeating the large equation.
It also names the existing additive, finite-limit and finite-colimit preservation
instances of `towerModel` before forming its derived functor. These are real
`inferInstance` constructions, with no new assumptions or postponed proofs; naming
them prevents repeated expansion of the exact-equivalence proof terms.
The repair changes neither the compactification bridge statement nor its canonical
maps, site universes, or domains. The saved ordinary/word/main modules are retained.
The `lean.statement` record of the derived transport is updated verbatim to include
its explicit return type. All four files are checked through `scompile.py`, followed
by the required delivery preflight and compile.

Repair validation: prescribed `scompile.py` passed every delivered module in its own
compiler invocation, with no errors or unexpected warnings: ordinary coordinates
2.6 s, derived coordinates 38.1 s (sandbox check 45.3 s), words 3.0 s, bridge 4.9 s.
The returned 60-second failure is repaired without increasing the limit, disabling
linters, or splitting another module.

The delivery preflight caught a record-generation error: an update had truncated
`constantBeta`'s `lean.statement` at the named argument `(A := ...)` instead of
the declaration's body delimiter. The record is repaired to contain its complete
verbatim signature. This affects JSON metadata only.
