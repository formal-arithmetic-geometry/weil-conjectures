## Worker report

The new module `Sheaf.Paper.CompletedCompactSupportExchange` defines
`AlgebraicGeometry.Scheme.completedCompactSupportExchange`. It contains one definition,
with real data and no new theorem, sorry, choice, or helper notion. The existing node is
changed only in `lean`.

Source checked: current blueprint `main-20261015`,
`sec-six-functors-basics/sk-prop-sf-cbc/def-cbc-completed-exchange-map.md`, Definition 1939,
and the node's expanded strict-tower formulation (order 1588). The current blueprint's
open-comparison display uses g-prime twice: its left pullback is the ambient projection
bar-g-prime, as already corrected explicitly in the DAG statement. This delivery uses
that well-typed upper open square and does not change the statement.

### Hypothesis and clause correspondence

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Four schemes X-prime, X, Y-prime, Y and arrows f, f-prime, g, g-prime | Explicit scheme and morphism binders, all in universe t. |
| Compactification c=(j,p), proper p, open j, p j=f | `c : Compactification f`; `c.i`, `c.g`, `c.isOpenImmersion`, `c.isProper`, `c.comm`. |
| f separated and finite type | A compactification implies `c.isSeparated` and `c.locallyOfFiniteType`; `[QuasiCompact f]` is the remaining condition for finite type. It also derives `QuasiCompact c.i` with `c.quasiCompact_openImmersion inferInstance`. There is no extra finiteness assumption on g. |
| Base-changed compactification c-prime and bar-g-prime | `c' : Compactification f'`, `gbar : c'.Z ⟶ c.Z`, `properSquare : ChosenCartesianSquare gbar c'.g c.g g`, `openSquare : OpenImmersionSquare g' c'.i c.i gbar`. These impose both pullback universal properties and the projection identities. Their pasted outer square is the compact-support square. They allow any presentation of the base change, not just the literal pullback term. |
| Schemes over a common S | The construction uses the underlying square. Every such square is over Y via f and g; an externally supplied S-structure imposes no additional constraint on this underlying construction. |
| j and j-prime quasi-compact | The body derives the needed instance for j from c and quasi-compact f. Quasi-compactness of its base change j-prime follows from the upper Cartesian square; the open comparison interface only needs the instance for j. |
| Noetherian adic ring, finite perfect positive quotients, additive torsion | `d : AdicCoefficientDatum A` with `[CommRing A]`; the recorded datum bundles these hypotheses. |
| I=(a_1,...,a_r), including empty tuple | `r : ℕ`, `a : Fin r → A`, `ha : Ideal.span (Set.range a) = d.ideal`. These are exactly the finite generator data of intrinsic completion. |
| Completed coefficient sheaves A_W and full derived categories | `d.derived`, `d.push`, `d.completedPull`, and `cbcDerivedOpenShriek` all use the actual completed coefficient sheaves, not the discrete constant A-module categories. A has universe t+1, with site object universe t+1 and morphism universe t. |
| K intrinsically derived I-complete | `K : (cbcCompleteProperty d X r a ha).FullSubcategory`. `K.obj` is its derived object and its property is the recorded intrinsic Koszul-unit invertibility. |
| M=j_!K, exact localized ringed-site extension by zero | `(cbcDerivedOpenShriek d c.i c.isOpenImmersion).obj K.obj`, using the existing open comparison's normalized module construction and its exact termwise descent. |
| Completed rings restrict correctly along opens | The existing `cbcDerivedOpenShriek` and `cbcDatumCompletedExchange` use the coefficient localization and scalar comparisons of the recorded open-comparison dependency. No replacement coefficient structure is supplied. |
| M and Rp_*M are complete, quotient unit invertible | These are supplied by the cited `completedOpenExchangeComparison`, `AdicCoefficientDatum.push_complete`, and `koszulReconstruction` interfaces. The map's ambient proper factor needs no additional certificate; no extra completeness hypothesis is introduced. |
| Relative Rf_!=Rp_*j_!, and its base change | The source and target explicitly display the composites of `cbcDerivedOpenShriek` and `d.push`, exactly the compactification-relative formula. |
| Strict reduction, strict termwise pull/push, tensor comparisons | Reused inside `d.completedExchange`: `completedReductionTower`, `d.towerPull`, `d.towerPush`, `d.reductionTowerPullbackIso`, `d.towerProjection`. They are defined on strict derived towers, including quotient transitions. |
| Pi is the diagram counit-tensor projection adjunct and is invertible | The existing `d.towerProjection` and its isomorphism instance are used by `d.towerH` and `d.towerH'`. No arbitrary isomorphism or assumption that the entire quotient diagram is perfect is introduced. |
| H, H-prime and strict v=H-prime R(e) H-inverse | `d.towerV'` is defined as `towerH.inv ≫ towerV ≫ towerH'.hom`, and `towerV` is the pullback/reduction comparison followed by reduction of the ambient mate. This is the displayed H formulation after its canonical source identification. `exchangeRealizationH`, `exchangeRealizationHPrime`, and `strictTowerExchangeMateNormalization` record exactly that identification. |
| a, s, Rlim(v), c-inverse and proper gamma | The first factor is literally `d.completedExchange properSquare M`: `completedRlim.map towerH.hom ≫ completedRlim.map towerV' ≫ directImageRlimIso.inv.app ...`. The a identification is definitional in `d.completedPull`. This is the node's ordered three-factor gamma. |
| Agreement with completed proper base change on witnessed reductions | `completedBaseChangeMap` is definitionally this same `completedExchange`; `strictTowerExchangeMateNormalization` retains the finite witnesses and strict equality; `completeProetale_isIso` concerns this very map. No witnesses are added to the definition's domain. |
| Canonical completed open beta | `(cbcDatumCompletedExchange d openSquare r a ha).app K`, the existing comparison on the same `d.completedPull` presentation as proper gamma. Its coefficient/tower transports retain the universal counits and completion unit. |
| Ordered compact-support exchange gamma then Rp-prime_*(beta) | The definition body is `d.completedExchange properSquare M ≫ (d.push c'.g).map ((cbcDatumCompletedExchange d openSquare r a ha).app K)`. |
| No invertibility or compactification-independence assertion | The result is a morphism `⟶`. There is no new isomorphism assertion, coherence theorem, or assumption of etale origins, constructibility, boundedness, smoothness, or condensed-module realization. |

### Dependency declarations

All recorded statement-dependency modules are imported. The declarations were read in
the source checkout or the current shared side-project sources; the decisive construction
files were read in full. No dependency interface is replaced.

| Dependency | Module and declaration |
| --- | --- |
| `def-cbc-compact-support-square` | WeilConjectures.Compactification.BaseChange — AlgebraicGeometry.Compactification.baseChange |
| `lemma-nagata-open-immersion-qc-over-separated-target` | Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated — AlgebraicGeometry.QuasiCompact.of_comp |
| `lem-pod-separated-finite-type-base-change` | Mathlib/AlgebraicGeometry/Morphisms/Separated.lean, Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean, Mathlib/AlgebraicGeometry/Morphisms/QuasiCompact.lean — AlgebraicGeometry.IsSeparated.isStableUnderBaseChange, AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange, AlgebraicGeometry.quasiCompact_isStableUnderBaseChange |
| `def-weil-pbc-adic-coefficient-datum` | Sheaf.Paper.AdicCoefficientDatum — AlgebraicGeometry.Scheme.completedReductionTower |
| `def-weil-pbc-intrinsic-completion` | Sheaf.Paper.IntrinsicCompletionCompleted — AlgebraicGeometry.Scheme.IsCompletedIntrinsicallyDerivedComplete |
| `def-weil-pbc-proetale-operations` | Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations — AlgebraicGeometry.Scheme.sfIntrinsicDerivedPullback |
| `lem-weil-pbc-profinite-coefficient-inverse-image` | Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage — AlgebraicGeometry.Scheme.proEtale_profinite_coefficient_inverse_image |
| `lem-pur-site-restriction-module-adjunction-exact` | Sheaf.CategoryTheory.LocalizedModuleExactIndependent — SheafOfModules.localizedModuleExactIndependent |
| `lem-weil-proetale-weakly-etale-localization` | Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization — AlgebraicGeometry.Scheme.ProEt.weaklyEtale_localization |
| `lem-sf-exact-functor-derived-triangulated` | Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean — CategoryTheory.Functor.mapDerivedCategory |
| `prop-weil-pbc-direct-image-limits` | Sheaf.Paper.CompletedDirectImageLimits — AlgebraicGeometry.Scheme.AdicCoefficientDatum.directImageRlimIso |
| `prop-weil-pbc-koszul-reconstruction` | Sheaf.Paper.KoszulReconstruction — AlgebraicGeometry.Scheme.koszulReconstruction |
| `def-weil-pbc-projection-compactification` | Sheaf.Paper.ProjectionCompactification — AlgebraicGeometry.Scheme.proEtaleRingCompactSupportImage |
| `def-weil-pbc-ambient-ringed-exchange` | Sheaf.Paper.PbcActualRingedExchange — AlgebraicGeometry.Scheme.pbcActualCompletedAmbientExchange |
| `def-weil-pbc-completed-pullback` | Sheaf.Paper.PbcActualStrictPullback — AlgebraicGeometry.Scheme.pbcActualStrictCompletedPull |
| `lem-cbc-completed-extension-zero-comparison` | Sheaf.Paper.CompletedOpenExchangeTransport — AlgebraicGeometry.Scheme.completedOpenExchangeComparison |
| `def-cbc-exchange-map` | WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange — AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap |
| `lem-weil-pbc-diagram-site-realization` | Sheaf.CategoryTheory.DiagramSiteRealization — CategoryTheory.exists_diagramSite_realization |
| `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` | Sheaf.Paper.PbcActualScalarPullback — AlgebraicGeometry.Scheme.pbcActualScalarDerivedPullIso_exists |
| `lem-weil-pbc-ringed-projection-mate-exact` | Sheaf.Paper.ProjectionMateExact — SheafOfModules.ringedProjectionMateExact |
| `def-weil-pbc-projection-formula-map` | Sheaf.Paper.ProjectionFormulaBaseChangeNaturality — AlgebraicGeometry.Scheme.proEtaleProjectionFormulaMate |
| `lem-weil-pbc-right-adjoint-preserves-kinjective` | WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp — CategoryTheory.Adjunction.preservesKInjectiveComplexes |
| `lemma-weil-pbc-perfect-projection-formula` | Sheaf.Paper.PerfectProjectionFormula — AlgebraicGeometry.Scheme.PerfectProjection.perfect_projection_formula |
| `lem-weil-tower-category-levelwise-abelian` | Mathlib/CategoryTheory/Abelian/FunctorCategory.lean — CategoryTheory.Abelian.functorCategoryAbelian |
| `prop-weil-pbc-rlim-functoriality` | Sheaf.Paper.CompletedRlimFunctor — AlgebraicGeometry.Scheme.completedRlim_computation |
| `def-weil-pbc-etale-origin-witness` | Sheaf.Paper.RingedEtaleOriginWitness — AlgebraicGeometry.Scheme.EtaleOriginWitness |
| `def-weil-pbc-completed-base-change-map` | Sheaf.Paper.CompletedBaseChangeMap — AlgebraicGeometry.Scheme.AdicCoefficientDatum.completedBaseChangeMap |
| `thm-weil-pbc-complete-proetale` | Sheaf.Paper.CompleteProetale — AlgebraicGeometry.Scheme.completeProetale_isIso |
| `lem-weil-pbc-strict-tower-exchange-mate-normalization` | Sheaf.Paper.StrictTowerExchangeMateNormalization — AlgebraicGeometry.Scheme.strictTowerExchangeMateNormalization |
| `lem-pc-pre-derived-adjoint-functors-general` | Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral — CategoryTheory.preDerivedAdjunctionGeneral |

The additional open-interface declarations used directly are in
`Sheaf.Paper.CompletedOpenExchangeTransport` (`cbcDatumCompletedExchange`) and its
public dependency `Sheaf.Paper.CompletedExtensionZeroComparison`
(`cbcCompleteProperty`, `cbcDerivedOpenShriek`). The proof-only explanatory dependencies
in the expanded node remain imported as required by the stage-2 contract.

### Edge cases

Checked the declaration and dependency interfaces for the empty scheme and zero complex:
neither nonemptiness nor nontriviality is assumed. The empty finite generator tuple r=0
is admitted, and `ha` then means I=0. I equal to the unit ideal and the zero coefficient
ring are not excluded by this definition beyond the recorded adic-datum conditions.
All positive quotients are represented by n+1 in the existing tower interface, including
n=0 (exponent 1). Unbounded complete complexes are admitted. Identity base changes,
identity compactifications of proper maps, empty opens, and arbitrary non-flat g are
included. The map does not assert the identity/pasting/compactification comparisons,
which belong to the cited later theorems. No universe equality was added.

### Searches

- `msearch.py ... leanfinder "Completed compact support exchange map as composite of
  completed proper base change and completed extension by zero comparison"`: eight
  unrelated hits (uniform completions, compactly supported continuous maps and
  CompHausLike comparisons); no match.
- `msearch.py ... loogle "SheafOfModules, DerivedCategory"`: zero hits.
- `msearch.py ... grep "completed.*(Exchange|exchange)|compactSupportExchange"`: zero hits.
- `msearch.py ... leansearch "Completed compact support base change exchange defined by
  a proper compactification and completed extension by zero"`: eight unrelated support
  and continuous-extension hits; no match.
- `rg` in Mathlib, upstream `WeilConjectures`, shared `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `CompletedCompactSupportExchange`,
  `completedCompactSupportExchange`, `cbcCompletedCompactSupport`: no existing declaration.
- Broader `rg` for completed exchange and compact-support exchange, and the item id in
  upstream sources: found the existing proper factor, completed open comparison, and
  finite-etale compact-support map, but no completed compact-support composite. Reused
  those existing factors rather than restating them.

### Validation

`python3 .../scompile.py Q22 def-cbc-completed-exchange-map
lean/Sheaf/Paper/CompletedCompactSupportExchange.lean` passed cleanly for the sandbox
and module-path compile (4.8 s and 4.1 s respectively). The first exploratory compile
used the nonexistent scheme class `FiniteType`; it was repaired to the exact
quasi-compact condition, since the compactification supplies local finite type.
No warning, sorry, new axiom, dependency repair, new node, or statement correction remains.

Required `deliver2.py Q22 def-cbc-completed-exchange-map --no-push` printed
`OK (dry run)` at commit `b7a16f64a6`: compilation and preflight passed except for
the independent second-reading section, which the second reader writes. Nothing pushed.

## Second reading by Q22

I independently opened the node copy, the source definition at
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/def-cbc-completed-exchange-map.md`
(Definition 1939, order 1588), and `lean/Sheaf/Paper/CompletedCompactSupportExchange.lean`.
The source introduces the compact-support cartesian square, the adic datum, a derived
I-complete `K`, a compactification `c=(j,p)` and its cartesian base change `c'`, and
then defines one morphism as completed proper exchange for `p` applied to `j_!K`,
followed by the completed extension-by-zero comparison. The Lean declaration renders
these items as follows.

* The four schemes and square are implicit `Scheme.{t}` objects with arrows `f`, `f'`,
  `g`, and `g'`; `properSquare : ChosenCartesianSquare gbar c'.g c.g g` and
  `openSquare : OpenImmersionSquare g' c'.i c.i gbar` give the lower and upper
  cartesian squares and the shared projection `gbar`.
* `d : AdicCoefficientDatum A`, with `A : Type (t + 1)` and `[CommRing A]`, is the
  recorded coefficient datum. `r`, `a : Fin r → A`, and `ha` present the finite
  generators of its ideal, including `r = 0`; `K` is exactly an object of
  `(cbcCompleteProperty d X r a ha).FullSubcategory`, hence the source's intrinsic
  derived-I-completeness condition.
* The source compactification is `c : Compactification f`; its open and proper maps
  are `c.i` and `c.g`. The target compactification is `c'`, and the two square
  structures force it to be the specified base-change presentation. The only explicit
  `[QuasiCompact f]` is exactly the remaining part of finite type: `Compactification`
  supplies separatedness and locally finite type, while quasi-compact plus locally
  finite type gives finite type. No condition on `g` is added.
* The left side is
  `(d.completedPull g).obj ((d.push c.g).obj
  ((cbcDerivedOpenShriek d c.i c.isOpenImmersion).obj K.obj))`, rendering
  `Lg^*_{comp} Rp_*j_!K`. The right side is
  `(d.push c'.g).obj ((cbcDerivedOpenShriek d c'.i c'.isOpenImmersion).obj
  ((d.completedPull g').obj K.obj))`, rendering
  `Rp'_*j'_!Lg'^*_{comp}K`.
* The body is the ordered composite
  `d.completedExchange properSquare (...) ≫ (d.push c'.g).map
  ((cbcDatumCompletedExchange d openSquare r a ha).app K)`. Thus the first factor is
  the specified strict-tower completed proper exchange and the second is precisely the
  canonical completed open comparison. No invertibility, compactification
  independence, etale-origin witness, boundedness, smoothness, or extra hypothesis is
  asserted.

The dependency interfaces were reopened. `Compactification`, `ChosenCartesianSquare`,
`OpenImmersionSquare`, `AdicCoefficientDatum.completedExchange`,
`cbcCompleteProperty`, `cbcDerivedOpenShriek`, and `cbcDatumCompletedExchange` have the
objects and directions used above; no private replacement notion occurs. The source
node's clauses about completed coefficient sheaves, strict quotient towers, the
projection-formula mate, and the normalization with `completedBaseChangeMap` are
implemented by the cited dependencies used by `completedExchange`; the definition
itself introduces no arbitrary map or choice.

Edge cases checked: `r = 0` and the zero ideal are admitted by `Fin r` and `ha`; zero
complexes, empty schemes, empty opens, identity squares and identity compactifications
are not excluded; `n = 0` is represented by the existing `n + 1` quotient tower; `g`
may be arbitrary and non-flat; and no universe equality is imposed beyond the datum's
`t + 1` coefficient universe and `Scheme.{t}` sites. The declaration has no hidden
nonemptiness or nontriviality assumption.

I repeated the existing-definition searches with LeanFinder/Loogle/LeanSearch-style
queries and `rg` over Mathlib, upstream `WeilConjectures`, shared `lean/Sheaf`, and
`dag/lean_names_upstream.json` for `CompletedCompactSupportExchange`,
`completedCompactSupportExchange`, and compact-support completed exchange variants.
Only unrelated completion, compact-support topology, and ordinary exchange declarations
were found. The existing proper exchange and open comparison were reused; this composite
notion is absent, so a new definition module is required.

No mismatch was found between the node statement and the Lean signature, and no repair
was needed. In particular, the explicit quasi-compact hypothesis is not an added
mathematical restriction: it supplies exactly finite type from the compactification's
locally-finite-type property. The module compiled with
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q22 def-cbc-completed-exchange-map
lean/Sheaf/Paper/CompletedCompactSupportExchange.lean` with no errors or warnings.
