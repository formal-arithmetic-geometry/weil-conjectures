## Worker report

Item: `lem-cbc-completed-extension-zero-comparison`, Q34, stage 2, 2026-10-16.
Module: `Sheaf.Paper.CompletedOpenExchangeTransport`.
Main declaration: `AlgebraicGeometry.Scheme.completedOpenExchangeComparison`.
All theorems have `sorry` proofs. Every definition has real data, obtained either
by functor composition or from a uniquely counit-normalized existence theorem.
No other DAG node is stated or changed. The item's mathematical statement is unchanged.

This is the interface repair specified by
`coord/repair-notes/lem-cbc-completed-extension-zero-comparison.json`, including
its archived invalidated binding. The withdrawn declaration is not rebound.
The old `CompletedExtensionZeroComparison` module and every public declaration
remain available by public import. The new comparison uses `d.completedPull`,
which is the presentation used by the actual proper completed exchange.
It also exposes `cbcDatumActualStrictTransport` from the presently recorded
`pbcActualStrictCompletedPull`, rather than silently using a different prerequisite.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Commutative Noetherian adic ring, finitely generated ideal, torsion first quotient, finite perfect positive quotients | `{A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)`, the recorded arithmetic datum, reused without additional coefficient conditions |
| Four schemes and the cartesian open square, with no condition on the bottom arrow | `sq : AlgebraicGeometry.OpenImmersionSquare gU j' j g`; its inherited chosen cartesian square and its two `IsOpenImmersion` fields |
| Quasi-compactness of j | `[QuasiCompact j]`; no quasi-compactness or properness binder on `g` or `gU` |
| Completed coefficient sheaf, not the constant sheaf A | `d.completedRing T`, definitionally the recorded `completedReductionCoefficient T d`; all objects lie in `d.derived T` |
| Ringed slice identification on both opens | The retained `cbcCompletedSliceMap`, fixed by every finite quotient projection, and `cbcModuleToSlice`, used by `cbcOpenShriek` |
| Extension by zero is sheafification of the direct-sum module presheaf | `cbcOpenShriek` is exactly slice transport followed by `SheafOfModules.extensionByZeroPresheaf` and `PresheafOfModules.sheafification (𝟙 _)` |
| Extension applied termwise to complexes | `cbcDerivedOpenShriek`, the exact extension functor's `mapDerivedCategory` |
| K is intrinsically derived I-complete | `K : (cbcCompleteProperty d U r a ha).FullSubcategory`, with `r : ℕ`, `a : Fin r → A`, `ha : Ideal.span (Set.range a) = d.ideal`; the predicate uses the published intrinsic Koszul completion via its canonical coefficient transport |
| j!K is intrinsically complete | First clause of the final universal quantifier, `cbcCompleteProperty d X ... ((cbcDerivedOpenShriek ...).obj K.obj)` |
| Completed pullback of j!K to X' | Source functor of `cbcDatumCompletedExchange`: open extension followed by `d.completedPull g` |
| Extension on X' of completed pullback to U' | Target functor of `cbcDatumCompletedExchange`: `d.completedPull gU` followed by the base-changed open extension |
| Canonical completed base-change map is an isomorphism | `IsIso (cbcDatumCompletedExchange d sq r a ha)` |
| Natural in complete K | The map is a natural transformation on the full complete subcategory; its naturality is part of its type, with all complete-object morphisms included |
| Both displayed objects are intrinsically complete on X' | Second and third clauses of the final universal quantifier, with exactly the two displayed endpoints |
| Map induced by finite canonical exchanges and the strict derived-limit comparison | Definition transports the retained `cbcCompletedExchange` using `cbcDatumCompletedTransport`; the latter is Rlim applied to a counit-normalized comparison of whole strict towers, not independent finite-level choices |

Canonical normalization is part of the delivered interface:

* `cbcDatumFiniteCoefficient_eq` compares the actual two finite structure maps.
  `cbcDatumCoefficient_eq` compares their limit lifts. Their proof plans use all
  projections and the quotient-transition naturality equations.
* `cbcDatumModulePull_eq` identifies the fixed tensor object AND map formulas.
  `cbcDatumTowerModulePull_eq` compares whiskering on the entire strict tower
  category, so it retains every actual transition map. Their complex versions
  retain the same differentials and the proof-irrelevant additive instances.
* `cbcDatumOrdinaryTransport_exists` and `cbcDatumTowerTransport_exists` assert
  unique natural isomorphisms with explicit equations on actual cochain
  representatives and the published universal derived counits. These determine
  the isomorphisms used in the definitions; no mere `Nonempty` endpoint choice
  or new comparison assumption is used.
* `cbcDatumCompletedTransport` applies the same Rlim functor to the strict
  comparison after the same recorded reduction functor.
* `cbcDatumCompletedTransport_unit` compares the old ordinary-to-completed unit
  with `d.ordinaryToCompleted`. `cbcDatumActualStrictTransport_unit` separately
  records this equation for the current prerequisite's strict unit.
* `cbcDatumOrdinaryExchange` transports the retained, generator-normalized
  adjoint mate with the ordinary counit transports.
  `cbcDatumCompletedExchange_unit` explicitly requires compatibility of the
  completed exchange with that mate and the actual quotient completion units.

Dependency declarations used, read with their source signatures and docstrings:

* `Sheaf.Paper.AdicCoefficientDatum`: `AdicCoefficientDatum`,
  `completedReductionCoefficient`, `completedReductionTower`, the finite ring
  comparison, and the `AdicCoefficientDatum.completedRing`/`derived` aliases.
* `Sheaf.AlgebraicGeometry.OpenImmersionSquare`: `OpenImmersionSquare`, including
  its chosen fiber-product identification and both open-immersion fields.
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` and its
  imported `QuasiCompact`; only the latter is a hypothesis of this lemma.
* `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`:
  `Scheme.ProEt.weaklyEtale_localization`, with concrete site and coefficient
  identifications, reused by the retained ringed-slice construction.
* `Sheaf.CategoryTheory.ExtensionByZeroPresheaf`:
  `SheafOfModules.extensionByZeroPresheaf`.
* `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification` with the identity ring map.
* `Sheaf.Paper.IntrinsicCompletionCompleted`:
  `IsCompletedIntrinsicallyDerivedComplete`; it is reused through the existing
  `IntrinsicCompletion` transport and `cbcCompleteProperty`, not redefined.
* `Sheaf.Paper.PbcActualStrictPullback`: `pbcActualStrictCompletedPull` and
  `pbcActualStrictCompletedPullUnit`, explicitly compared in the delivered API.
* `Sheaf.Paper.CompletedTowerPullback`: `completedCoefficientMap`,
  `completedModulePullback`, `completedTowerPullback`, ordinary/tower counits,
  and their named complex comparisons.
* `Sheaf.Paper.CompletedPullback`: `AdicCoefficientDatum.completedPull`,
  `towerModulePull`, `towerPull`, `ordinaryToCompleted`.
* `Sheaf.Paper.CompletedExtensionZeroComparison`: all retained slice/extension
  definitions, `cbcOrdinaryExchange`, `cbcCompletedExchange`, and the original
  theorem. This import preserves the old public API.
* The recorded proof dependency modules are imported without `public` wherever
  they are not statement dependencies. The existing Rlim constructions are
  reused; no new cone or inverse-limit object is chosen.

Edge cases checked before drafting: the empty open, the identity open, the zero
complex, the zero coefficient ring, ideal zero with empty generator tuple
`r = 0`, and the unit ideal with zero quotient coefficients. None is excluded
by a nonemptiness, nontriviality, positive-generator-count, boundedness or
constructibility assumption. Positive quotient level n means power n+1.
The site retains object universe t+1 and morphism universe t; coefficients are
`Type (t + 1)`. No equality between the site universes was imposed. Base change
is an arbitrary scheme morphism. The proof uses quasi-compactness only for
extension/product preservation, as the corrected node requires.

Searches for existing statements and transport:

* `msearch.py`, LeanFinder, query “canonical completed pullback base change
  extension by zero natural isomorphism preserving completion units”: eight
  hits about free sheaf pullback, continuous linear completion, uniform-space
  completion and ordinary scalar extension. No completed open-exchange transport.
* `msearch.py`, LeanSearch, query “completed pullback extension by zero base
  change natural isomorphism”: eight categorical pullback and hypercover hits,
  none the required completed pro-etale statement.
* `msearch.py`, Loogle, valid query `CategoryTheory.Functor, CategoryTheory.IsIso`:
  twelve generic functor/isomorphism and naturality lemmas, no specialized match.
  Earlier `CategoryTheory.Functor, CategoryTheory.NatIso` returned unknown
  identifier; this is recorded as a rejected query, not absence evidence.
* `msearch.py`, grep, `completed.*[Pp]ullback|extension[Bb]y[Zz]ero` in
  `CategoryTheory`: zero hits.
* `rg` in the upstream source, the side `lean/Sheaf/Paper` sources and the
  upstream declaration-name index for `completedExtensionZeroComparison`,
  `cbcCompletedExchange`, `completedOpen.*Transport`: only the retained side
  module gives the old exchange. The source tree has no occurrence of this
  blueprint node ID. The maintenance diagnostic explains why that old binding
  alone is insufficient.

No statement correction, new independent notion, dependency rewrite or
`STATEMENT-DISPUTED` flag is needed. Every added helper belongs to the canonical
comparison of this node and has its source, blueprint ID and proof plan in its
docstring. The node copy changes only `lean`.

Validation: `scompile.py Q34 lem-cbc-completed-extension-zero-comparison` accepted
the statement module and the separate `scratchpad/Consumer.lean` on current
server sources, with exit 0 and no diagnostics (statement 19.4 seconds, consumer
5.2 seconds in the check with the recorded proof imports). Local fallback was
needed because recompiling the existing `CompletedPullbackReduction` overlay
hit 60 seconds; server confirmation compiled that unchanged dependency in
11.2 seconds. No timeout was raised and no live source was modified.

The consumer uses six arbitrary schemes, `osq : OpenImmersionSquare gU j' j gX`
and `psq : ChosenCartesianSquare gX f' f gY`, with `[QuasiCompact j]` and a
complete `K` on U. There are no assumptions on `gX`, `gY`, or `gU`, and no
comparison is supplied as a hypothesis. It type-checks the actual composite

```lean
d.completedExchange psq
    ((cbcDerivedOpenShriek d j osq.isOpenImmersion).obj K.obj) ≫
  (d.push f').map
    ((cbcDatumCompletedExchange d osq r a ha).app K)
```

from completed pullback along gY of `f_* j_! K` to
`f'_* j'_!` of completed pullback along gU of K. The proper factor is exactly
the published `AdicCoefficientDatum.completedExchange`, and the second is
exactly the new open factor. This validates the consumer composition requested
by the maintenance note. A second consumer checks
`cbcDatumActualStrictTransport d h` at type
`pbcActualStrictCompletedPull d h ≅ d.completedPull h` for arbitrary h.
These probes are scratch validation, not declarations of another DAG node.

The final `deliver2.py ... --no-push` performs compilation again and preflight.
The independent second reading is intentionally left for the next worker.

## Second reading by Q34

I opened the current DAG node, its blueprint source place (order 1587), the
repair note and the complete `CompletedOpenExchangeTransport.lean` module. The
node's objects and clauses match the repaired declaration as follows:

* The adic datum is `d : AdicCoefficientDatum A` with `{A : Type (t + 1)}` and
  `[CommRing A]`; no extra coefficient, Noetherian-scheme, characteristic, or
  finiteness assumption is introduced.
* The square is `sq : OpenImmersionSquare gU j' j g`, supplying the four schemes,
  both open immersions, commutativity and the chosen cartesian identification.
  The sole square hypothesis is `[QuasiCompact j]`; there is no condition on
  `g` or `gU`, and quasi-compactness of `j'` is obtained by the recorded base
  change result.
* The completed coefficient sheaves and derived categories are rendered by
  `d.completedRing T` and `d.derived T`, with slice identifications supplied by
  `cbcCompletedSliceMap`/`cbcModuleToSlice`. No constant sheaf `A` is substituted.
* Extension by zero is `cbcOpenShriek`, built from the direct-sum
  `extensionByZeroPresheaf` followed by module sheafification, and its termwise
  derived functor is `cbcDerivedOpenShriek`.
* The input is quantified as `K :
  (cbcCompleteProperty d U r a ha).FullSubcategory`, where `r`, `a` and
  `ha : Ideal.span (Set.range a) = d.ideal` are the finite presentation of the
  intrinsic completion predicate. The three resulting conjunction clauses are
  exactly completeness of `j_!K`, of completed pullback of `j_!K`, and of
  `j'_!` of completed pullback of `K`.
* `cbcDatumCompletedExchange d sq r a ha` is the canonical map between those
  two endpoints. The declaration `completedOpenExchangeComparison` states
  `IsIso` for it and quantifies over every complete `K`; naturality is inherent
  in this natural transformation's type. The transport is the repaired
  `cbcDatumCompletedTransport` from the old presentation to `d.completedPull`,
  and its unit and quotient-transition normalizations are explicit in the
  preceding declarations.

Verdict: every hypothesis and conclusion clause of the node is rendered with
the same objects and quantifier order. The prior invalid binding used
`cbcCompletedPullback`; this module instead uses `d.completedPull` and exposes
the normalized transport, so that recorded repair is present. I found no new
mismatch and made no further source or node change.

Edge cases checked against the signatures and definitions: `r = 0` and empty
generator tuple, zero and unit ideals (including zero finite quotients), the
zero complex, empty and identity opens, empty schemes, singleton and empty
product families in the product argument, arbitrary base-change maps, and the
site universe convention `Type (t + 1)`/morphisms at `t`. None is excluded by
an unmentioned nonemptiness, boundedness, constructibility, characteristic, or
scheme finiteness assumption.

I repeated the existing-definition audit with LeanFinder/msearch for completed
pullback plus extension-by-zero exchange, Loogle for generic functor/isomorphism
matches, and `rg` over Mathlib, the upstream source and `lean/Sheaf`. The hits
were generic completion or pullback lemmas; no declaration states this
completed pro-etale comparison. The old public module remains imported, while
the new declarations are the canonical interface repair. The recorded consumer
probe compiles a composition with the actual proper `d.completedExchange` and
the new `cbcDatumCompletedExchange`, and a second probe checks
`cbcDatumActualStrictTransport` for arbitrary maps.

The repaired file compiles with the prescribed `scompile.py` wrapper and has
only postponed `sorry` proofs. No new definition node or dependency module is
needed, and no statement correction is being made in this reading.
