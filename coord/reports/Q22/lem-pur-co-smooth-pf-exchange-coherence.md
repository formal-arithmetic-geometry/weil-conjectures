## Worker report

This delivery states `AlgebraicGeometry.ProEtale.compactification_projection_exchange_coherence`
in `Sheaf.AlgebraicGeometry.CompactificationProjectionExchangeCoherence` with a single `sorry`.
It uses the canonical upstream maps underlying the recorded dependency
`Sheaf.Paper.ExchangeProjection`, without changing that module or its public imports.
No theorem is proved, no definition is hollow, no node statement is corrected, and no new node
is introduced. The item's node changes only in `lean`; no dependency node is changed.

The prior worker confused NZ's stage-1 split with a stage-2 landing. The ledger entry at
15:44 on 2026-10-17 records the reviewed split; the current item has no `lean` record.
NZ's report explicitly says no Lean was written or compiled. This assignment therefore still
needs its stage-2 statement and does not resplit the node.

### Hypotheses and clauses

| Node clause | Lean rendering |
| --- | --- |
| Finite commutative discrete coefficient ring | `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`. Discreteness is built into the fixed-scalar constant-coefficient sheaf presentation, with no topological coefficient category. |
| Schemes T, U, U', T' | `{T' T U' U : Scheme.{u}}`, without any field or absolute separatedness assumption. |
| Separated finite-type u | `{u : T ⟶ U}` with `[IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]`. |
| Arbitrary v and base-change arrows | `{v : U' ⟶ U}`, `{w : T' ⟶ T}`, `{u' : T' ⟶ U'}`; no property of v is assumed. |
| Cartesian square and chosen fibre-product identification | `sq : IsPullback w u' u v`, the standard Mathlib Cartesian-square assertion used by `finiteExchangeProjection`. The canonical fibre-product identification is the unique isomorphism respecting both projections; the maps depend only on `sq.toCommSq`. The recorded `ChosenCartesianSquare` is imported. |
| Supplied compactification c=(j,p), p proper, j open, pj=u | `c : Compactification u`, with `j = c.i`, `p = c.g`, ambient scheme `c.Z`, and `c.comm`. The upstream Compactification definition supplies open/proper instances. |
| Quasi-compact j | `[QuasiCompact c.i]` is included explicitly as in this node. |
| Base-changed compactification and bar(w) | `c.ofIsPullback sq`; the published exchange uses `pullback.fst c.g v` and its canonical open base-change square. |
| Ordinary unbounded constant-discrete module categories | `DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ))` and the corresponding category on U. These are exactly the finite-level categories in the recorded `finiteExchangeProjection`, not condensed or completed categories. |
| Arbitrary N and P | The explicit binders `(N : DerivedCategory ...)` and `(P : DerivedCategory ...)`, without boundedness, constructibility, etale origin, Tor amplitude, or perfection. |
| F_u^c = Rp_*j_! | `Rf_!(c)[ModuleCat.{u + 1} Λ]`, the published composite of exact degreewise open extension and proper right derived image. |
| E_u^c: proper mate followed by open base change | `rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat Λ) sq c`, definitionally the existing `rightDerivedLowerShriekOfCompactificationBaseChangeMap`. Its proper factor is `derivedBaseChangeMap`, the unit-square-counit mate; its final factor is the canonical open comparison. |
| PF_u^c: proper counit projection followed by open tensor and composition | `projectionMapOfCompactification (ModuleCat Λ) c`, definitionally `projectionMapOfCompactification (ModuleCat Λ) c`. The definition is proper projection followed by the inverse open projection isomorphism and `leftDerivedUpperStarCompactificationIso`. |
| E after v*PF | The first two factors on the left side of the displayed Lean equality. |
| Canonical target tensor and pullback-composition comparisons | The next two factors on the left: `Rf_!(c.ofIsPullback sq).map` of `leftDerivedUpperStarTensorComparison ... w`, then of tensor with `(leftDerivedUpperStarSquareIso ... sq.toCommSq).inv.app P`. |
| PF for the base change after E tensor identity | The final two factors on the right: `derivedTensor.map (E.app N)` at `v*P`, then `projectionMapOfCompactification ... (c.ofIsPullback sq)` at `w*N,v*P`. Mapping the first variable of the curried tensor fixes the second, so it is E tensor identity. |
| Canonical source tensor comparison | The first factor on the right is `leftDerivedUpperStarTensorComparison ... v` at `F_u^c N,P`. |
| Naturality in N,P | Each side is a composite of components of the published natural transformations/bifunctors and their natural comparison maps. The equality is stated for every N,P, hence identifies these two natural families. It does not merely assert equality for chosen objects. |
| No invertibility conclusion | The conclusion is equality of the two actual composites; it contains neither `IsIso` nor any invertibility hypothesis on exchange or projection. |

### Coefficient presentation and dependency declarations

The node explicitly identifies its finite maps with the formulas of `def-exchange-projection`.
That recorded interface already uses fixed-scalar `ModuleCat`-valued sheaves. This statement
uses exactly its finite maps and their domains, not a replacement operation. For finite discrete
coefficients this is the canonical presentation of modules over the constant ring sheaf:
`finiteCoefficientRealization` keeps the module presheaf and sheafifies along the scalar unit,
and `finiteCoefficientRealization_isEquivalence_ring` states it is an exact equivalence.
The module-object/constant-ring presentation is also related by the published
`finiteCoefficientIntrinsicRealization_exact` and `sfIntrinsicModuleEquivalence`.
These are canonical scalar-section realizations, not freely chosen category identifications.
A finite coefficient ring can be placed in `Type (u+1)` without restriction, and the site's
object and morphism universes remain those of the published `Scheme.ProEt.topology`.

Read and imported statement dependencies:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`, `AlgebraicGeometry.ChosenCartesianSquare`;
  actual finite map arguments use Mathlib `IsPullback` as the recorded exchange interface does.
- `WeilConjectures.Compactification.Refinement`, `AlgebraicGeometry.Compactification.Refinement`,
  and its underlying `Compactification`/`Compactification.ofIsPullback` construction.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`, `ProEtale.FiniteCoefficientModules`,
  `FiniteCoefficientDerivedCategory`, `finiteCoefficientRealization` and its equivalence theorem.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`,
  `Scheme.proEtaleConstantRingDerivedPullback`, and its exact pullback, direct image and
  tensor-unit-normalized adjunction; their fixed-scalar forms are the ones already used by
  `finiteExchangeProjection`.
- `Sheaf.SixFunctors.IntrinsicDerivedTensor`, `Scheme.proEtaleDerivedTensor`, the intrinsic
  K-flat tensor; the fixed-scalar derived tensor in `finiteExchangeProjection` is the same
  sheaf tensor construction in that interface's presentation.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`,
  `Scheme.sfIntrinsicExtensionByZero`: its definition literally transports the fixed-scalar
  `ProEtale.openImmersionLowerShriek` used here through the canonical realization equivalences.
- `Sheaf.Paper.ExchangeProjection`, `ProEtale.finiteExchangeProjection`, read in full: its
  second and third components are literally the two upstream canonical maps used here.
  Their owning modules are imported directly: `WeilConjectures.SixFunctors.ProEtale.
  FiniteCoefficient.Derived.LowerShriekBaseChange` and `.LowerShriekProjection`.
  All published exchange/projection declarations and public imports remain intact.
- `def-weil-scheme-morphism-properties` is the recorded convention collecting Mathlib's
  `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, `IsProper`, `IsOpenImmersion`.

The already stated proof-dependency modules are imported privately:
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`,
`Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition`,
`Sheaf.Paper.RingedExchangeTensorCoherence`, and `Sheaf.Paper.ProjectionMateExact`.
The dependency `lem-sf-open-tensor-normalization` has no Lean record and is cited in the proof
docstring; it is a proof dependency only, and its absence is no obstacle to stating this node.
The theorem docstring contains all five node proof steps, including the open restriction
calculation on K-flat representatives and the final two naturality substitutions.

### Sources, searches, and edge cases

Read the current main-20261015 blueprint final base-change sentence and Stacks
`sites-cohomology.tex`, `remark-compatible-with-diagram` (Tag 0E48) and
`lemma-j-shriek-and-tensor` (Tag 0GL1). No correction is needed: these are maps on arbitrary
unbounded objects, with no assertion that either structural transformation is invertible.

Searches run with msearch.py:

- LeanFinder: "Compact support projection formula commutes with arbitrary base change exchange
  on derived sheaves". Eight hits on generic sheaf-module pullback, composition and restriction
  maps; none states the compact-support coherence identity.
- LeanSearch: the same query. Eight hits on tensor/base-change algebra, generic morphism-property
  stability and sheaf restriction; none states this identity.
- Loogle: `CategoryTheory.Adjunction.rightAdjointProjectionMap`. No hit; identifier unknown
  in the external index (the project definition itself is present in the imported source).
- Mathlib grep through msearch.py: `projectionMapOfCompactification|LowerShriek.*[Bb]ase[Cc]hange`
  in AlgebraicGeometry: no hits.
- `rg` in upstream WeilConjectures and side `lean/Sheaf` for projection/exchange coherence,
  the item id, and `projectionMapOfCompactification_baseChange`: the etale theorem
  `AlgebraicGeometry.Etale.projectionMapOfCompactification_baseChange'` has the analogous
  formula on a different site; `Sheaf.AlgebraicGeometry.CompactProjectionExchange` is also
  etale. Neither is this pro-etale statement. `finiteExchangeProjection` supplies the
  required arrows but does not assert their coherence. No existing pro-etale theorem matches.
- Read the current server sources of the FiniteCoefficient derived projection, compact-support
  base-change and tensor-pullback modules with the prescribed `scompile.py --source` interface.
  They supply the same published declarations with corrected module paths.

Edge cases checked before writing: empty schemes are allowed; the zero coefficient ring is
allowed (`CommRing` without `Nontrivial`); N or P may be zero; v may be the identity, any open
immersion, or arbitrary nonseparated morphism. For j the identity the equality is the ordinary
proper exchange/tensor square, and for p the identity it is the open tensor/base-change square.
The source imposes no field, characteristic, or invertibility condition. There is no lower
cohomological bound. Both identity and nonidentity base changes are retained.
No `STATEMENT-DISPUTED` issue was found.

## Repair of return L (immutable head bea30ba9323f)

The retained packet's initial dry run passed at 487a8c4776, but the return identifies a
real import-interface regression. This repair removes the sandbox replacement of
`Sheaf.Paper.ExchangeProjection` and the sandbox dependency-node override for
`def-exchange-projection`. The published module and its entire public import block
are preserved unchanged. The theorem now spells out the upstream
`projectionMapOfCompactification` and
`rightDerivedLowerShriekOfCompactificationBaseChangeMap` directly. These are exactly
the third and second components of `finiteExchangeProjection`, whose body was read;
no map is reconstructed or copied, and no mathematical hypothesis or clause changes.
The current FiniteCoefficient owning modules are used because mixing the retired
and current copies produces duplicate declarations. Restoring the historical import
block was tested through scompile.py and reproduced the duplicate
`upperStarIsoLowerStarInv`; combining the old projection module with the new one also
reproduced duplicate `rightDerivedLowerShriekOfCompactification`.

Every named consumer retains its import environment because this delivery no longer
changes ExchangeProjection: `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`
retains its access to `projectionMapOfCompactification`;
`Sheaf.Paper.CohomologicalSmoothness` and
`Sheaf.Paper.CompactSupportCoefficientChange` retain access to
`rightDerivedLowerShriekOfCompactificationBaseChangeMap`; and
`Sheaf.Paper.EtaleCompactSupportCoefficientChange` retains access to
`rightDerivedLowerShriekOfCompactificationPlus`. No consumer edit is needed. This is
removal of the returned interface delta, not an unchanged re-push.

The report's clause table uses the underlying canonical maps; all prior hypotheses,
comparisons, edge cases, sources, and search results still apply. No statement
correction or new node is introduced. The delivered file has explicit universes and
`autoImplicit false`; its only sorry is the named theorem, with the five-step proof
in its docstring. The node's lean.statement is the verbatim final signature. The
post-repair file compilation and fresh server preflight are recorded below.

Post-repair validation: scompile.py compiled the sole delivered file cleanly in
sandbox mode (6.9 seconds) and library mode (8.0 seconds), with no warnings.
The fresh deliver2.py --no-push passed the server preflight and compilation at
d9e1e340fc. Its staged set contains only this report, the item node, and the item
module: no dependency override and no import-pruning delta remain. The final push
runs the same checks again against the current base.

## Second reading by Q22

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
