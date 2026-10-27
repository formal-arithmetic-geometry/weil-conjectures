## Worker report

The delivery states `lem-pur-relative-compact-support-pasting` in
`Sheaf.Paper.RelativeCompactSupportPasting`. Its main declaration is
`AlgebraicGeometry.ProEtale.RelativeCompactSupport.towerPasting`; the complete
node is realized by the declarations listed in its Lean record. Its constant-ring
instances of the recorded `compactificationExchangeFromData` now belong to this
same item module. The live `def-exchange-projection` node and its entire Q14 Lean
record are retained byte-identically. No natural-language statement, dependency
list, proof, review record, or target changes. No new DAG node is needed.

The live item's Q94 review is a stage-1 split, not a Lean attachment: its `lean`
was absent. This delivery performs the assigned stage-2 work on that reviewed
split. There is no stage-1 re-splitting or duplicate stage-1 delivery.

### Objects and hypotheses, clause by clause

| Node clause | Lean rendering |
| --- | --- |
| Commutative ring B, allowing infinite B | `B : Type (u + 1)` and `[CommRing B]`; no `Finite B` in either pasting theorem or either triple-pasting theorem. The coefficient universe is the recorded strict-tower interface's universe. |
| Small pro-etale constant-B module derived categories | `StrictTower.coefficients B X`, `StrictTower.Modules B X`, and their actual `DerivedCategory`; `ordinaryG`, `ordinaryR`, `ordinaryJ` are aliases for the recorded module operations followed by exact descent or total right derivation. They introduce no substitute module category or coefficient action. |
| Strict towers and their ordinary unbounded derived categories | The existing `StrictTower.Derived B X = DerivedCategory (ℕᵒᵖ ⥤ Modules B X)`, with index n denoting positive level n+1. The statements use the actual existing `G`, `R`, `adj`, `J`, `gComp`. They do not form towers of separate derived categories. |
| Separated finite-type f and supplied compactification | `c₀ : Compactification f₀` and `[QuasiCompact c₀.i]`. The structure contains the open immersion, proper factor, and equality `f₀ = c₀.i ≫ c₀.g`. The compactification already implies separatedness and local finite type of f₀; quasi-compactness of its open factor gives quasi-compactness of f₀, hence finite type. Thus no geometric hypothesis is discarded. |
| Arbitrary a and b | `a : Y₁ ⟶ Y₀`, `b : Y₂ ⟶ Y₁`, with no isomorphism, flatness, finite-type, or etale-origin assumption. |
| Pullback compactifications and their induced maps | `c₁`, `c₂`, the maps `x₁`, `x₂`, `z₁`, `z₂`, and the upper and lower `IsPullback` squares `sj₁`, `sj₂`, `sp₁`, `sp₂`. These are Cartesian realizations of the specified pullbacks, not extra chosen transformation data. Fibre-product uniqueness is exactly the projection-preserving identification stipulated in the node. |
| Identify successive and composite base changes | `sp₂.paste_horiz sp₁` and `sj₂.paste_horiz sj₁` realize the outer Cartesian squares on the successive compactification. For literal pullbacks the identification is `pullbackLeftPullbackSndIso c.g a b`, whose two projection equations characterize it uniquely. The maps in the statement are expressed after this identification, so there is no arbitrary isomorphism parameter. |
| Specified E, the unit--square--counit mate | `StrictTower.exchange`, constructed by `mateEquiv (adj B p) (adj B p') (squareG ...).hom`. `ordinaryE` uses the actual derived module adjunction and exact descent of the existing `moduleSquareG`. |
| Specified open-unit-normalized beta | The existing `StrictTower.beta`; for the ordinary category, `ordinaryBeta` descends the existing `singleBetaInv`, which is the transpose of the pulled-back module open unit. `ordinaryBetaInv_isIso` states its arbitrary-ring invertibility so the definition can take its unique inverse. No mere existence choice of a comparison is used. |
| H = proper mate at J followed by proper pushforward of beta | `towerH` and `ordinaryH` are written out as these two transformations with the required functor associators. |
| E for a composite equals successive E | First conjunct of `towerPasting` and `ordinaryPasting`. `paste` uses Mathlib `TwoSquare.vComp` and inserts precisely `gComp B b a` and `gComp B z₂ z₁`, or their ordinary descents. |
| Beta for a composite equals successive beta | Second conjunct, with the compactification and open pullback compositors in the corresponding positions. |
| H for a composite equals successive H | Third conjunct, with the base and open pullback compositors. |
| Equalities are transformations before evaluation | All six pasting conclusions are equalities in functor-category hom types. No evaluation functor occurs in either pasting theorem. |
| Finite evaluation gives the ordinary maps | `finiteEvaluation [Finite B]` gives the E, beta, and H equations for every object and every n, including all `evalG`, `evalR`, `evalJ`, and composite `supportEval` comparison factors. These component equations express compatibility of those natural transformations, not only cohomology comparisons. |
| At B = A_(E,n), in the named finite domain, these are the chosen-compactification maps | `quotientDomainAgreement` uses the actual `Padic.coefficientExtensionRing l E (n + 1)` and the item-owned `quotientChosenExchange` instance of the recorded `compactificationExchangeFromData`. It explicitly binds the prime, finite extension, S, invertibility on every residue field of S, the three finite-type S-schemes, the two separated finite-type S-morphisms, their Cartesian square, and the chosen compactification. Its pulled-back compactification is exactly `c.ofIsPullback sq`. Positive levels n+1 cover every n ≥ 1. |
| Projection identifications for three maps and parenthesization | `towerTriplePasting` and `ordinaryTriplePasting`, each with three conjuncts for E, beta, H. Both actual nested pastes are displayed, with `eqToHom (congrArg ... (Category.assoc ...))` identifying associative composite scheme maps at the source and target. The pullback compositors are the recorded projection/section-normalized ones. |
| No etale origin, base-map isomorphisms, or equivariant compactification | None is a binder. In particular no hypothesis makes E invertible, and E is never inverted in the constructions. |

The Cartesian-realization formulation was checked by an actual compiler probe:
instantiate `towerPasting` and `ordinaryPasting` with `c`, `c.baseChange a`,
`(c.baseChange a).baseChange b`, the literal pullback projections, the two
`IsPullback.of_hasPullback` witnesses, and the two
`Compactification.isPullback_i_ofIsPullback` witnesses. Both complete applications
compile. Thus the item does not require the user to supply extra Cartesian
squares or compactifications beyond its own data. The probe also checked the
actual projection-preserving `pullbackLeftPullbackSndIso c.g a b`. The probe is
outside the delivered modules.

### Dependency declarations read and used

- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: the public general
  module operations and normalized `Scheme.proEtaleRingModuleAdjunction` from its
  public `ProEtaleOperationsCanonicalAdjunction` dependency. The recorded small-ring
  specialization is not silently substituted for the coefficient-sized interface.
- `Sheaf.AlgebraicGeometry.StrictConstantTowerOperations`:
  `StrictTower.coefficients`, `Modules`, `Derived`, `modulePullback`,
  `moduleDirectImage`, `moduleGComp`, `G`, `R`, `adj`, `gComp`, `ev`,
  `constantRingIso`, `constantRingIso_comp`, `evalG`, `evalR`, `evalR_isIso`.
- `WeilConjectures.Compactification.RefinementCategory`: the compactification
  notion and its refinement-category interface, reusing the same underlying
  `AlgebraicGeometry.Compactification`.
- `WeilConjectures.Compactification.BaseChange`: `Compactification.ofIsPullback`,
  `baseChange`, `isPullback_i_ofIsPullback`, and their projection equations.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` and
  `...Pullback.Pasting`: `pullback`, its projections and universal property, and
  `pullbackLeftPullbackSndIso`.
- `Sheaf.AlgebraicGeometry.StrictTowerOpenExtension`: `moduleJ`, `moduleJAdj`,
  `J`, `jAdj`, and `evalJ`.
- Mathlib `CategoryTheory.mateEquiv`, its unit/counit formula and
  `mateEquiv_vcomp`/`mateEquiv_hcomp`, as the dependency's `mathlib_match` records.
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`: the actual `beta`,
  `beta_comp`, and normalized proper/open calculus. Its public arrow module
  supplies `exchange`, `squareG`, `singleBetaInv`, and `singleBeta`.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.compactificationExchangeFromData`.
  This is the live dependency's existing constructor. The item module supplies
  its constant-ring inputs in `ConstantCompactificationExchange.sourceGComp`,
  `sourceSquare`, `finiteChosenExchange`, and `quotientChosenExchange`.
  `sourceGComp` uses the recorded K-flat/unit-normalized
  `Scheme.proEtaleCanonicalPullbackComposition`, transported along the existing
  `constantRingIso_comp`. `finiteChosenExchange` applies the recorded constructor
  to the actual normalized module adjunctions and `singleBeta`; the quotient
  helper specializes that construction to `Padic.coefficientExtensionRing`.
- Already-stated proof dependencies are imported privately:
  `StrictTowerPullbackSquarePasting.squareG_pasting_inv`,
  `CategoryTheory.Adjunction.coefficient_exchange_of_counit`,
  `CategoryTheory.tower_evaluation_isKInjective`,
  `WeilConjectures.integralTowerGeneralPullbackComposition`, and
  `Scheme.coefficientModulePullbackComposition_existsUnique`.
  The K-injective Hom and conjugate-unit Mathlib matches are available through
  their existing source modules. The module docstrings give the seven-step
  argument, with the proper, open, composite, evaluation, and associativity parts
  attached to the relevant theorem.

### Searches and edge cases

Actual `msearch.py` searches for this group/item:

- LeanFinder: `Horizontal pasting for compactification relative constant coefficient
  strict tower compact support exchange maps`. Eight hits on compactly supported
  continuous functions; none is the sheaf-theoretic statement.
- Loogle: `CategoryTheory.mateEquiv_hcomp`. One exact generic mate-law hit, already
  represented by a proof dependency, not the geometric/tower/evaluation result.
- Mathlib grep: `compact.*[Pp]asting|[Pp]asting.*compact|mateEquiv_hcomp`. Seven mate
  and bicategorical-mate hits; no compactification-relative strict-tower statement.
- LeanSearch: `Horizontal pasting of compactification relative base change maps for
  strict towers of sheaves`. Eight generic pullback-pasting and category-square
  hits; none states the result.
- Project `rg` searches by the exact node id and by
  `relativeCompactSupport`, `compactSupport.*[Pp]asting`,
  `constant.*tower.*pasting`, `compact.*support.*pasting`, and
  `relativeCompact.*Exchange`, in both `lean/WeilConjectures` and `lean/Sheaf`.
  No complete match. I read the generic
  `CompactSupportFormalism.pfBaseChange_paste_horiz` and
  `shriekBaseChange_paste_horiz` in
  `WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange`: they assume a
  supplied formalism and do not supply the actual strict-tower and finite
  evaluation clauses. I also searched the helper names before defining them.

The source is the local Stacks Tag 0E47 text in `sites-cohomology.tex`, read at
4093–4123. It states the proper exchange pasting and omits the verification;
the node's reviewed seven-step extension supplies the strict-tower/open/finite
normalization. The existing ordinary source compositor explicitly retains its
K-flat representative and ordinary-unit characterizations.

Checked edge cases: the zero ring, infinite B = Z, empty open/scheme, j = identity,
a or b equal to identity, a noninvertible base map, nonconstant towers, and towers
without a uniform lower cohomological bound. No type or premise excludes these.
The index 0 is positive coefficient level 1, and `quotientDomainAgreement` covers
all positive quotient levels. Finite B outside the quotient family, such as
F₂ × F₃, is covered by finite evaluation; it is not passed to the blueprint's
quotient-domain assertion. The extra `finiteChosenAgreement` theorem has been
removed. `quotientDomainAgreement` records agreement with the definition solely
on its named restricted domain. No statement dispute or correction remains.

All definitions have real data. The only newly postponed proofs are the named
`ordinaryBetaInv_isIso`, `towerPasting`, `ordinaryPasting`,
`quotientDomainAgreement`, `finiteEvaluation`,
`towerTriplePasting`, and `ordinaryTriplePasting`; every proof is exactly `sorry`
and each realizes a clause or needed construction of this same DAG statement.
The item-owned source and coefficient helper definitions contain no postponed proof.

## Repair of return H13

The returned head `9a8d7d628eb7` replaced the live Q14 primary declaration and
module of `def-exchange-projection` by a finite constant-ring special case. This
repair restores the dependency node copy from the current live source,
byte-for-byte, and delivers no change to that node. Its primary declaration
`CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`, module
`Sheaf.Paper.ExchangeProjectionSuppliedDomains`, signature, complete ten-name
declaration list, and every other Lean-record key remain unchanged. Thus its
existing higher-coefficient interfaces and all thirteen live consumers identified
by the reviewer (including Q49/Q08/NY/NK/Q25/Q22/Q24) retain their bindings; there
is no consumer adaptation to validate.

The separate `ExchangeProjectionRelativeConstant.lean` dependency module has been
removed from the packet. Its five actual constructions (`ordinaryG`, `sourceGComp`,
`sourceSquare`, `finiteChosenExchange`, `quotientChosenExchange`) are now item-owned
helpers inside `RelativeCompactSupportPasting.lean`, with this item's source and
blueprint docstrings and this item's `lean.declarations` entries. They apply the
recorded `compactificationExchangeFromData`; they do not redefine that constructor
or assert the full exchange/projection definition on a special case.

The extra `finiteChosenAgreement` theorem is removed. The remaining
`quotientDomainAgreement` keeps exactly the A_(E,n) restriction, prime and finite
coefficient extension, invertibility on S, finite-type S-schemes, separated
finite-type S-morphisms, and the Cartesian square. Finite evaluation for arbitrary
finite B remains its own clause, as the node requires. The pasting, evaluation,
three-map associativity statements, arbitrary-ring beta construction theorem,
and literal-base-change realizations are retained. No item statement correction
or dependency-record repair is needed.

### Validation

The initial saved two-module packet passed `deliver2.py --no-push`; that mechanical
pass did not resolve the independent review's H13 objection. The repair delivers
one module, compiled through `scompile.py` against the published library, followed
by a fresh `deliver2.py --no-push` and delivery. The earlier separate
literal-base-change probe compiled too. All variables
and universes are explicit, module mode is enabled, every declaration has its
source/blueprint docstring, lines are at most 100 characters, and no diagnostic
command is present in a delivered module. The prescribed wrapper performs the final preflight, per-file compile and push.

## Second reading by N8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
