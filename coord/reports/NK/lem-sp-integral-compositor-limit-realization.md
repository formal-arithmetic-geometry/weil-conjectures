## Worker report

The module `Sheaf.Paper.IntegralCompositorLimitRealization` states
`AlgebraicGeometry.ProEtale.IntegralCompositorLimit.integralCompositorLimitRealization`.
It supplies explicit natural composition isomorphisms and states their reduction,
adjunction and uniqueness laws. Its only postponed theorem is this named theorem;
its docstring follows all six proof steps. No node statement is corrected and no
dependency record or new node is needed.

Hypothesis and clause correspondence:

- The global finite field and its algebraic closure are `D : FiniteFieldDatum.{u}`;
  their characteristic is `D.p`, with the primality and closure structures already
  in that datum. The coefficient is `l` with `[Fact l.Prime]` and `_hl : l ≠ D.p`.
  `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]` and
  `[FiniteDimensional (Padic l) E]` express every finite coefficient extension.
  No nontrivial-extension hypothesis excludes `E = Padic l`.
- `X`, `Y`, `Z` have their `Over (Spec (.of D.k))` instances. On each structure
  morphism, `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact` express exactly
  separated finite type. `f.IsOver` and `g.IsOver` express morphisms over k.
  `d e : ℕ` and `SmoothOfRelativeDimension d f`, `SmoothOfRelativeDimension e g`
  express smoothness and pure nonnegative relative dimensions.
- Integral categories are exactly `sfIntegralConstructibleCategory l E T`, on
  `scalarReductionSource`, hence the completed coefficient sheaf, not the
  discrete constant ring. Normalized categories are exactly
  `spNormalizedConstructibleTorTowerCategory l E T (q.abelian T)`, on the
  ordinary derived category of strict varying-coefficient systems, including
  uniform cohomological/Tor bounds. Levels n in the dependencies mean exponent n+1.
- `Space` packages the specified reduction/total-limit equivalence. Its
  `reduction` and `normalized` fields use `SpReductionTower` and
  `SpNormalizedEquivalence`. `reduction_eq` identifies the forward functor with
  `SpIntegralAdjunction.reduction`; `limit_eq` identifies the inverse with
  `SpIntegralAdjunction.limit`. Its `unit_eq` and `counit_eq` identify the actual
  adjunction maps. HEq only accommodates the endpoints identified by the preceding
  functor equalities; it supplies no substitute map or new mathematical condition.
- `TowerEdge.pair` is the recorded `TowerAdjointCompositor.Pair`. Its preservation
  field is the recorded `PreservesNormalized`. `towerLeft`, `towerRight` restrict
  these same functors by the existing full-subcategory lift, and `towerAdjunction`
  restricts their same adjunction. All maps remain actual derived tower morphisms.
- `IntegralEdge.closed` allows the recorded `SpIntegralAdjunction.support` on the
  exact integral category. Its comparison is the specified isomorphism from that
  independently constructed completed-ring compactification composite to
  `realize S.equivalence T.equivalence (towerLeft ...)`. The right functor is
  literally `realize T.equivalence S.equivalence (towerRight ...)`, the specified
  L H red realization. `IntegralEdge.hom_eq` identifies its given integral
  adjunction with the full-faithfulness Hom chain from the dependency, so its
  units/counits are fixed as well. These fields package the comparisons that the
  node explicitly supposes given; their existence is not a new conclusion here.
- `alpha` and `theta` are the given natural isomorphisms on the normalized full
  categories; the given counit normalization is `_towerCounit`. These are exactly
  the actual tower compositor data supplied by
  `lem-sp-tower-adjoint-compositor-realization`, restricted to N. No finite-level
  faithfulness is assumed.
- `realizationComposition` is the middle-kappa isomorphism. `leftCompositor`
  composes the two specified integral comparisons, this isomorphism, L alpha red,
  and the inverse gf comparison. Thus it is exactly the first displayed
  expression through the specified comparisons.
- `rightCompositor` is L theta red followed by the inverse middle-kappa
  isomorphism, exactly the second displayed expression. Both constructions are
  natural isomorphisms with explicit data, without any existential choice.
- `Laws.left_reduction` says red(alpha-integral) followed by b_gf equals
  b_g followed by F_g(b_f) followed by alpha on red(M).
  `Laws.right_reduction` says red(theta-integral) followed by c_f and H_f(c_g)
  equals c_gf followed by theta on red(K). These are the exact two reductions,
  including every intermediate equivalence map. Essential surjectivity of the
  equivalences extends this description to all normalized towers.
- `Laws.counit` is the integral adjunction comparison equation.
  `Laws.unique` gives uniqueness even among natural transformations, hence among
  natural isomorphisms. `Laws.composite_counit` is exactly epsilon_g after
  F_g(epsilon_f H_g). Units and counits are those specified by the Hom chains
  (`hom_eq`), with the equivalence units and counits fixed by `Space`.
- The last clause follows by instantiating the theorem at `E = Padic l`, whose
  algebra and degree-one finite-dimensional instances meet the same binders.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` reexports the recorded
  ring of integers, uniformizer and finite quotient coefficient constructions;
  its `Padic.finite_coefficientExtensionRing` supplies their finiteness interface.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  the standing separated finite-type setting and `CondensedRing.compactificationOverField`.
  Compactifications `cf`, `cg`, `ch` are the specified choices used by the actual
  compact-support functors; the statement is valid for every such choice.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`:
  `AlgebraicGeometry.SmoothOfRelativeDimension` (and its smoothness convention).
- `Sheaf.Paper.SfIntegralConstructible`: `WeilConjectures.sfIntegralConstructible`,
  `WeilConjectures.sfIntegralConstructibleCategory`.
- `Sheaf.Paper.SmoothPurityCoefficientTowers` and
  `Sheaf.Paper.SmoothPurityNormalizedTowers`, publicly reexported by the
  normalized-equivalence dependency: the recorded strict coefficient and
  normalized constructible tower categories and `IsSpNormalizedTower`.
- `Sheaf.Paper.SmoothPurityNormalizedEquivalence`: `SpNormalizedEquivalence`,
  its `adjunction`, restriction, and the completed reduction/limit functors.
- `Sheaf.Paper.IntegralDirectImageTower`: completed compact-support and
  reduction/total-limit comparisons; the section-model support is the published
  `SpIntegralAdjunction.support` reexported by the adjunction dependency.
- `Sheaf.Paper.IntegralAdjunctionBijection`: `SpIntegralAdjunction.Realization`,
  `homChain`, and the reexported `support`, `reduction`, `limit` constructions.
  The present `IntegralEdge.hom_eq` uses exactly that Hom-chain normalization
  without assuming the dependency's separate smooth-purity conclusion.
- `Sheaf.Paper.TowerAdjointCompositorRealization`:
  `TowerAdjointCompositor.Pair`, `left`, `PreservesNormalized`, and the actual
  adjunction/compositor convention of `towerAdjointCompositorRealization`.
- Proof dependencies already in Mathlib: `Adjunction.restrictFullyFaithful`
  and its unit/counit formulas (`Mathlib.CategoryTheory.Adjunction.Restrict`),
  `Adjunction.comp` and `comp_counit_app` (`Adjunction.Basic`), and
  `Adjunction.rightAdjointUniq` with its counit normalization (`Adjunction.Unique`).

Edge cases checked before drafting: identities f or g, d=e=0, empty schemes,
zero derived objects, equivalence counit equal to the identity, and the degree-one
coefficient extension. No cancellation by a dimension, no nonemptiness of a scheme,
no inversion of ell, and no assumption that separate finite evaluations are faithful
occurs. Small pro-etale site sizes and the coefficient sizes are inherited unchanged
from the recorded dependency categories. The categorical helper universes and Hom
universes are bound independently and explicitly.

Searches performed with the required launcher msearch wrapper:

- LeanFinder: “Transport composition isomorphisms of adjoint functors through
  reduction and total derived inverse limit equivalences”. Eight hits, including
  `Adjunction.derived` and `derivedε_fac_app`; none states the integral normalized
  tower realization and both reduction/compositor identities.
- Loogle: “CategoryTheory.Adjunction.restrictFullyFaithful,
  CategoryTheory.Adjunction.rightAdjointUniq”. Zero combined-query hits; the
  recorded individual declarations were opened in Mathlib and reused.
- Grep of Mathlib, CategoryTheory/Adjunction: “compositor|restrictFullyFaithful”.
  Five hits, all the generic restriction API, reused here.
- LeanSearch: “Composition isomorphisms of adjoint functors transported through an
  equivalence preserve the counit and reduce to the original comparison”. Eight
  hits, including `Adjunction.leftAdjointCompIso`, `Equivalence.trans_toAdjunction`
  and the generic equivalence unit/counit API. None is this concrete theorem.
- Direct rg in `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json`: item id, `IntegralCompositorLimit`,
  `integralCompositorLimitRealization`, `realizationComposition`, and variants
  of integral compositor/limit. No existing declaration states this node.
  Related compact-support system and other integral compositor declarations concern
  different coefficient/system frameworks. The exact tower dependency and integral
  adjunction dependency were opened and reused rather than restated.

No STATEMENT-DISPUTED flag or source correction is needed.

## Second reading by NK

A separate manual pass compared the node, current blueprint proof (1)--(3), and
all definitions above. The dispatcher prohibits starting another agent; this is
not represented as an independent-agent review. The maintainer's independent
review reads this delivery, as specified by the worker brief.

The pass checked both arrow directions (kappa for compact support, inverse kappa
for exceptional image), the reversal of functor-composition notation, the exact
completed integral category, and that uniqueness fixes the supplied left comparison.
It also checked that integral adjunction normalization is data of the input rather
than an arbitrary right-adjoint choice. No mathematical node change was made.
Compilation and delivery-gate results are recorded below when available.

Validation: `scompile.py NK lem-sp-integral-compositor-limit-realization` compiled
both sandbox and library presentations cleanly against live server dependencies;
the delivered library module took 14.0 seconds. No errors or warnings were printed.
