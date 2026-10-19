## Worker report

The module `Sheaf.Paper.GlobalTransportChartNormalization` states
`AlgebraicGeometry.ProEtale.CompactSupportTransport.globalTransportChartNormalization`.
All theorem proofs are `sorry`; all definitions contain actual canonical data.
The earlier sandbox was retained and inspected. It had no node copy or report, so
there was no delivery to dry-run at entry. Its unconstrained functor parameters,
reversed functor compositions, unbound corner functors and final `True` chart
placeholder have been replaced in the same module.

Hypotheses and clauses, read against the current node:

* Finite commutative coefficients are `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  Every scheme is `Scheme.{u}`. Both coefficient categories are the actual
  `Sheaf … (ModuleCat.{u + 1} Λ)` categories, and every derived functor is on
  `DerivedCategory.Plus`, with no constructibility restriction.
* A Cartesian square is `sq : IsPullback g' f' f g`. The theorem quantifies over
  every such square and has `[IsSeparated f] [LocallyOfFiniteType f]
  [QuasiCompact f]`, exactly separated finite type. There is no condition on `g`.
* `E : Etale.LocalCompactSupportExtension Λ` is arbitrary simultaneous extension
  data, not an inhabitant chosen from its existence theorem. Its `H`, `exchange`,
  `comparison` and `restriction` are precisely H, E, q and r of the node. Their
  normalizations and restriction laws are fields of that recorded structure.
* `A`, `B`, `l`, `p` abbreviate canonical inverse image, right derived comparison
  direct image, and the two exact degreewise inverse images. `a` derives the
  inverse of `comparisonUpperStarCompUpperStarIso` using the exact-functor
  composition comparisons. Thus no arbitrary pullback comparison is assumed.
* `compactSupportComparisonUnit` is `asIso` of the actual derived adjunction unit.
  The dependency interface below makes its fixed-coefficient presentation usable.
  `F H = B X ⋙ H ⋙ A Y` is defined on the whole D+ category, so restricts to the
  full subcategory of etale-origin objects in the node without adding a choice.
* `C H` is the right whiskering of that unit by `H ⋙ A Y`. Its component is
  `A_Y.map (H.map (eta.app L))`, with exactly the endpoints C_f of the node.
  `S g d` and `T g' d'` are natural isomorphisms: their factors are respectively
  `a_g` then `p_g(C_f)`, and `C_f'` then `F_f'(a_g')`. Their types certify all
  asserted invertibility and naturality of the endpoint comparisons.
* `phi d d' E = S.inv ≫ whiskerRight E A_Y' ≫ T.hom`; in conventional functional
  order this is T A(E) S^{-1}. `globalPhi` specializes it to the supplied global
  exchange. Its `NatTrans` type includes naturality for every morphism of L.
  No inverse of the exchange occurs, and no claim says globalPhi is invertible.
* `He c` and `Hp c` are the recorded etale and pro-etale `Rp_* j_!` functors.
  `b` is `asIso` of `rightDerivedFunctorPlusBaseChange
  (lowerStarComparisonUpperStarBaseChange …)`, exactly the normalized counit mate.
  `e` is the degreewise exact-functor image of the recorded open comparison.
  `Cc` is first b_p at j_!L, then Rp_* of e_j. It never uses the upstream
  arbitrary-Nonempty-choice compact-support comparison.
* `chartPhi` is the same S^{-1}, A(E^c), T construction, with
  `Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap Λ sq c`.
  The chart is arbitrary; `c.ofIsPullback sq` is its specified pullback. `hc`
  and `hc'` supply the quasi-compact open parts required by the existing
  comparison interface; hc' is automatic by base-change stability from hc.
* `D` is `C_f.symm`, then A(q_c), then C_c. `J` is F_f'(a_g')^{-1}, then
  D_c' at l_g'L, then Hp_c'(a_g'). The first theorem conjunct is the equality
  `p_g(D_c)^{-1} ≫ globalPhi ≫ J = chartPhi` of natural transformations, exactly
  the displayed node equation, with Lean's left-to-right composition convention.
* The second conjunct identifies globalPhi for any open base map with
  `restriction`, a natural isomorphism explicitly built from r, a and C.
  The third is horizontal localization/pasting when either base map is open.
  `pastedPhi` writes all endpoint identifications: pComp, the first transported
  exchange, the intermediate inverse a inside F, the second transported
  exchange at the etale representative, then a and inverse pComp on the target.
  For an open V in Y, the two factorizations of the restricted square give the
  same composite pullback. This equation says exactly that restricting Phi and
  applying the source and target restriction endpoints gives Phi^V. The first
  conjunct applied to this square then gives its chart equation with those
  endpoints inserted. This is an equation of specified transformations.
* With both base maps open, the third conjunct is the iterated-restriction law:
  the endpoints constructed in two stages equal the one for their composite.
  The fourth conjunct states identity restriction using the canonical pId
  identifications. Open immersions are never assumed quasi-compact. The local
  extension's existing exchange_localization and restriction_identity fields
  supply precisely these laws; the theorem docstring spells out the conversion.

Dependency declarations read and used:

* `WeilConjectures.Compactification.BaseChange`: `Compactification.ofIsPullback`,
  `isPullback_i_ofIsPullback`, `isPullback_g_ofIsPullback`; the square and c' data.
* `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `Etale.DerivedCategoryModule`, `DerivedCategory.Plus`; the actual module D+.
* `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: the coefficient realization
  and fixed-ring presentation, exposed through the comparison dependency.
  Fixed-ring module sheaves are the canonical presentation of the constant
  ring-sheaf modules, not a change to the coefficient category's mathematics.
* `Sheaf.Paper.EtaleLocalCompactSupportExtension`:
  `Etale.LocalCompactSupportExtension` with all its fields, read in full.
* `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived`:
  `finiteCoefficientDerivedComparisonAdjunction`, `siteComparison_boundedBelow`;
  reexported and supplemented as described below.
* `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`:
  `supportSiteComparisonCoefficientPullbackIso`,
  `supportSiteComparison_pullback_coherent`. These record the coherent canonical
  inverse-image mate. Its fixed-ring upstream presentation is
  `comparisonUpperStarCompUpperStarIso`, derived degreewise here.
* `Sheaf.AlgebraicGeometry.ComparisonDirectImage`:
  `isIso_comparisonDirectImagePlus`, applied to the canonical derived mate.
* `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange`:
  `comparison_derivedBaseChangeMap` and its source/target comparison definitions;
  these specify the direct-image normalization (proof import).
* `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`:
  `openImmersionLowerShriekComparisonUpperStarIso`,
  `openImmersionLowerShriekComparison_coherence`.
* `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `preservesFiniteLimits_openImmersionLowerShriek`; exactness used by the
  degreewise derived construction.
* `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`:
  `proEtale_extension_by_zero`; pro-etale exact extension and degreewise action.
* `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange`:
  `rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`.
* `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: the recorded
  pro-etale operations module (proof import); the fixed-ring presentation used
  here is the actual canonical exact `ProEtale.upperStar`.
* Mathlib `AlgebraicGeometry.IsSeparated.instQuasiSeparated` is the recorded
  separated-to-quasi-separated proof dependency, already transitively imported.

Edge cases: zero coefficient ring and zero complexes require no nontriviality
assumption. Empty schemes and empty opens are allowed. Identity maps use pId;
two successive opens use pComp and the restriction cocycle. The proper-map chart
j=id uses its actual comparison e_id. Arbitrary noninvertible exchanges are
allowed: only specified endpoint isomorphisms are inverted. No global
compactification, quasi-compact base or quasi-compact open restriction is chosen.

Searches actually run with msearch.py under Q81 and this item:

* leanfinder: `global compact support transport chart normalization conjugation
  natural transformation etale proetale`; 8 hits, all unrelated scheme
  normalization/etale declarations, no matching statement.
* loogle: `CategoryTheory.isoWhiskerLeft,CategoryTheory.isoWhiskerRight`;
  0 hits with unknown identifier CategoryTheory.isoWhiskerLeft. The actual
  namespace `CategoryTheory.Functor` was then read from ExactFunctor source.
* grep: `globalTransport|ChartNormalization|comparisonUpperStar` in Mathlib
  CategoryTheory; 0 hits.
* rg in the source library and lean/Sheaf for globalTransport/chart normalization,
  and rg for the exact node id in the source library: no matching declaration.
  Broader transport/chart searches found unrelated commutative algebra modules.
  The existing compact-support comparison was read; it chooses an unspecified
  proper comparison and has no global-to-chart or restriction equality, so is
  not this statement and is deliberately not used.

No new nodes or source-based statement correction are needed. The current node's
statement and all non-lean metadata are unchanged. No STATEMENT-DISPUTED issue.

## Dependency modules

`thm-weil-pbc-site-comparison` gains the module
`Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`. Its recorded unit is in
the continuous-function coefficient realization, whereas the published
compactification and canonical comparison maps use fixed-ring module sheaves.
The new module reexports the entire recorded statement and adds the canonical
fixed-ring bounded-below unit's invertibility, with its resolution proof plan.
The unit is `derivedComparisonAdjunctionPlus … .unit`; the isomorphism is `asIso`
of exactly it. Its inverse is uniquely determined. This is a section 1(B)
interface repair for the same full D+ comparison theorem, not an extra assumption
on the transport statement. Only the dependency's lean record changes.

## Second reading by Q81

A separate reading pass checked the current node against the module, including
the dependency module. This was performed by the same dispatched worker;
independent mathematical review is the maintainer's subsequent delivery review,
as specified in the dispatch brief. No independent review is claimed here.

The earlier file's `True` conclusion and arbitrary functors failed the clause
check and were removed. Composition order was rechecked: F=B_X H_f A_Y,
C_f=A_Y H_f(eta), Phi=S^{-1} A(E) T in Lean order,
D=C_f^{-1} A(q) C_c, and J=F'(a)^{-1} D' Hp'(a). The chart equality therefore
has exactly p(D)^{-1}, Phi, J on its left. Its right side uses the actual E^c.
The restriction clauses include identity and both orders of localization, so
allow empty and non-quasi-compact opens and retain iterated restriction. Each
definition was inspected for arbitrary choice and sorry data; only the two
named theorem proofs are postponed. The complete eight-step proof is in the
main theorem's docstring, and the dependency has its resolution proof docstring.
