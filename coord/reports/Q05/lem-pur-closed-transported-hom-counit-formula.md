## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedTransportedHomCounitFormula` states
`AlgebraicGeometry.ProEtale.closed_transported_hom_counit_formula` with a single
`sorry`. The node's statement, dependencies, proof and other fields are unchanged;
only its `lean` record is added. There are no new nodes or dependency repairs.

The named helpers construct the actual maps used by the statement, rather than
postulating comparison isomorphisms. They belong to this node and are listed in
`lean.declarations`. `closedTransportDirectImage` is termwise closed direct image,
with its finite-colimit instance supplied by the existing complementary-open
exactness theorem. `closedTransportDirectImageIso` is the existing unique derived
comparison. The etale and pro-etale normalizations remove identity extension by
zero using the published identity isomorphisms and then this exact-derived
comparison. `closedTransportComparison` descends the canonical underived
`lowerStarComparisonUpperStarBaseChange`, with the canonical composition
isomorphisms. It is not chosen from an existence theorem.

`closedTransportEtaleRight` is the existing ordinary etale compact-support right
adjoint at `Compactification.ofIsProper i`. `closedTransportEtaleAdjunction`
transports its left functor through the canonical etale normalization and retains
this same right adjoint. `closedTransportEtaleValue` is G composed with U_X.
`closedTransportExceptional` uses the dependency's `sfFiniteExceptionalAt`, with
the existing Brown theorem supplying its left-adjoint instance. The explicit Hom
map and counit use these actual adjunctions and the actual comparison isomorphism.
All definitions have real bodies; none contains a postponed proof.

Hypotheses and clauses, in order:

| Node text | Lean rendering |
| --- | --- |
| Fixed global field and finite coefficient datum, A = A_(E,n) | `P : PurityFiniteSetting.{u}`, with `P.field.k` and `P.Coefficient`; positive level, ell distinct from p, the finite coefficient extension and its fixed closure are fields of this existing setting. |
| Separated finite-type k-schemes Z and X | Their `Over (Spec (CommRingCat.of P.field.k))` instances, and `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` on each structure morphism. |
| Closed k-immersion i | `i : Z ⟶ X`, `[IsClosedImmersion i]`, and `[i.IsOver (Spec (CommRingCat.of P.field.k))]`. |
| Quasi-compact complementary open j | `j : U ⟶ X`, `[IsOpenImmersion j]`, `[QuasiCompact j]`, and `hij : IsCompl (Set.range i.base) (Set.range j.base)`. |
| Ordinary constant-A module derived categories on the two small sites | `DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u+1} P.Coefficient))` and the analogous categories using `Scheme.ProEt.topology`; these are the fixed-module-sheaf presentation used by all recorded canonical comparison interfaces. |
| S_T, U_T and their specified counit | `comparisonUpperStar ... T` with `.mapDerivedCategory`, `comparisonLowerStar ... T` with `.rightDerivedFunctor`, and `derivedComparisonAdjunction ... T`. |
| F, ordinary etale G and counit epsilon^G | Exact etale `lowerStar.mapDerivedCategory`; `closedTransportEtaleRight` and `closedTransportEtaleAdjunction`, using the same compact-support adjoint after `closedTransportEtaleNormalization`. |
| Exact pro-etale direct image and its total unbounded right derived identification | First conjunct gives finite limits and colimits; second gives invertibility of the actual right-derived comparison on every complex. `closedTransportDirectImageIso` gives the normalized natural isomorphism to the termwise descent P. |
| Canonical natural isomorphism lambda_H | `closedTransportComparison ...`, a natural isomorphism of the exact functors, restricted to bounded-below H in the theorem. It descends the specified underived comparison mate, so uses the canonical direct-image comparison. |
| Compact-support comparison at the identity witness is lambda inverse under identity extension | Third conjunct: `compactSupportSiteComparison.hom.app H` followed by S_X of the etale normalization equals the pro-etale normalization followed by `closedTransportComparison.inv.app H.obj`. Both sides have exactly the unnormalized pro-etale compact-support source and S_X F H target. |
| L in D+ and E_L = G U_X L in D+ | `closedTransportAllowedTarget ... L` is exactly the conjunction of these two `DerivedCategory.TStructure.t.plus` properties. |
| Transported exceptional value Ri! L = S_Z E_L | Fourth conjunct identifies the existing `sfFiniteExceptionalAt` value with the explicit composite. |
| Every bounded-below H and the four specified Hom arrows | Fifth conjunct is `Function.Bijective (closedTransportHomMap ... H L)`. This map first precomposes with `lambda.hom.app H`, applies comparison `homEquiv`, applies etale `homEquiv`, then applies `S_Z.map`. No replacement arbitrary equivalence is introduced. |
| Inverse image of identity is exactly the expanded transported counit | Sixth conjunct says, for every candidate t, that the Hom map sends t to the identity if and only if t equals `closedTransportCounit`. This is both existence (specialize t to that named map) and uniqueness of the inverse image. The named map is `lambda.inv ≫ S_X.map epsilon^G ≫ e_X`. |
| Naturality of the relative bijection | Seventh conjunct is the square for every source morphism `v : H' ⟶ H` and target morphism `u : L ⟶ L'`, with both H,H' bounded below and both targets allowed. |
| Naturality of the counit on the full allowed subcategory | Eighth conjunct is `P.map (S_Z.map (E.map u)) ≫ t_L' = t_L ≫ u` for every ambient morphism between allowed L,L'. |
| No assertion of an unbounded pro-etale exceptional adjunction | Bijectivity, identity inversion and the naturality equations retain the explicit lower-bound guards. Defining the composite and its component maps on ambient categories adds no adjunction assertion. |

Finiteness is not an extra premise: the main statement applies an instance lambda
to `Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing ... P.level_pos)`.
This supplies the already known finiteness of precisely P.Coefficient, without a
new instance definition or a hidden `let` in the statement. All universes and
variables are explicitly bound; `autoImplicit` is disabled.

Dependencies read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, its
  `Ring`, `Coefficient`, and coefficient ring instances.
- Mathlib `AlgebraicGeometry.Morphisms.ClosedImmersion`, `OpenImmersion`,
  `Morphisms.FiniteType`, `Morphisms.QuasiCompact`, `Morphisms.Proper`,
  `Morphisms.Separated`: the ordinary scheme-morphism predicates in the binders.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, namely the explicit etale
  derived module category used here; Mathlib `DerivedCategory.Plus` and the
  standard t-structure lower-bound property.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: its fixed-coefficient
  realization presents modules over the node's continuous-function ring sheaf.
  The statement uses the ordinary fixed-ring presentation, as the node requests
  and its recorded comparison/compact-support interfaces already do.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `AlgebraicGeometry.Scheme.proEtaleSiteComparisonModules`, the canonical
  `comparisonAdjunction` of the existing module-valued inverse/direct image.
- `Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed`:
  `siteComparisonDerivedPullbackPlus`, precisely the D+ restriction of the same
  `comparisonUpperStar.mapDerivedCategory` used in the formula.
- `Sheaf.AlgebraicGeometry.ClosedUnboundedCompactSupportNormalization`:
  `AlgebraicGeometry.Etale.closed_unbounded_compactSupport_normalization`;
  the canonical maps in its conclusion are used as the normalization data.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`, through
  `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`: `sfFiniteExceptionalAt`.
  Only its finite-level declaration is relevant; the integral/rational System
  is not a new assumption in this finite statement.
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`: `directImageComparison`;
  the canonical direct-image mate supplies the comparison on bounded-below objects.
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`:
  `compactSupportSiteComparison`; its identity-witness component is the exact map
  compared in the third conjunct.
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`:
  `isIso_compactSupportComparisonUnit`; this is the full faithfulness used in the
  final Hom factor. The already published unbounded comparison adjunction is
  `AlgebraicGeometry.ProEtale.derivedComparisonAdjunction`.
- Existing exactness and derived comparison infrastructure:
  `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.ClosedImmersion`,
  `preservesFiniteColimits_lowerStar_of_isCompl`; `Functor.mapDerivedCategory`,
  `mapDerivedCategoryNatIso`, `mapDerivedCategoryCompIso`,
  `rightDerivedFunctorIsoMapDerivedCategory`; etale identity extension
  `mapDerivedCategoryOpenImmersionLowerShriekId`; pro-etale identity extension
  `openImmersionLowerShriekIdIso`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, supplies actual coefficient finiteness.
  The other stated proof dependencies are imported where available; the two
  newly split coefficient Hom-presentation/identity-open lemmas have no Lean
  record and are described by name in the complete proof docstring.

Edge cases checked against the actual maps and domains:

- Z empty: all source-supported objects are zero; no positive dimension or
  nonempty-scheme condition is added. The proof's dimension bound may be zero.
- i identity: the complement is empty, its open immersion is quasi-compact,
  and identity extension is removed by the named identity comparisons.
- Zero H or zero L: the maps are defined and identity inversion is meaningful
  even when the identity morphism is zero.
- Arbitrary positive coefficient level, including level one: only the original
  `P.level_pos` is used; no divisibility or Kummer-level condition is introduced.
- Unbounded-above H and L are allowed when bounded below. No constructibility,
  finite Tor amplitude, etale-origin condition on L, or global exceptional
  adjunction is introduced.
- Universes: schemes are `Scheme.{u}`, module values and the coefficient lift
  have universe `u+1`, and the actual standard derived categories are used;
  no site-universe equality or new independently chosen derived category occurs.

Searches actually run with `msearch.py` for this item:

- LeanFinder: "Expanding the natural Hom bijections for a bounded below exceptional
  functor transported through fully faithful site pullback computes its counit".
  Eight hits, including `Functor.sheafAdjunctionCocontinuous_homEquiv_apply_val`,
  `Equivalence.sheafCongr.counitIso`, and dense-subsite counit results. None gives
  the closed exceptional finite transport and its specified comparison formula.
- Loogle: `"Adjunction", "homEquiv_counit"`. Three hits, including
  `CategoryTheory.Adjunction.homEquiv_counit` and its CoreHomEquivUnitCounit
  counterpart. These provide the elementary reversal formula, not this item.
- Mathlib grep: `transportedCounit|closedComparison|exceptional.*counit`.
  Zero hits.
- LeanSearch: "Counit formula for a right adjoint transported by etale proetale
  site comparison". Eight generic adjunction/comonad/Kan-extension hits,
  none the closed finite site transport statement.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for
  `closedTransport|transported_hom_counit|transportedHomCounit|closed_transport`,
  and for the node id: no existing declaration for this item. Broader searches
  found coefficient-transport counit interfaces and the already used fixed
  comparison, finite exceptional, and closed exactness modules; these concern
  different statements, not duplicate versions of this result.

The blueprint source was read at its recorded finite Hom chain: its final factor
is full faithfulness, not a second comparison adjunction. The resulting map here
has that exact last factor. The module's proof docstring expands all five DAG
proof steps, including exact-derived normalization, identity-open comparison,
relative Hom chain, reversal at identity, and naturality.

No statement correction or STATEMENT-DISPUTED issue was needed. The theorem
remains a stage-2 statement, not a claim of proof closure. Compiler and delivery
validation are performed by the prescribed wrappers only.

## Second reading by Q05

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
