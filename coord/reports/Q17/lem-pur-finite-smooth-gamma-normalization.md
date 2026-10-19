## Worker report

The delivery states `AlgebraicGeometry.Etale.finite_smooth_gamma_normalization` in
`Sheaf.Paper.FiniteSmoothGammaNormalization`. Every definition has real construction data;
the theorem has the sole `sorry` in that module. Its docstring reproduces the node's nine
proof steps. An accompanying dependency module repairs the pure-codimension interface as
explained below. Neither natural-language node statement is changed.

I read the current item, all its statement-dependency records, their recorded declarations
and docstrings, and the current blueprint proofs `sk-thm-smooth-purity.proof.md` and
`sk-prop-sp-orientation.proof.md`. The latter displays the three orientation factors.
The retained partial draft was repaired: its arbitrary orientation existential and its
adjunction-identity conclusion did not state those normalization assertions.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Prime ell, n at least one | `(ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)` |
| A = Z/(ell^n) | The recorded `NoetherianSectionSpecialization.Coeff ell n`, definitionally `ULift (ZMod (ell ^ n))`, is the universe lift of that ring. |
| Ordinary unbounded constant-A module derived categories | `DerivedCategoryModule (Coeff ell n) X` and the analogous category on Y; coefficients are `ModuleCat.{u+1}` and schemes are `Scheme.{u}`. |
| X and Y Noetherian, ell invertible on both | `[IsNoetherian X] [IsNoetherian Y]`, `hX`, `hY`, with invertibility in every structure stalk. |
| Separated etale finite-type f | `[Etale f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`; “finite” in the item's name does not mean a finite morphism. |
| f compactifiable | `[HasCompactification f]` uses the recorded existing compactification notion. |
| The canonical graph-normalized comparison | `N : FiniteSmoothCompactSupportComparisons A` and `hN : FiniteSmoothComparisonNormalized A N`. These abbreviate exactly the comparison-family type and the graph/sheaf plus homotopy/derived-unit equations in `etaleSupportMapCompatibility`. That dependency supplies such families. The theorem is uniform in every family satisfying those equations. |
| Identify compact-support and sum adjunctions, including counit | `finiteSmoothSumComparison` transports N through `rightDerivedLowerShriekIso`. `finiteSmoothAdjointCoordinates` constructs rho by `Adjunction.rightAdjointUniq` applied to the actual compact-support adjunction and the existing termwise sum adjunction; the final isomorphism identifies exact and left-derived inverse image. |
| W, p1, p2, Delta | Mathlib `pullback f f`, `pullback.fst f f`, `pullback.snd f f`, `pullback.diagonal f`. The named Noetherian instance only packages the existing locally Noetherian and compact-space base-change instances. |
| Rank-zero N_Delta=X, pi=z=id after canonical identification | `G.normalIso` asserts that the actual Rees normal-cone projection is an isomorphism. Its specified zero section is inverse by `normalConeZeroSection_normalConeProj`. This retains the actual cone, rather than substituting an unrelated smooth bundle. G is existentially supplied in the conclusion. |
| Factor (i), Delta pullback of exceptional base change | `finiteSmoothDiagonalFactor` is the inverse section compositor followed by Delta pullback of `dualizingComplexBaseChangeMap A (IsPullback.of_hasPullback f f).flip`. This is the same actual mate as the recorded smooth-base-change interface, with the square flipped to make p1 the new vertical map. |
| Factor (ii), normalized deformation comparison | `G.deformationCompact`, `G.comparison`, `G.normalized` supply precisely the existing Rees family, its comparison kappa, and the recorded t=1 normalization. `finiteSmoothDeformationFactor` is the recorded `specialization` at zero with that kappa. Its target is the actual normal-section invariant. |
| Factor (iii), inverse vector-bundle purity with rank-zero integration | `finiteSmoothRankZeroFactor` transports the actual normal pair to `(X,id)` by its projection and zero section and the canonical section base-change mate. It then uses the counit-preserving comparison with the identity adjunction for `unboundedEtaleLowerShriekId`. This is the inverse purity map of the specified rank-zero trace: `def-amb-vector-integration` explicitly prescribes the identity-adjunction trace at d=0, and the zero-fold Tate tensor and zero shift are the coefficient unit. No arbitrary vector-bundle isomorphism or arbitrary trace is supplied. |
| Each factor is identity in adjunction-preserving coordinates | The three successive equalities compare (i) followed by the p1 section coordinates to the f coordinates, (ii) followed by normal coordinates to p1 section coordinates, and (iii) to the normal coordinates. These are equalities of the actual arrows, not just assertions of invertibility. |
| Alpha is the specified three-factor composite, and is identity in coordinates | The existential isomorphism alpha is constrained by `α.hom = finiteSmoothDiagonalFactor ... ≫ finiteSmoothDeformationFactor ... ≫ finiteSmoothRankZeroFactor ...` and `α = finiteSmoothOmegaCoordinates ...`. Thus its choice is determined. |
| Phi is the specified projection-and-counit tensor map | `finiteSmoothGammaMap` uses the recorded `smoothTensorDualityMap`, preceded by the inverse right unitor and tensoring with `α.inv`. |
| For every unbounded K, gamma is the canonical counit-preserving comparison | `∀ K : DerivedCategoryModule A Y`, `finiteSmoothGammaMap ... = (finiteSmoothAdjointCoordinates ...).inv.app K`. This also gives isomorphy and naturality, without boundedness, constructibility or Tor-amplitude assumptions. |
| Its adjunct is precisely sum/evaluation | The last equality uses the actual compact-support `homEquiv.symm` on the left. The right is N's transported comparison, sum extension of `L(f*) ≅ D(f*)`, and the actual counit of `(etaleLowerShriekUpperStarAdjunction ...).mapDerivedCategoryAdjunction`. It is not the tautological formula for the same adjunction's own counit. |

The comparison-family type and its normalization predicate are only abbreviations and a
conjunction of equations already in the recorded dependency; they do not construct a
second sum functor, compact-support functor or canonical comparison. In particular, the
module does not invoke `nonempty_etaleCompactSupportNormalization` or use that theorem as
a replacement proof route. The actual graph comparison is the one independently supplied
by `lem-sfb-quasifinite-compact-support-exact` and `lem-pur-etale-support-map-compatibility`.

Dependency declarations read and reused:

- `def-asd-compactifiable`: `Sheaf.AlgebraicGeometry.CompactifiableOverField`, with
  `AlgebraicGeometry.Compactification` and `HasCompactification` from
  `WeilConjectures.Compactification.Defs` as its defining clause.
- `def-weil-pbc-derived-categories`: the six-functor `DerivedCategoryModule` in
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`; its recorded migrated module is
  `WeilConjectures.AlgebraicGeometry.DerivedCategories`. The theorem needs the unbounded
  derived category, not the torsion-cohomology predicate.
- `thm-amb-etale-exceptional-adjoint`: `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint`,
  `isLeftAdjoint_rightDerivedLowerShriekOfCompactification`; the constructions use
  `rightDerivedUpperShriek` and `rightDerivedUpperShriekAdjunction` from the framework.
- `prop-asd-smooth-base-change`: `Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange`,
  `smoothExceptionalBaseChangeMap`, `smoothDualizingBaseChangeMap`. The diagonal factor
  uses the framework `dualizingComplexBaseChangeMap` on the flipped actual square;
  expansion gives precisely the recorded exceptional mate and unit comparison.
- `lem-pur-noetherian-etale-section-specialization`:
  `Sheaf.Paper.NoetherianEtaleSectionSpecialization`, `Coeff`, `family`, `Normalized`,
  `specialization`, `sectionMap`; the section/identity compositors are the published ones.
- `def-amb-vector-integration`: `Sheaf.AlgebraicGeometry.VectorBundleIntegration`,
  `vectorBundleIntegration` and its defining rank-zero identity-trace normalization.
- `thm-asd-smooth-tensor`: `Sheaf.AlgebraicGeometry.SmoothTensorDuality`,
  `smoothTensorDualityMap` and its actual inverse projection/counit construction.
- `lem-pur-diagonal-regular-immersion`: the dependency module supplied in this delivery,
  using the current recorded `IsRegularImmersionOfPureCodimension` definition.
- `thm-amb-vector-bundle-purity`: `Sheaf.Targets.VectorBundlePurity`,
  `VectorBundlePurityAtModulus`, the purity adjunct of the actual integration trace.
  The factor here evaluates that construction at the rank-zero identity representative.
- `def-pc-scheme`: Mathlib `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `def-weil-pbc-noetherian-ring`: Mathlib `IsNoetherianRing` and
  `isNoetherianRing_iff`, together with `IsNoetherian` for the finite affine-cover convention.
- `lem-sfb-quasifinite-compact-support-exact`:
  `Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact`, `quasifiniteCompactSupportExact`.
- `lem-pur-etale-support-map-compatibility`:
  `Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility`, `etaleSupportMapCompatibility`;
  its graph and homotopy normalization equations are written verbatim in the helper predicate.

The ordinary sum adjunction is reused directly as
`(etaleLowerShriekUpperStarAdjunction (ModuleCat A) e inferInstance).mapDerivedCategoryAdjunction`,
which is the construction recorded in `lem-amb-etale-adjoint-locality`. This avoids depending
on an ambiguously resolved short name. All stated proof dependencies available as modules
are imported directly or through the dependency modules (including the K-flat, tensor
symmetry, shriek projection and Nagata modules).

Edge cases checked before finalizing the statement: empty X; both schemes empty; identity
f; open immersion; a nontrivial finite disjoint union/fold map; n=1; K=0; and complexes
unbounded in both directions. No nonemptiness, surjectivity, finite-morphism assumption,
positive relative dimension, field-base assumption or boundedness is added to the item.
The clopen complement of Delta is retained in the Rees deformation. For d=0 the ideal is
zero near each point of Delta even when it is the unit ideal on the complementary component.
Thus no erroneous global zero ideal or positive-codimension regularity predicate is used
for that case. The identity counit evaluates each sheet once, including for the fold map.

Searches performed:

- `msearch.py ... leanfinder`: “For a separated etale morphism the diagonal deformation
  smooth purity orientation and tensor map agree with the sum extension adjunction counit”.
  Eight generic algebraic differential/etale hits, no normalization theorem.
- `msearch.py ... loogle 'CategoryTheory.Adjunction.rightAdjointUniq'`: twelve hits,
  including the exact right-adjoint uniqueness definition and its counit equation. Used
  that existing construction.
- `msearch.py ... grep 'etale.*purity|purity.*etale'`: no Mathlib match.
- `msearch.py ... leansearch`: “For etale morphisms the smooth purity isomorphism constructed
  by diagonal deformation and rank zero trace is the counit preserving sum adjunction
  comparison”. Eight generic smoothness/etale/ordinary counit results, no matching theorem.
- `rg` in Mathlib and both allowed project trees for the concrete comparison, identity
  pullback, normal-cone, rank-zero and diagonal names found the reused interfaces above.
  `rg` for `finite_smooth_gamma|finiteSmoothGamma|rankZero|rank_zero|zeroRank` found no
  existing theorem stating this normalization. The exact item-id search in the upstream
  source also found none. The upstream diagonal declaration's full docstring disclosed
  the positive-codimension and missing-dimension-clause mismatch repaired below.

There is no STATEMENT-DISPUTED flag and no correction to the item's statement. The old
diagonal binding is an interface fault, handled as a lean-only dependency repair.
All new helper definitions belong to the stated three-factor construction; there are no
new independent notions or new DAG nodes.

## Dependency modules

`lem-pur-diagonal-regular-immersion` is rebound to
`Sheaf.AlgebraicGeometry.DiagonalRegularPureCodimension`, declaration
`AlgebraicGeometry.diagonal_isRegularImmersionOfPureCodimension`. The old
`AlgebraicGeometry.isRegularImmersion_diagonal` has `[NeZero d]` and concludes the
upstream affine-local predicate, whose docstring explicitly omits the chapter's stalkwise
dimension equality. The definition node now records the separate
`IsRegularImmersionOfPureCodimension`, and this repair uses it. The current
`blueprint_update` states only regularity of the diagonal in the chapter's fixed setting;
it removes the historical tangent-bundle conclusion. The replacement states precisely
that assertion over separated finite-type field schemes, with `hd : 1 ≤ d` as prescribed
by the definition node's positive-codimension convention. The structural map of W is
`pullback.fst f f ≫ f ≫ aY`. The f finite-type binders follow the same fixed setting;
for a smooth map between the finite-type field schemes they also follow from local finite
type and Noetherian quasi-compactness. Its single postponed theorem has the full etale-local
regular-generators and stalk-dimension proof in its docstring. The consumer's rank-zero
clopen argument is stated directly and does not invoke this positive-codimension theorem.
Only this dependency's `lean` field changes; the current source and blueprint_update stay.

## Second reading by Q17

A separate rereading in this worker session compared the current node, current blueprint,
both modules and both JSON records clause by clause. No other agent was started, as the
dispatcher expressly forbids delegation for this item; this is a self-rereading, not a
claim of an independent second worker. The maintainer's independent review remains the
external review gate.

The rereading rejected the retained draft's unconstrained alpha and tautological counit
formula. They were replaced by the actual three-factor composite, all three coordinate
equalities, equality with rho at the unit, equality of gamma with rho inverse, and the
actual sum-counit formula. It also rejected using a full compact-support-normalization
existence theorem as the input proof route: the final quantification uses only the exact
canonical comparison equations of the two specified support dependencies. The normal
cone is the actual extended-Rees cone throughout; its identification with X is by its
projection, not a fresh cone datum or an arbitrary map. Rank-zero integration is evaluated
in its prescribed identity-adjunction coordinates, with the section base-change transport
retained. There is no replacement of the source orientation by an arbitrary isomorphism.

For the dependency repair, I reopened the `blueprint_update` and the definition node.
Positive codimension is already part of the latter, and the current blueprint drops the
old normal/tangent-bundle conclusion. The replacement's conclusion uses that exact landed
predicate, including its dimension equality; the old affine-local predicate is retained
only as a proof import. The empty-scheme case remains included. Neither node's statement
nor any citer was edited.

Validation: prescribed scompile.py checks compiled both modules separately in import
order, without errors or warnings (the dependency took about 2 seconds; the main module
about 13 seconds). The required deliver2.py --no-push dry run passed the server preflight
and every per-file compilation, printing OK for commit 60f6c95823. Both node copies differ
from the read-only base only in lean, and both stored signatures occur verbatim in their
modules. Final delivery uses the prescribed deliver2.py wrapper.
