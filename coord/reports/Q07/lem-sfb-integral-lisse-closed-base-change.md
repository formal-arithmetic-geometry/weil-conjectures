## Worker report

The item now has its stage-2 statement in `Sheaf.Paper.IntegralLisseClosedBaseChange`.
The NB merge is a reviewed stage-1 proof split, not a stage-2 statement: its item has
no `lean` record. The previous attempt's unchanged-node refusal was therefore caused
by submitting no new Lean binding. This packet supplies the missing statement.

The sole postponed theorem is
`AlgebraicGeometry.ProEtale.IntegralLisseClosedBaseChange.integral_lisse_closed_base_change`.
Every definition and the coefficient-map instance has actual data; no chosen arbitrary
map, hollow existence, or stronger exchange hypothesis is introduced. The theorem's
source/proof docstring contains the seven steps of the current DAG split. The exact
all-continuous theorem remains the agent-formulated input that the node says it is;
Stacks 0EYP supplies only a discrete-etale analogue. No source or node correction is made.

Clause-by-clause reading of the statement:

- Distinct primes p and ell are `(p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (_hpℓ : p ≠ ℓ)`.
  The field of characteristic p is `(k : Type u) [Field k] [CharP k p]`.
- E with its norm topology and finite extension structure is `(E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]`. Ω with the extended norm topology
  is `(Ω : Type u) [NormedField Ω] [NormedAlgebra E Ω] [IsAlgClosure E Ω]`.
  No completeness instance for Ω is requested.
- Both coefficient cases are separate conjuncts `GeometricAssertions
  (Profinite.continuousCoefficientRingObj E) w` and the same expression for Ω.
  These are exactly all continuous functions, with precomposition restrictions and
  pointwise multiplication. At coefficient universe u,
  `continuousCoefficientRingObj` has the same presheaf and ring operations as the
  dependency `continuousMapRingObjOfUniverse.{u,u}`. Their sheafness proofs are proof
  irrelevant. The inclusion is literally `continuousMapRingObjMapOfUniverse.{u,u}`
  applied to `algebraMap E Ω` and its continuity, not finite-subextension coefficients.
- `condensedRingObj Λ X` is the recorded coefficient `p_X^* Λ`, and `Mod` is Mathlib's
  internal module category. `pull` is the exact module pullback's `mapDerivedCategory`;
  `moduleObjectDerivedPushforward` is the recorded total right derived lowerStar,
  computed using K-injective resolutions in the module category. All are ordinary
  unbounded `DerivedCategory`, without bounded-constructible restrictions.
- The single universe u contains k, E, Ω, all schemes and profinite parameter sets;
  the site objects live in u+1 with morphisms in u, and abelian coefficient groups
  live in u+1 as the dependency framework requires. This is a common compatible
  universe, obtainable for arbitrary supplied data by choosing a common enlargement;
  it does not equate the site's object and morphism universes.
- X and U are affine via `[IsAffine X] [IsAffine U]`. Their k-scheme structures are
  `Over (Spec (.of k))` instances. The morphism q has `[IsIntegralHom q]` and is over k.
  The closed immersion s has `[IsClosedImmersion s]` and is over k. No finite type,
  Noetherian, connectedness, positive-rank, or finiteness condition on q is imposed.
- `T`, `h`, `qZ`, and `w : IsPullback h qZ q s` are exactly X_Z and its projections.
  Using an arbitrary specified cartesian square includes the chosen fibre product and
  every isomorphic presentation. The induced k-structures are recorded by the Over
  instances and IsOver binders; they add no geometric restriction.
- For every `M : Mod ... (condensedRingObj Λ X)`, `IsLisseCoefficientModule Λ M` is the
  actual recorded finite-free local triviality condition. Its definition uses a
  pro-etale covering and `Mod.IsFree`, whose natural number rank may be zero and may
  vary with the cover object. No substitute lisse notion is defined here.
- The displayed exchange is `IsIso ((exchange Λ w.toCommSq).app
  ((DerivedCategory.singleFunctor _ 0).obj M))`. Its source is s* Rq_* M[0]; its
  target is RqZ_* h* M[0]. Exact pullback identifies h* M[0] canonically with (h*M)[0].
- `adj` transports the recorded total-derived adjunction along its canonical exact
  pullback comparison. `pullComp` is the recorded underived pullback-composition
  isomorphism localized by `mapDerivedCategoryNatIso` and its composition comparison.
  `square` assembles qZ* s* = h* q* using the actual equality w.w.
  `exchange` is `Adjunction.squareExchange` with those adjunctions and this square.
  Its component is definitionally the adjunct of square followed by h* counit, so the
  node's arrow normalization is retained, rather than just an isomorphism of endpoints.
- `ModuleNaturality` displays the equality for every map between lisse modules, after
  the actual degree-zero embedding and derived push/pull maps.
- `CubeNaturality` quantifies over cartesian cubes with weakly-etale base map v.
  Its two explicit composites compare pullback of the old exchange with the new
  exchange using the other two canonical exchange comparisons and the pullback
  composition identifications. No inverse of a direct-image comparison is assumed.
  Isomorphisms are weakly etale; cartesian cubes with such v cover isomorphisms of
  squares, including arbitrary isomorphic fibre-product presentations.
- The same `CubeNaturality` applies to v = the morphism of
  `(profiniteToProEtOf U).obj Q` for any `Q : Profinite.{u}`. Thus it is an equation
  on the entire U[Q], rather than an equality after point evaluation. Further
  profinite parametrization uses the same quantified cubes over U[Q]; composing base
  arrows gives the cube over the original U. Empty Q is retained.
- `ScalarAssertions (coefficientInclusion E Ω) w.toCommSq` uses ordinary
  `Mod.extendScalars`, not derived tensor, on M. `scalarUnit` is the actual unit of
  `Mod.extendRestrictAdjunction`, embedded in degree zero and transported by the
  canonical single/restriction isomorphism. This is precisely x ↦ 1 tensor x.
  `RestrictionExchange` displays coefficient compatibility of the Ω exchange after
  exact restriction, with `restrictPush` directed from restricted Ω direct image to
  E direct image of the restriction. The second conjunct is the naturality square
  for the actual scalar unit. Together they are the node's scalar square, retaining
  canonical comparisons without requiring them invertible.
- No statement asserts exactness of q_* on arbitrary sheaves, or an isomorphism of
  scalar extension with direct image. The only invertibility assertion concerns the
  specified exchange on the stated lisse degree-zero inputs.

Dependency declarations read and used:

- `Sheaf.Topology.ContinuousMapCondensedRing`: the continuous-map presheaf, sheaf,
  abelian object and pointwise ring-object declarations in the node record.
- `Sheaf.Topology.ContinuousMapCondensedRingMap`:
  `Profinite.continuousMapRingObjMapOfUniverse` and the corresponding ring-sheaf map.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`: `coefficientRing`,
  `condensedRingObj`, `upperStarFromPoint`, `profiniteToProEtOf` and the actual
  coefficient pullback identifications. The first is strong-monoidal transport of Λ.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `Mod`, `ModObj`, `Mod.Hom`, `Mod.regular`;
  the free module predicate is the recorded upstream `Mod.IsFree`.
- `Sheaf.Paper.CoefficientHeartStratificationDefs`: `IsLisseCoefficientModule`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`: `moduleObjectDerivedPushforward`;
  its public upstream interface gives `derivedUpperStarLowerStarAdjunction` and
  `leftDerivedUpperStarIsoMapDerivedCategory`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Mathlib.AlgebraicGeometry.Morphisms.Integral`: `IsIntegralHom`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Sheaf.CategoryTheory.AdjunctionSquareExchange`: the actual adjunct construction.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`:
  `coefficientMap` and `derivedComapUpperStarIso`; ordinary `Mod.extendScalars`,
  `Mod.comap` and `Mod.extendRestrictAdjunction` give the actual scalar unit.
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing` exposes the common-universe
  specialization of the recorded all-continuous rings and their commutative structure.

Every recorded proof-dependency module with a Lean binding is imported non-publicly,
except when already publicly needed by the statement. Unstated proof dependencies
(the closed-test model and w-strict component cohomology) are cited in the proof docstring;
no extra theorem or arbitrary existence assumption is introduced to stand in for them.

Edge cases checked against the written signature and formulas: rank zero, different ranks
on the cover, X or Z empty, the unit ideal or zero ideal defining Z, identity integral map,
identity closed immersion, non-finite integral q, non-finitely-presented integral algebras,
empty profinite Q, zero complexes, and incomplete Ω. None is excluded. Identity square
comparisons use the library's actual compositors and equality transport. No coordinate
presentation or positive-rank hypothesis was introduced.

Searches actually run for this attempt:

- `msearch.py leanfinder`: “Closed base change for derived direct images of lisse
  continuous modules under integral morphisms of affine schemes”: 8 hits, concerning
  integral/affine stability, scheme module pushforward and closed immersion stability;
  no derived condensed-coefficient exchange statement.
- `msearch.py loogle`: `"IsIntegralHom", "baseChange"`: one hit,
  `AlgebraicGeometry.IsIntegralHom.instIsStableUnderBaseChangeScheme`, not this result.
- `msearch.py grep`: `(IsIntegralHom|integral).*(baseChange|base_change)`: four Mathlib
  hits, concerning integrality and its base-change stability, not sheaf cohomology.
- `msearch.py leansearch`: “For an integral morphism of schemes and a closed immersion,
  derived base change holds for lisse sheaves of modules over continuous coefficients”:
  eight hits on morphism properties, not the present exchange theorem.
- `rg` in `lean/WeilConjectures` for the exact node id: no match. Searches of that tree
  and `lean/Sheaf` for integral/closed/baseChange/exchange/lisse found the bounded
  constructible framework, discrete/integral étale base change, integral-stratum open/
  closed exchange, and generic adjunct constructions. Their full relevant interfaces
  were read: none states this all-continuous ordinary-unbounded integral result.
  Existing generic derived functors and `Adjunction.squareExchange` are reused.

Validation: the single module passes `scompile.py` in both sandbox and library mode
with no warnings. No source in the shared read-only repository was modified.

## New nodes

None. The helper definitions are just the owning node's specified exchange arrow,
canonical comparisons and the explicit equations spelling out its clauses. They are
listed in `lean.declarations`, with source/blueprint docstrings and real bodies.

## Second reading by Q07

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
