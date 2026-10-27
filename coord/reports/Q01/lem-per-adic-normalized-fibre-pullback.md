## Worker report

The module `Sheaf.Paper.AdicNormalizedFibrePullback` states
`AlgebraicGeometry.Scheme.AdicFibreComparison.adic_normalized_fibre_pullback`.
Its only postponed proof is `by sorry`. `NormalizedPullback` packages the
isomorphisms and their specified equations; it constructs no objects by choice
or by a postponed existence assertion. The original statement and all original
node fields outside `lean` are unchanged. No dependency repairs or new nodes.

Sources read: Bhatt–Scholze, Proposition 6.8.4(1),(4),(6), pp. 59–60,
and Remark 6.8.15, p. 62; Stacks `etale-cohomology.tex`,
`lemma-stalk-pullback`, Tag 03Q1(3), including its colimit proof; current
blueprint `latest/.../sk-p-dl-a1-perverse/lem-per-smooth-pullback-t-exact.proof.md`,
first paragraph. Proposition 6.8.4(4) is used only after affine refinement,
where its qcqs hypothesis holds. The full eight-step DAG proof is carried
in the theorem docstring, including the componentwise inverse, torsion in
integral Hom modules, common refinements and the actual functor equations.

Hypothesis and clause correspondence:

- The field is `{k : Type u} [Field k]`; the prime and its invertibility are
  `(l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]`. `FiniteTypeBase k` is the
  existing `CondensedERealization.Base`: its scheme has an actual structure
  map to `Spec k`, locally finite type, quasi-compactness and separatedness.
  `base l X` derives noetherianity, finite dimension and invertibility in
  every local ring. These consequences are not extra assumptions.
- Coefficients are universally quantified as `(A : Type u) [Field A]
  [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]`; this A is the statement's
  E, not its valuation ring. Its valuation ring and uniformizer are exactly
  `Padic.coefficientExtensionIntegers l A` and
  `Padic.coefficientExtensionUniformizer l A`. The fixed algebraic closure
  and further field L introduce no datum into the pullback assertion;
  quantification covers every finite subfield and every repeated-field case.
- `R : ContinuousRational.Family l` is the realization family supplied by the
  recorded realization theorem. `Fibres l R` consists of the dependency's
  `NormalizedFibre.Assertions`, simultaneously at all finite fields and bases.
  In particular its fibre is finite dimensional, additive and E-linear,
  exact, intrinsically identified with `omega`, and normalized on all lattices.
  Its `fractions` field is the precise inverse-uniformizer-times-limit formula.
- The integral category, completed coefficient sheaves, strict reduction tower,
  raw rationalization and localized standard heart are those used by
  `R.realization` and `NormalizedFibre.Heart`; no category is copied or changed.
  The pair category and scalar associators are context for the sibling scalar
  result, not an additional pullback conclusion or assumption here.
- A scheme morphism is arbitrary `(g : Y.scheme ⟶ X.scheme)`; it is not
  restricted to maps over k, smooth maps or flat maps. The geometric point
  is `(κ : Type u) [Field κ] [IsAlgClosed κ] (y : Spec (.of κ) ⟶ Y.scheme)`;
  the image point is literally `y ≫ g`.
- `NormalizedPullback.pull` is a natural isomorphism
  `heartPull l A R g ⋙ (ω A Y).point.functor ≅ (ω A X).point.functor`.
  `heartPull` is the literal restriction of `R.along.raw`, itself the raw
  localization of the actual completed integral pullback, not an arbitrary
  replacement functor. Being a natural isomorphism includes its equation on
  every rational heart arrow.
- `local_normalization` universally quantifies the adapted source chart C,
  lattice N and presentation φ. A `NormalizedFibre.Chart` is an affine etale
  chart on a finite locally closed stratum; `Lattice` retains the integral
  continuous module, the actual normalized finite-free etale tower and its
  scalar-compatible complete reduction cone.
- For the possibly non-affine pulled chart, the field quantifies
  `W₀ : (pullback g C.map).affineOpens`, a geometric lift `t₀`, and its
  equation with `pullback.lift y s hs.symm`. The returned target chart D is
  identified by `i₀ : D.scheme ≅ W₀.1.toScheme`; its maps are the two actual
  pullback projections after the open inclusion. Thus the formula holds on
  EVERY specified affine neighbourhood through the lifted point, rather than
  just on an unspecified chart unrelated to the pulled chart. The ordinary
  pullback is canonically the same as the iterated stratum/chart pullback
  appearing in the natural-language statement.
- `hsystem` makes M's tower exactly the etale inverse-image tower.
  `pullTowerIso` is constructed using the existing
  `Etale.upperStarCompUliftSheafFiberIso` with module coefficients. Its finite
  components are coefficient-linear canonical inverse-image stalk maps;
  the recorded `inverseImage_stalk_germ` gives exactly their pulled-section
  germ normalization on underlying additive sheaves. Naturality of this
  tower isomorphism includes every quotient transition.
- `P : PullLimit ... (pullTowerIso ...)` retains an integral isomorphism with
  `P.projection` fixing EVERY component to that finite stalk map. The last
  `HEq` in `local_normalization` says pull is its scalar localization conjugated
  by the dependency's two `normalization` isomorphisms. The `HEq` only handles
  the displayed geometric-point equations; it does not forget any map.
- The intervening existential degree-zero models e,e' have H⁰(e)=identity
  and `e'.hom = pullModelMap ... e`. The subsequent germ equation pins q to
  this actual J/derived-pullback/counit comparison and its ordinary tensor
  units, before using any lattice presentation. Thus q cannot be rescaled.
- The integral reduction-cone equation for δ uses the actual finite etale
  inverse-image unit, transported by the canonical site-comparison mate.
  Its section equation pins η to the same integral sections after the
  actual rational coefficient inclusion. Finally
  `ψ.hom = q.hom ≫ modulePull.map φ.hom ≫ η.hom`; the rational lattice
  presentation cannot absorb a scalar independent of q, δ or η.
- `unit_normalization` states the germ formula on every degree-zero
  presentation, not only on a selected lattice. The presentation e' is
  exactly the actual derived counit composite `pullModelMap`.
- `identity` and `composition` require heart isomorphisms whose underlying
  maps are exactly `R.identity.raw` and `R.composition.raw`. Their component
  equations are the asserted identity/composite equations. The composition
  direction is `(h ≫ g)^* → g^* ⋙ h^*`; inverting that comparison yields
  the q-direction in proof step 8.
- Independence of charts, strata and lattices: local_normalization is
  universal over every C,hC,N,φ and W₀,t₀ for the SAME `pull` family.
  `ω.normalization` identifies every lattice computation with that single
  fibre. Changing the source and target identifications therefore conjugates
  the same comparison. On a common refinement a fractional integral map
  represents the change; naturality of `pull` combined with the existing
  `ω.fractions` equation is precisely the node's conjugation equation.
  Equal fractional representatives represent the same rational heart arrow,
  so they have identical maps under the same natural isomorphism. No
  torsion-freeness of integral Hom is imposed.
- Neither a flatness class nor commutation of stalks with limits occurs.
  All limits are the explicit tower of finite etale stalks in `Lattice.fiber`.

Dependency declarations read and reused (full signatures/docstrings checked):

- Scheme properties: convention node `def-weil-scheme-morphism-properties`
  fixes no separate declaration. Mathlib's `LocallyOfFiniteType`,
  `QuasiCompact`, `IsSeparated`, and the recorded `CondensedERealization.Base`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`.
- `Sheaf.Paper.IntegralUniformCoefficient`:
  `Scheme.pbcBoundedConstructibleComplete`; the recorded realization uses
  its actual `PbcBoundedConstructibleComplete` category with finite witnesses.
- `Sheaf.Paper.PbcRationalCategory`: `Scheme.PbcRationalDerivedCategory`
  and the underlying `PbcRationalCategory` raw localization.
- `Sheaf.Paper.LocalizedTStructure`: `Scheme.pbc_localized_tstructure`;
  reused through `ContinuousRational.localizedT` and `NormalizedFibre.Heart`.
- `Sheaf.Paper.IntrinsicQbarCategory`:
  `WeilConjectures.intrinsicPbcQbarCategory` (context only).
- `Sheaf.Paper.PbcScalarExtension`: `Scheme.pbcCoherentScalarExtension`
  and its actual rational associators (context only).
- `Sheaf.Paper.ContinuousRationalDerivedRealization`:
  `ContinuousRational.continuous_rational_derived_realization`, `Family`,
  `At`, `Along.raw`, `modulePull`, `moduleUnit`, identity/composition.
- `Sheaf.Paper.AdicNormalizedFibreExactness`:
  `ContinuousRational.NormalizedFibre.adic_normalized_fibre_exactness`;
  its definitions are in `Sheaf.Paper.AdicNormalizedFibreData`: `Assertions`,
  `Heart`, `Chart`, `Lattice`, `rationalFiber`, `rationalLimitMap`, `Represents`.
- `Sheaf.Paper.LisseCompletedSystemComparison`:
  `ProEtale.CompletedLisse.completed_system_comparison`.
- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`:
  `AlgebraicGeometry.inverseImage_stalk_germ`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the actual coefficient
  integers, uniformizer and quotient construction used by Lattice.
- `Sheaf.Paper.AdicCoefficientDatum`: `Scheme.completedReductionTower`.
- `Sheaf.Paper.PbcQbarCompletedPullback`: `Scheme.pbcQbarCompletedPull`;
  actual integral/raw pullback is retained in `Family.along` and heartPull.
- `Sheaf.Paper.AdicStratifiedPullbackInterface`:
  `AdicFibreComparison.pullbackAssertions`, `FiniteTypeBase`, `base`,
  `heartPull` and their actual finite-type geometry instances.
- Shared helper definitions (not restated):
  `Sheaf.Paper.AdicFibreComparisonData`: `Fibres`, `PullLimit`, `pullTowerIso`;
  `Sheaf.Paper.AdicFibreComparisonCoherence`: `germ`, `presentedFibre`,
  `pullModelMap`. These modules do not import the aggregate comparison theorem.
- Proof-only imports retain the lisse comparison, inverse-image germ theorem,
  normalized-fibre exactness and finite-type fibre-dimension bound. Finite-type
  noetherianity is Mathlib's already imported finite-type morphism material.

Searches for an exact existing statement:

- msearch LeanFinder, query “Normalized geometric fibre of adic constructible
  rational heart commutes with completed pullback independent of lattice”:
  eight unrelated normalization/Proj hits, no match.
- msearch LeanSearch, query “geometric fibre of inverse image of a sheaf is
  the fibre at the image point”: topological stalk pullback and scheme
  module open-restriction comparisons; no adic normalized-heart result.
- msearch Loogle, `CategoryTheory.Functor, CategoryTheory.NatIso`: unknown
  NatIso identifier, no hits; corrected query
  `CategoryTheory.Functor, CategoryTheory.Iso`: twelve generic mapIso hits.
- msearch grep, `normalized.*[Ff]ibre|[Ff]ibre.*pullback`: three unrelated
  Mathlib matches, no normalized adic comparison.
- rg in live `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json`, same terms and this exact item id:
  found `PerAdicNormalizedFibreComparisons.normalizedFibreComparisons`,
  the aggregate ancestor containing pullback, scalar, rank and common-stage
  assertions. Its signature is strictly more extensive than this node;
  it is not recorded as an exact existing match. Its pullback normalization
  formulas were read in full. The current module reuses its pre-existing
  lower definitions, expands the local equations and states only pullback.
  It does not import that downstream aggregate theorem or assume it.

Edge cases checked before writing:

- Empty schemes/strata: no geometric lift exists on an empty stratum,
  so pointwise assertions have no instance there. The empty heart still has
  its zero object; no nonempty stratification or chart hypothesis is added.
- Rank zero: zero finite-free towers have zero inverse limit; the specified
  linear comparison is their unique isomorphism. No rank-positivity premise.
- Positive levels: the actual system uses n:ℕ for uniformizer power n+1,
  so all n≥1 quotients in the source are present without a spurious level 0.
- Identity and twofold composite maps: explicitly retain the existing raw
  unit and composition comparisons; equality is of their actual fibre maps.
- Non-flat maps and closed immersions: g has no flatness requirement;
  finite free local lattice models compute the derived pullback as required.
- Non-affine pulled charts: every chosen affine open through the lifted
  point is quantified. The target chart is explicitly that open, up to iso.
- Fraction equality with torsion in Hom: only annihilation of a cleared
  difference is used, never cancellation before localization.
- Universes: schemes/fields have u, site objects u+1 and morphisms u;
  coefficient module objects are ModuleCat.{u+1}. Every binder is explicit;
  `autoImplicit false` is active. No site universe equality is imposed.

Validation: the delivered module has passed scompile.py's sandbox and named
library passes, with no errors or non-sorry warnings. No global build or
local Lean compilation was run. Delivery preflight and final delivery follow.

## Second reading by Q01

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
