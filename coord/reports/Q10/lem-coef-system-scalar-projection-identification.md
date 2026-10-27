## Worker report

States `WeilConjectures.SystemScalarProjection.system_scalar_projection_identification`
in `Sheaf.Paper.SystemScalarProjectionIdentification`. Definitions contain real map
composites; the single postponed theorem has the complete seven-step proof in its
docstring. No node statement, dependency list, or proof changes are made.

Hypothesis and clause correspondence:

- Global field and distinct primes: `K : FiniteFieldDatum.{u}`, `l : ℕ`,
  `[Fact l.Prime]`, `_hl : l ≠ K.p`. Finite coefficient extensions are `E,L :
  Type (u+1)` with fields, `Algebra ℚ_[l]`, finite-dimensional instances, and
  the actual inclusion `i : E →ₐ[ℚ_[l]] L`.
- Quotient towers: reuse `FiniteFreeSystemRestriction.A`, `.B`, `.aTransition`,
  `.bTransition`, `.systemInclusion`. Index `n : ℕ` means positive exponent n+1.
  B is S/pi^(n+1)S, not S/v^(n+1). `s : Assertions ... d b ramification`
  is precisely the supplied restriction/scalar/geometry calculus of the dependency;
  its `ramifiedIdeal` identifies B with exponent e(n+1), and `reducedBasis` is the
  reduction of the same integral `b : Fin d → O_L` at every level. No unproved
  arbitrary equivalence is selected from a mere Nonempty assertion.
- Small sites and strict systems: use `Scheme.ProEt.topology`,
  `SemilinearProperOpen.Modules` and `.Derived` with coefficient/sheaf universes
  `{u+1,u,u+1}`. These are ordinary derived categories of the actual sequence-site
  module category, not functors into separate derived categories. `U` is the
  dependency's exact termwise restriction; `T` is `(s.scalars X).scalar.T`.
- Geometric hypotheses: `X,Y : Spaces K` retain separated finite-type schemes over
  k; `f.IsOver`, `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f` render
  the stated k-morphism. `c : Compactification f` retains the open and proper
  constituents. `ambient Y c` derives, rather than assumes, the same properties of
  the intermediate scheme. Compact support is the dependency's `compact = J ⋙ R`.
- Normalized input and all level finiteness conditions: `domain ... X M` is exactly
  `Normalized` with the dependency's scalar reduction adjuncts together with
  `levelwiseCtf`. The finite cohomological support, constructibility for every
  homology sheaf, and `∃ a b, a ≤ b ∧ ...` finite Tor condition are inside `∀ n`;
  no bound or stratification uniform in n is imposed.
- Specified a_p and b_j: `properScalar` is the B-geometric `homEquiv` applied to
  `scalarPull.hom` followed by T of the actual A-counit. `scalarPull` is the double
  adjunction conjugate of the dependency's section-normalized restriction square.
  `openScalar` is the open/scalar left-adjoint comparison conjugate to that same
  square; it is the ordinary open balancing map. `comparison` is exactly
  `properScalar(j_! M)` followed by R_B of `openScalar`.
- Specified projection: `PinnedGeometry.geometry` is the recorded semilinear
  `Geometry`, specialized to the actual A tower. Its coefficients, transitions,
  target calculus, ordinary pullback and finite adjunctions are pinned to the
  existing operations. `mu_eq` and `levelMu_eq` identify `mu` and `levelMu`
  with `Geometry.tensorPullback` and `Geometry.levelTensorPullback` themselves.
  `coefficientPull` localizes the ordinary coefficient adjunct stored by
  `s.geometry`, via `mapDerivedCategorySingleFunctor`.
  `properProjection` applies `mu` to `(Rp_* H, coefficientObject)`, then the
  actual `lower.closed.tensor.map (epsilon, coefficientPull.hom)`, then the
  actual A-geometric `homEquiv`. It is independent of `scalarPull`.
  `openTensorInv` is the open-unit transpose of the inverse pinned tensorator,
  with coefficient pullback inserted. This is precisely the `gamma_inverse`
  normalization of `lem-sf-open-tensor-normalization`. `projection` is the
  proper map followed by Rp_* of the inverse open tensor map.
- Linked tensor normalization and equality before evaluation: the theorem now
  quantifies `∃ (ω : TensorPresentation ...) (g : GeometryFamily ...), ...`.
  The same `ω` is an argument to `Identification`. Its `projection_eq` says
  `U(comparison) ≫ compactIso.hom = ω_Y.hom ≫ projection g ≫ compact.map ω_X.inv`.
  `TensorNormalization.pure`, `.summand`, and `.representative` pin this omega
  on ordinary sections and K-flat total-complex representatives. It is no
  longer a separate Nonempty assertion. Equality lives in D(S_A), before
  evaluation; `Identification.open_normalization` asserts the actual tensor
  open inverse is invertible.
- Scalar-adjunction mate: `Identification.scalar_mate` is the exact equality
  under `(s.scalars Y).scalar.adjunction.homEquiv`, including the scalar unit and
  inverse restriction/compact-support identification. `Identification.isIso`
  asserts invertibility of c in D(S_B).
- Finite evaluations: `LevelData` retains the normalized scalar/proper/open
  `AdjunctionEvaluation` records. Its finite ring square is the naturality square
  of the actual constant coefficient maps; `restrictionPull` and `restrictionPush`
  use `Scheme.proEtaleRingRestrictionDerivedPullback/DirectImage`. They do not
  evaluate any system comparison. `pull` and `openMap` are their finite scalar
  conjugates under `VaryingRing.levelAdj` and `.levelJAdj`; `finiteScalarMap`
  is the finite B-geometric transpose of the extended finite A-counit, followed
  by finite open balancing. `coefficientPull` is independently localized from
  finite constant-section adjuncts. `properProjection` uses the same pinned
  `levelMu`, finite `lower.levelClosed.tensor`, and finite counit. `openTensorInv`
  uses the finite open unit and inverse levelMu, the normalized finite balancing
  formula of the open-tensor dependency. `finiteMap` is finite omega followed by
  this actual finite PF followed by compact support of inverse finite omega.
  `Equation` asserts both that restriction of `finiteScalarMap` equals this
  independent `finiteMap` and that evaluation of `comparison` equals the
  finiteScalarMap word, with all evaluation identifications inserted. The open
  inverses' invertibility is asserted on these inputs, not assumed.
- Fixed-basis finite sums: `BasisCoordinates.ordinary_section` specifies each
  inclusion as the section of the same integral basis element times (1 tensor x).
  `representative` fixes these inclusions on every complex via the existing model
  counit, not just on cohomology or finite evaluations. `orthogonal` and `total`
  express the coordinate identities for a finite direct sum. `Distributivity`
  says the restricted comparison takes each summand inclusion to compact support
  of that inclusion; the total identity specifies the complete distributivity map.
- Proper refinements: `refinementGamma` reuses the published intrinsic gamma with
  its identity direct-image factor; `refinementCompositor` uses the actual sComp
  and equality cast. `theta` is R of the inverse gamma after this compositor.
  The theorem explicitly asserts gamma is invertible on M for A and on T M for
  B, including ramification e>1, so no B-tower specialization of the A-only
  refinement theorem is assumed. Its displayed equation is
  `comparison c₁ ≫ theta_B = T(theta_A) ≫ comparison c₂`, in D(S_B).
- Identity, composable refinements, common refinements and cocycle:
  `RefinementCoherence` records these four equations for both towers, using
  `Refinement.id`, `.comp` and arbitrary supplied common-refinement spans.
  Together with the scalar square these imply its identity/pasting and common
  refinement normalization. All equations have the whole-system category as
  ambient category; inverse limits are not used.

Dependency declarations read (the convention records have no Lean object):

- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`, `WeilConjectures.FiniteFieldDatum`.
- `def-weil-l-adic-coefficient-extension`: `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, `Padic.finite_coefficientExtensionRing`.
- `lem-coef-finite-free-extension`: `Sheaf.Paper.FiniteFreeCoefficientExtension`, `WeilConjectures.FiniteFreeCoefficients.finite_free_coefficient_extension`.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`, `AlgebraicGeometry.Scheme.ProEt`.
- `def-weil-size-convention`: convention, expressed by explicit universes / standard scheme properties.
- `def-weil-scheme-morphism-properties`: convention, expressed by explicit universes / standard scheme properties.
- `lem-coef-semilinear-derived-sections`: `Sheaf.Paper.SemilinearDerivedSections`, `WeilConjectures.SemilinearSections.semilinearDerivedSections`.
- `def-pc-sheaf-restrict-scalars`: `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`, `SheafOfModules.restrictScalars`.
- `lem-pur-derived-change-of-rings`: `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`, `ModuleCat.nonempty_ordinaryDerivedChangeOfRings`.
- `def-weil-compactifications-refinements`: `WeilConjectures.Compactification.RefinementCategory`, `AlgebraicGeometry.Compactification.Refinement`.
- `lem-coef-finite-adjunction-diagram-realization`: `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization`, `WeilConjectures.FiniteAdjunctionDiagram.finiteAdjunctionDiagramRealization`.
- `lem-coef-finite-free-system-restriction`: `Sheaf.Paper.FiniteFreeSystemRestriction`, `WeilConjectures.FiniteFreeSystemRestriction.finiteFreeSystemRestriction`.
- `def-coef-normalized-dvr-tower`: `Sheaf.Paper.NormalizedDVRTower`, `WeilConjectures.NormalizedDVRTower`.
- `def-weil-finite-tor-amplitude`: `Sheaf.Paper.FiniteTorAmplitudeSites`, `WeilConjectures.finiteTorConstructibleEtale`.
- `def-weil-pbc-constructible-complexes`: `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`, `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`.
- `def-weil-pbc-adjunction-mate`: `Mathlib/CategoryTheory/Adjunction/Mates.lean`, `CategoryTheory.mateEquiv`.
- `lem-sf-open-tensor-normalization`: `Sheaf.SixFunctors.OpenTensorNormalization`, `SheafOfModules.openTensorNormalization`.
- `def-exchange-projection`: `Sheaf.Paper.ExchangeProjectionSuppliedDomains`, `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`.
- `lem-pur-system-level-projection-formula-coherence`: `Sheaf.Paper.SystemProjectionFormulaCoherence`, `WeilConjectures.SystemProjectionFormula.system_projection_formula_coherence`.
- `lem-pur-finite-free-compact-composition`: `Sheaf.Paper.FiniteFreeCompactSupportComposition`, `AlgebraicGeometry.FiniteFreeCompactSupport.finite_free_compactSupport_composition`.
- `def-sf-refinement-comparison-isomorphism`: `Sheaf.Paper.RefinementComparisonIsomorphism`, `AlgebraicGeometry.ProEtale.refinementComparisonIsomorphism`.
- `lem-pur-system-compactification-pf-substitution`: `Sheaf.Paper.SystemCompactificationProjectionSubstitution`, `WeilConjectures.SystemTensorMate.system_compactification_pf_substitution`.

The owning restriction module supplies the quotient ring constructions, scalar
adjunction and termwise restriction used directly here. The statement modules for
projection coherence, refinement substitution and open normalization are imported
for their map interfaces / proof plan. No dependency module needs replacement.

Searches actually run:

- msearch leanfinder: “Restriction of finite free coefficient scalar adjunction mate
  equals projection formula map on derived strict systems and commutes with
  compactification refinements”: eight unrelated Profinite/Nobeling hits; no match.
- msearch loogle: `CategoryTheory.mateEquiv, CategoryTheory.Adjunction.homEquiv`:
  zero hits for the combined query.
- msearch grep `scalarMate|projectionFormula|mateEquiv` in Mathlib/CategoryTheory:
  general mate equivalence and its unit/counit equations; no system coefficient
  and refinement assertion.
- rg in project Sheaf and WeilConjectures for scalar/projection, scalar mates,
  compact scalar comparison, and the exact node id: finite-stage scalar/projection
  results and existing whole-system restriction / PF infrastructure found, but
  no declaration of this whole-system identification. The exact id has no source
  declaration. The namespace `WeilConjectures.SystemScalarProjection` was absent.

Source check: the node is an agent-formulated coherent-system obligation extracted
from the older rational-operations proof, not a blueprint unit statement. The
current latest blueprint no longer has that old rational-operations file. Read the
current `sec-smooth-purity/sk-lem-sp-tower/lem-coef-finite-free-extension.md` and
its proof: reducing one free integral basis, finite-free additivity, canonical
counit/evaluation transposes, compatibility with quotients and the ramified
exponents en agree with the obligation's seven-step proof. The source node's own
statement and proof are preserved, rather than silently switched to another unit.

Edge cases: positive level n=1 is index zero; ramification e>1 retains the same
pi-power tower and actual ideal equality; identity E=L and rank one reduce to
unit comparisons; empty scheme/open and zero M give the ordinary zero maps;
identity and composable refinements retain the actual compositor casts. Orthogonal
coordinates also make sense for an empty finite index set; the supplied reduced
basis bijection rules out rank zero for these nonzero quotient rings. No common
cohomological/Tor interval, faithfulness of evaluation, derived restriction
faithfulness, or evaluated K-injectivity assumption occurs.

## Second reading by Q10

Final in-thread rereading (no subagent was started, as instructed by the dispatcher).
Matched each clause above against the unchanged node and the source file. Corrected
an ambient-scheme instance inference issue, the orientation of sComp, finite-map
evaluation endpoint factors, and the direction of the complex naturality equation.
Added TensorPresentation's pure-section and K-flat summand normalization to avoid
leaving U T as an unexplained substitute for the recorded actual tensor. Confirmed
that the ramified upper refinement mate's invertibility is a conclusion, not an
extra assumption. The maintainer supplies the independent delivery review.

Repair validation is recorded after the final source changes. All compilation uses
scompile.py and all packet construction uses deliver2.py. No global build or direct
Git operation was used.

## Returned delivery repaired

The immutable returned head was ee1a9cd6b110. The sandbox initially matched that
packet; its item statement, source, dependencies and proof are retained. The current
shared dependency sources were reread, including SemilinearGeometryDerived,
SemilinearGeometryOps, FiniteFreeSystemRestriction, OpenTensorNormalizationData,
OpenTensorNormalization, ProEtaleRingSheafChangeAdjunction and VaryingRingOperations.
The prescribed wrapper rebases the repaired packet onto the current server branch.

1. H3+H4, system PF and linked omega: removed the old `tensorPull` and the
   U T-based proper/open projection definitions. The replacement uses actual
   closed tensor, `coefficientObject`, the pinned `Geometry.tensorPullback`,
   section-normalized coefficient pullback, and actual epsilon tensor identity.
   The theorem supplies the pinned realization as a conclusion. Its very same
   omega occurs in Identification.projection_eq, conjugating actual PF on both
   endpoints. No scalar comparison is used to define PF.
2. H3, independent finite word: replaced the evaluated-system definitions of
   LevelData.pull and openMap by canonical finite restriction squares and finite
   adjunction conjugates. The B-linear finite coefficient comparison is a finite
   proper-counit/open-balancing word. The independently defined finiteMap uses
   Geometry.levelTensorPullback and the finite open tensor inverse specified by
   the finite open unit; Equation now identifies the restricted B-linear map
   with this actual finite tensor PF as well as its evaluated system comparison.

The accepted normalized domain, original B-linear comparison, scalar_mate, isIso,
basis normalization/distributivity, refinement equation direction, both refinement
coherence records and the upper gamma isomorphism conclusion are retained. Checked
zero M, empty open/source, identity coefficient extension, rank one, ramification
e>1, and identity/composable refinements against the repaired formulas. No uniform
cohomological or Tor interval was introduced. No conclusion is detected levelwise.

Validation: final full repaired module passed scompile.py in 36.8 s (sandbox) and
41.6 s (library), with no errors or warnings. Generated structure injectivity
lemmas are disabled to avoid unnecessary elaboration; no mathematical field was
removed. One named theorem retains its stage-2 sorry. The finite equation writes
the actual evaluated object explicitly, without a hidden let binder.

Final validation after removing the hidden let and wrapping long lines:
scompile.py passed the complete file, sandbox 49.0 s and library 47.9 s,
with no errors or warnings. The first dry run correctly rejected the three
long lines from the explicit finite evaluation; all three were wrapped.
