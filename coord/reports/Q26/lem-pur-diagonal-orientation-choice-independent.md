## Worker report

The module `Sheaf.Paper.DiagonalOrientationChoiceIndependent` states
`WeilConjectures.PurityFiniteSetting.diagonalOrientationChoiceIndependent`.
Its only postponed theorem is this node's theorem, with proof `sorry` and the full
six-step DAG argument in its docstring. All three supporting definitions contain
real predicate or morphism data. No node statement, proof, or proof dependency is
changed. The chart-normalization theorem remains a proof dependency only. The new
`existing: true` definition node `def-pur-diagonal-dnc-chart-data` records the
published canonical normal-cone model, diagonal alpha, locality maps, and their
typing facts used to express the requested arrows. The Lean module is unchanged.

The current source is the second sentence of
main-20261015/sec-smooth-purity/sk-thm-smooth-purity/
prop-pur-smooth-purity-naturality-cover.proof.md. It specifies independence of all
choices with fixed standard-pair/Kummer normalization. The current reviewed split
is retained, including its open-restriction correction in proof Step 5.

Clause-by-clause correspondence:

- The primes p and ell, their inequality, q = p^a, a >= 1, the algebraic closure k,
  the finite subextension E/Q_ell and its quotient at n >= 1 are the actual fields
  of `P : PurityFiniteSetting.{u}`. `P.level_pos` excludes only the excluded zero
  quotient level. `P.Coefficient` is the published size lift of
  O_E/(varpi_E^n), with its existing ring structure. No ramification divisibility
  condition is assumed. `P.diagonalExponent = ell^n` annihilates this quotient.
- Y is separated finite type over k through `aY`, `[IsSeparated aY]`,
  `[LocallyOfFiniteType aY]`, `[QuasiCompact aY]`. The named k-morphism f is the
  explicit `f : X ⟶ Y`; its k-structure on X is the composite `f ≫ aY`.
  `[IsSeparated f]`, `[LocallyOfFiniteType f]`, `[QuasiCompact f]` give the
  separated finite-type morphism and imply X is separated finite type over k.
  This merely eliminates the redundant separate structure map and its equality.
- Pure dimension d >= 0 is `d : ℕ` and `[SmoothOfRelativeDimension d f]`.
  The declaration never assumes `1 ≤ d` and never uses the positive-codimension
  convention to exclude zero.
- The sites and constant-coefficient derived categories are exactly those of
  the dependency `PurityDiagonalDualizingObject`: the actual transported
  exceptional object is `P.diagonalDualizing f`, and its target is
  `P.diagonalTwist X d`. The latter is the canonical comparison image of
  `P.diagonalTwistEtale X d = affineLinearBaseCoefficient ... X d`.
  This is A_X(d)[2d], with its ordered finite Tate presentation.
- W, p_1, and Delta are literally `pullback f f`, `pullback.fst f f`, and
  `pullback.diagonal f`. C_Delta is `Dnc.sourceSection` on this section pair.
  The fixed alpha is the published `P.chartDiagonalAlpha d f aY`: its definition
  uses the inverse smooth base-change mate, pullback composition, the unit map,
  and the canonical site comparison. It is independent of every input choice.
- The actual normal cone is `(pullback.diagonal f).ker.normalCone`, with its
  published `normalConeProj` and `normalConeZeroSection`. `chartDiagonalNormalBundle`
  gives the rank-d conormal sheaf, including d=0. Its associated vector-bundle
  presentation is `F = ConormalGradedAlgebra.piece (pullback.diagonal f) 1` and
  the published `e = chartNormalModel d f`. `chartNormal_model_exists` identifies
  e with the canonical symmetric/Rees comparison and supplies its projection
  and zero-section equations. `Dnc.normalSection` is C_N on the actual cone;
  the actual cone is never replaced by a freely chosen isomorphic object.
- The two comparisons are `δ₁ δ₂`, isomorphisms from `Dnc.sourceSection` to
  `Dnc.normalSection`. `DiagonalChoiceDncNormalized` opens exactly the predicate
  under the existential in `Dnc.existsUnique_dncInvariance`, without selecting
  delta or postulating that the two inputs coincide. Its equation reads the
  same restricted DNC-family trivialization at t=1 and t=0 through the specified
  fibre mates and site comparisons. It quantifies every finite-type base change
  allowed there, including identity and nonflat maps, and every such family
  trivialization. This is the dependency's coordinate identity normalization.
- The independent integrations `t₁ t₂` are actual morphisms from
  `Etale.vectorIntegrationSource ... X d F` to `Etale.ordinaryFiniteUnit ... X`.
  The two `Etale.VectorIntegrationNormalization` hypotheses are the existing
  condition on every trivializing open and every frame, for every normalized
  root-line and projective-line datum. They require the actual Kummer-normalized
  affine-space trace, not an arbitrary local isomorphism or mere existence of
  some trace. The conormal presentation describes precisely the normal bundle
  of the preceding clause. No particular cover or frame is fixed.
- `γ₁ γ₂` are isomorphisms from the actual shifted Tate object on that model to
  `P.diagonalOrdinaryDualizing q`. Their two hom equations identify them with
  the adjunction `homEquiv` applied to t_1 and t_2, preceded by the inverse
  canonical Tate/pullback isomorphism. At the coefficient unit this is the
  inverse adjoint vector-purity map of the node; the unit projection and tensor
  unitor have already cancelled in this published normalization. Thus the
  gammas cannot be arbitrary purity isomorphisms unrelated to the integrations.
- `diagonalChoiceBeta` transports from the actual normal-cone invariant via
  `Dnc.normalComparison`, then the normalized etale-locality map for e. It
  applies derived zero-section pullback to the inverse gamma (including the
  published tensor-unit-to-degree-zero-unit map) and the fixed Tate restriction,
  then applies the canonical comparison to the pro-etale category. This is
  precisely beta_i. The universally quantified `t` and `M` are only the
  published normalized root-line and compact-support presentations, never an
  extra geometric or orientation hypothesis.
- Each Pi_i is expressed as `chartDiagonalAlpha.inv ≫ δᵢ.hom ≫
  (diagonalChoiceBeta ... γᵢ ...).hom`. The first conjunct asserts Pi_1 = Pi_2;
  the second asserts Pi_1 = `(P.diagonalDualizingObject d f aY).hom`. Together
  they assert both equalities with the specified canonical orientation, in the
  actual derived Hom set. No assertion about arbitrary orientations is added.

Dependency declarations used, with their owning modules:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting` and
  `PurityFiniteSetting.Coefficient`.
- `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`:
  `AlgebraicGeometry.ProEtale.IsCohomologicallySmoothFiniteCompared`; its
  published coefficient/exceptional conventions are imported without assuming
  cohomological smoothness as an extra hypothesis.
- `Sheaf.Paper.PurityDiagonalBaseChangeCompared`:
  `PurityFiniteSetting.comparedDiagonalBaseChange`, used through the canonical
  alpha definition; no private base-change map is defined.
- `Sheaf.Paper.PurityNormalProjection`:
  `Scheme.Hom.purityNormalProjection` and `purityNormalProjection_eq`, identifying
  the retraction-based cone projection used by DNC with the normal projection.
- `Sheaf.AlgebraicGeometry.DiagonalRegularPureCodimension`:
  `AlgebraicGeometry.diagonal_isRegularImmersionOfPureCodimension` for positive
  rank; rank zero is retained by the published conormal model's empty-sequence
  formulation, rather than by invoking this positive-only interface at zero.
- `Sheaf.Paper.PuritySectionInvariantIntrinsic`:
  `PurityFiniteSetting.sectionInvariantFinite`, the actual intrinsic section
  invariant. `Dnc.sourceSection`/`normalSection` use the recorded comparison
  realization with the same exceptional and derived inverse-image operations.
- `Sheaf.Paper.PurityDncInvariance`: `Dnc.existsUnique_dncInvariance`,
  `sourceComparison`, `normalComparison`, and `pullComparison`; its imported
  finite realization supplies `sourceSection`, `normalSection`, the family,
  and the specified fibre-one/fibre-zero comparisons.
- `Sheaf.Targets.VectorBundlePurity`: `AlgebraicGeometry.Etale.vectorBundlePurity`
  and `VectorBundlePurityAtModulus`; the latter's normalization is exactly the
  `VectorIntegrationNormalization` used for both traces.
- `Sheaf.Paper.VectorBundlePurity`: `PurityFiniteSetting.vectorBundlePurity`,
  with its integration-normalized inverse-purity family.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: the recorded intrinsic
  twists and reexported `diagonalTwistEtale`, `diagonalTwist`, `diagonalExponent`,
  `diagonalExponent_annihilates`, and `diagonalExponent_isUnit` finite interface.
- `Sheaf.Paper.PurityDiagonalDualizingObject`: `diagonalOrdinaryDualizing`,
  `diagonalDualizing`, `existsUnique_diagonalDualizingObject`, and
  `diagonalDualizingObject`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth` and
  `SmoothOfRelativeDimension` (the supplied d is a natural number).
- `Sheaf.Paper.DiagonalDncChartNormalization`: `chartDiagonalAlpha`,
  `chartDualizingUnit`, `chartDiagonalNormalBundle`, `chartNormalModel`,
  `chartNormal_model_exists`, `chartSectionEtaleRestriction`, and
  `chartNormalModelRaw`. These seven declarations are recorded by the new
  definition node `def-pur-diagonal-dnc-chart-data`, added to stmt_deps. The
  theorem `diagonal_dnc_chart_normalization` remains in proof_deps for Step 5.
- The already recorded proof dependencies are imported privately when they are
  not also statement dependencies: `VectorIntegrationSiteComparison`,
  `PurityDiagonalSectionPasting`, `DegreeZeroDerivedMapGluing`, and the recorded
  finite-type/Noetherian interface. They preserve the node's existing proof route.

Edge cases checked before writing and again against the compiled declarations:
rank zero uses the empty conormal frame, zero-fold Tate tensor and identity
adjunction; there is no NeZero d or positive-codimension hypothesis. Empty X
is included and none of the predicates chooses a nonempty open or a point.
Disconnected and nonreduced finite-type schemes are allowed. Every positive
coefficient level is allowed, including levels smaller than the ramification
index; there is no divisibility assumption. The normalization quantifies the
identity base change as well as arbitrary finite-type base changes. Site object
and morphism universes remain those in the published comparison construction;
there is no forced equality of them. The conclusion compares derived arrows,
not just cohomology or isomorphism classes. No statement dispute was found.

Searches for an exact existing statement:

- msearch.py, LeanFinder: "The normalized diagonal smooth purity orientation is
  independent of etale coordinates and vector bundle frames". Eight hits: tangent
  coordinate changes and standard-smooth/etale algebra presentations. None is
  this constant-finite-coefficient pro-etale derived-arrow assertion.
- msearch.py, Loogle: `"diagonal", "orientation"`: zero hits.
- msearch.py, grep: `diagonal.*orientation|orientation.*choice`: zero Mathlib hits.
- rg in both `lean/WeilConjectures` and `lean/Sheaf` with
  `diagonal.*[Oo]rientation|[Oo]rientation.*[Cc]hoice`: existing orientation datum,
  coefficient-change compatibility, canonical diagonal-dualizing construction,
  vector-bundle agreement, and affine chart-normalization declarations; none
  states equality for the two normalized DNC/trace realizations of this node.
- grep -rn of the item id in `lean/WeilConjectures`: no hit. The existing
  `PurityDiagonalOrientationCompatibility` is coefficient-change compatibility,
  and `VectorBundleDiagonalOrientation` concerns a bundle projection's
  orientation, so neither is an exact existing declaration for this item.

Validation: the single delivered module was compiled via the prescribed
`scompile.py Q26 lem-pur-diagonal-orientation-choice-independent` wrapper,
separately in sandbox and library module modes. Both passed with no errors and
no warnings (30.6 seconds and 37.5 seconds respectively, each under 60 seconds).
No diagnostic commands remain. Every variable and universe is explicitly bound
and `autoImplicit` is false. The report's mapping was reread against the node and
all four declarations; independent review belongs to the maintainer.

## New nodes

`def-pur-diagonal-dnc-chart-data` records the five existing definitions
`chartDualizingUnit`, `chartDiagonalAlpha`, `chartSectionEtaleRestriction`,
`chartNormalModelRaw`, and `chartNormalModel`, and their two typing facts
`chartDiagonalNormalBundle` and `chartNormal_model_exists`, all in
`Sheaf.Paper.DiagonalDncChartNormalization`. The primary signature is verbatim
from `chartDiagonalAlpha`. Its source is Steps 1--2 of the current blueprint's
diagonal-dualizing-object proof and the choice-independence sentence. It defines
the coefficient-unit conversion, fixed diagonal base-change alpha, normalized
etale section restriction, and the symmetric/Rees normal-cone presentation.
The normal model is fixed to the inverse of the raw canonical construction,
with its projection and zero equations. The finite-local-freeness and symmetric
comparison typing facts include rank zero. The restriction map retains its
Noetherian, compactifiable and finite-type etale domain and actual normalized
adjunction mate. No declaration is moved, copied or redefined.

LeanSearch and LeanFinder with query "Canonical diagonal normal cone conormal
symmetric algebra model and diagonal purity base change comparison" each returned
eight results about diagonals, differential base change and cotangent complexes;
none is this interface. Mathlib grep for the seven declaration names returned
zero hits. The same search in WeilConjectures returned no hit, and in Sheaf found
the seven published declarations above. DAG grep found only the chart theorem's
suite record, not a separate definition node; blueprint_refs search "diagonal
chart" returned zero blueprint matches. The new node therefore binds the existing
Sheaf definitions with `existing: true`, as explicitly required by the return.
All actual search queries and returned names are recorded in mathlib_searches.

## Return repair

The independent review of immutable head `b287e4cfd4e3` returned H2, and otherwise
checked the mathematics as sound. The initial saved-packet dry run passed at
`3ee6af01d99`; passing mechanical checks did not resolve this review point.
The repair drops `lem-pur-diagonal-dnc-chart-normalization` from stmt_deps,
retains it in proof_deps for proof Step 5, and adds only
`def-pur-diagonal-dnc-chart-data` to the live item's twelve statement dependencies.
The new existing definition node lists exactly the seven declarations requested
by the return. The theorem's statement and six-step proof, all other item fields,
and the delivered Lean file are retained. There is no statement correction.
`Dnc.sourceSection`, `normalSection`, `sourceComparison`, `normalComparison`,
`pullComparison` and the family/fibre operations are already plain definitions
from base statement dependency `thm-pur-dnc-invariance`; no additional theorem
statement dependency is needed for them.

The self-check reread the seven signatures and docstrings and both node records:
the unit conversion is `chartDualizingUnit`; the inverse base-change/section/site
composite is `chartDiagonalAlpha`; the actual etale-adjunction restriction is
`chartSectionEtaleRestriction`; relative Spec with homogeneous Rees normalization
is `chartNormalModelRaw`; `chartDiagonalNormalBundle` supplies the rank-d and
invertible-symmetric-comparison typing facts; and `chartNormal_model_exists`
pins the selected `chartNormalModel` to the inverse raw model and supplies the
projection and zero equations used by beta. No equality from the chart theorem
is used to form the statement. Rank zero, empty schemes and all n >= 1 remain
included, as already checked by the independent immutable-head review.

Repair validation: prescribed scompile.py passed in sandbox mode (14.0 s) and
library mode (15.5 s), with no errors or non-sorry warnings. The new definition
node records the full chartDiagonalAlpha signature, including its two result-type
instance binders and final source/target; its seven existing declarations are
also checked by deliver2.py through an import-and-#check probe. Lean file SHA256:
`13a3402b055a43a840b7c00ffcd9844b6dc4f821c18e257476e99f3a6756a625`.

## Second reading by Q26

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
