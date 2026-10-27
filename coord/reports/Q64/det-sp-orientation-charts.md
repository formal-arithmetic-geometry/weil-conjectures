## Worker report

The module `Sheaf.Paper.DiagonalOrientationCharts` states
`WeilConjectures.PurityFiniteSetting.diagonalOrientationCharts`, with proof `sorry`.
Its helper `DiagonalOrientationChartsConclusion` is the fully written proposition,
not a new coefficient object, orientation, or exceptional functor. Its body contains
only the published constructions and ordinary Lean terms; no data is postponed.
The item's node changes only in `lean`.

Source read: the current blueprint
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-orientation/sk-prop-sp-orientation-charts.md`
and its `.proof.md`, and the complete current DAG statement and five-step reassembly.
The reassembly is reproduced step by step in the theorem docstring. In particular,
no absolute separatedness assumption has been imported from an affine-target proof.

Hypotheses and clauses, matched to Lean:

| Node | Lean rendering |
| --- | --- |
| Fixed algebraic closure of a finite field, coefficient prime different from its characteristic | `P : PurityFiniteSetting.{u}` carries `P.field` and `P.coefficients`, with their published finite-field and coefficient data. |
| `E = Q_l` | `_hE : P.extension = ⊥`; the bottom intermediate field is the base field inside the fixed coefficient closure. |
| Positive level `n`, uniformizer `l`, finite coefficient `Z/l^n` | `P.level`, `P.level_pos`, and the existing quotient `P.Ring` and its standard size lift `P.Coefficient`; at the bottom coefficient field this is the prescribed finite quotient. The Tate exponent is the existing `P.diagonalExponent = l ^ P.level`. No new coefficient ring is defined. |
| Finite-type `k`-schemes `X,Y` and a `k`-map `f` | `{X Y : Scheme.{u}}`, `aY : Y ⟶ Spec (.of P.field.k)` with `[LocallyOfFiniteType aY] [QuasiCompact aY]`, and the structure map `f ≫ aY` on `X`. Since `f` is finite type, this is a finite-type structure map on `X`; it imposes no restriction on a morphism between the stated `k`-schemes. |
| `f` smooth, separated, finite type, pure relative dimension `d >= 0` | `(d : ℕ) (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [SmoothOfRelativeDimension d f]`. |
| Open subscheme `j : U ↪ X` | `U : X.Opens`, with its actual scheme `U.toScheme` and inclusion `U.ι`. This ranges over all open subschemes. |
| Étale coordinate map `e : U → A^d_Y` | `(e : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) Y) [Etale e]` uses the recorded Mathlib affine-space definition, with all `d` coordinates. |
| Coordinate map over `Y` | `w : (e ≫ (affineTraceAffineSpaceIso Y d).inv) ≫ affineTraceProjection Y d = U.ι ≫ f`. This is exactly the over-`Y` equation through the canonical coordinate-preserving identification with the ordered tower; there is no arbitrary affine-space identification. |
| No absolute separatedness of `Y` | There is no `[IsSeparated aY]`, `[Y.IsSeparated]`, or affineness assumption on either `Y` or `U`. The separatedness of the coordinate map follows from that of its composite, using `w` and `IsSeparated.of_comp`, inside the proposition. |
| Actual constructible exceptional inverse image and dualizing object | `P.diagonalDualizing f` and its canonical presentation `P.diagonalDualizingComparison f`. The former is the finite exceptional composite applied to the coefficient unit; the latter uses the comparison adjunction unit, not an arbitrary isomorphism. |
| Specified diagonal orientation `theta_f` | `P.diagonalDualizingObject d f aY`, the existing unique normalized orientation from `thm-pur-diagonal-dualizing-object`. It is not an orientation supplied by the caller. The node's alpha/DNC/beta construction specifies this very declaration; those factors are not redefined. |
| Restrict the orientation by `Lj*` | The equality's left side is `(ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) U.ι).leftDerivedFunctor.map (P.diagonalDualizingObject d f aY).inv`. This is the inverse-arrow form of the node's restricted orientation equality. |
| Under the canonical open identification `Lj* omega_f ≅ omega_(f restricted U)` | On the right, the inverse of `P.diagonalEtaleLocality N U.ι f` expresses this identification after passage through `P.diagonalDualizingComparison f` and `Dnc.pullComparison`. |
| `omega_(pe) ≅ Le* omega_p` by exceptional composition and `Re! = Le*` | The factors `P.diagonalEtaleLocality N v (affineTraceProjection Y d)` and `P.diagonalDualizingCongr w`, where `v = e ≫ (affineTraceAffineSpaceIso Y d).inv`, are exactly these canonical exceptional-composition/étale-adjoint identifications. In inverse-arrow form they go from pulled-back affine dualizing object to `omega_(f restricted U)`. |
| Pullback of the integration-normalized affine orientation | `(Etale.ordinaryFinitePullback P.Coefficient v).map (P.diagonalAffineMate t D Y (P.diagonalExponent_isUnit aY) d)`. `diagonalAffineMate` is the actual exceptional transpose of the ordered affine trace; in the inverse orientation equality the trace's transpose occurs in its original direction. |
| Common target `Lambda_U(d)[2d]` and canonical Tate pullback | `P.diagonalTwistEtale` and `P.diagonalTwist` are the existing shifted `d`-fold root-line objects. The two `Etale.vectorIntegrationBaseCoefficientPullback` factors give their canonical restrictions along `U.ι` and `v`. |
| Equality in the specified pro-étale derived category | The ordinary composite is mapped by `(ProEtale.comparisonUpperStar ... U.toScheme).mapDerivedCategory.map`. The two `Dnc.pullComparison` factors and the pulled-back `diagonalDualizingComparison` make its source and target literally those of the left side. This is equality of morphisms, not just isomorphic objects or equal cohomology. |
| Same ordered-coordinate and trace normalization as projection purity agreement | The affine factor is the published ordered Kummer-normalized integration counit mate, exactly the trace-transpose description in the node and in `lem-pur-projection-purity-agreement`. That module is imported for the normalization agreement used in proof step 4. |

The displayed equality is obtained by inverting the node's orientation equality.
On the right, start with the pulled-back Tate object, apply Tate restriction to `U`,
inverse Tate restriction along `v`, the pulled-back affine trace adjunct,
exceptional locality for `v`, congruence by `w`, inverse open locality for `U.ι`,
and the canonical inverse site/pullback comparisons. Its result is a map to
`Lj* omega_f`, with exactly the same source as `Lj* theta_f^{-1}`. Thus inversion
and cancellation recover precisely the forward equality asked for by the node.
No scalar, sign, chosen map, or unspecified isomorphism replaces a canonical arrow.

The normalized presentation data `t`, `D`, and `N` are universally quantified
inside the conclusion, just as in the dependency's
`DiagonalOrientationNormalization`. They are not hypotheses asserting the desired
comparison and are not an exceptional-adjoint admissibility assumption. The
published normalized root/trace and compact-support presentations give such data;
the statement applies to every such presentation. Noetherianity and the needed
compactification instances are constructed in the definition from the stated
finite-type hypotheses. There is no separate Noetherian, compactification,
quasi-compactness-of-an-open, or separatedness-of-a-chart hypothesis.

Dependency declarations read and used:

- `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting`,
  `WeilConjectures.PurityFiniteSetting` and its actual finite coefficient quotient.
- `def-weil-scheme-morphism-properties` is the recorded convention node, not a
  declaration to duplicate. Its relevant Mathlib properties are `IsSeparated`,
  `LocallyOfFiniteType`, `QuasiCompact`, and open immersion for `U.ι`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.SmoothOfRelativeDimension`; its full signature and affine-local
  standard-smooth docstring were read. `Smooth` is implied by this predicate.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`; the recorded affine-local signature was read.
- `def-sbc-affine-space` is a Mathlib leaf with no `lean` record:
  `Mathlib.AlgebraicGeometry.AffineSpace`, `AlgebraicGeometry.AffineSpace` and its
  projection. `affineTraceAffineSpaceIso` from the already-published
  `Sheaf.AlgebraicGeometry.AffineTraceTower` is the canonical coordinate map's
  isomorphism. Its full definition and coordinate formulas were read.
- `def-weil-exceptional-inverse-image`: the recorded
  `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` and its
  `ConstructibleExceptionalCoefficients.System` were read. The fixed finite-stage
  arrows needed here are precisely `diagonalDualizing`,
  `diagonalOrdinaryDualizing`, `diagonalDualizingComparison`,
  `diagonalEtaleLocality` and `diagonalDualizingCongr`, publicly exposed by
  `Sheaf.Paper.PurityDiagonalDualizingObject`. They use the existing
  `ProEtale.sfFiniteExceptionalAt` and ordinary exceptional adjoint.
- `def-weil-derived-pullback-tensor-hom`: the recorded
  `Sheaf.Paper.DerivedPullbackTensorHom` and finite operations are imported.
  Actual pullback is `ProEtale.upperStar ... |>.leftDerivedFunctor`, with
  `Etale.ordinaryFinitePullback` for its ordinary presentation. The canonical
  comparison is `Dnc.pullComparison` from `Sheaf.Paper.PurityDncInvariance`.
- `def-coefficient-twists-detailed`: the recorded
  `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` was read and imported.
  Its already-published fixed positive finite presentation
  `Sheaf.Paper.FixedFinitePositiveCoefficientTwist` supplies `diagonalExponent`,
  `diagonalTwistEtale`, `diagonalTwist`, and `diagonalExponent_isUnit` used by
  the dependency's orientation. The latter module is reexported by the orientation
  interface. No replacement twist is introduced.
- `thm-pur-diagonal-dualizing-object`:
  `Sheaf.Paper.PurityDiagonalDualizingObject`,
  `existsUnique_diagonalDualizingObject`, `diagonalDualizingObject`,
  `DiagonalOrientationNormalization`, and the canonical arrow definitions above.
- `lem-pur-diagonal-base-change`:
  `Sheaf.Paper.PurityDiagonalBaseChangeCompared`, `comparedDiagonalBaseChange`,
  and its explicit `diagonalComparedRestriction` construction, read and imported.
- `thm-pur-dnc-invariance`: `Sheaf.Paper.PurityDncInvariance`,
  `Dnc.existsUnique_dncInvariance`, `Dnc.sourceComparison`, `Dnc.normalComparison`,
  and the actual `Dnc.pullComparison`, read in full and imported.
- `cor-pur-vector-bundle-purity`: `Sheaf.Paper.VectorBundlePurity`,
  `vectorBundlePurity` and `VectorBundlePurityConclusion`, read and imported.
- `def-pur-section-invariant`: `Sheaf.Paper.PuritySectionInvariantIntrinsic`,
  `sectionInvariantFinite`, with its intrinsic dualizing and pullback definitions,
  read and imported. The section-invariant factors already belong to the specified
  diagonal orientation, not additional inputs of this chart statement.
- `lem-pur-projection-purity-agreement`:
  `Sheaf.Paper.ProjectionPurityAgreement`, `projection_purity_agreement` and the
  intrinsic ordered affine comparison, read and imported. Its separated-target
  hypothesis is used only over the affine target opens in the proof plan.
- The stated proof dependency `det-sp-orientation-vector-bundle` is imported
  privately from `Sheaf.Paper.VectorBundleDiagonalOrientation`; its full-domain
  `vectorBundleDiagonalOrientation` and conclusion were read. The five newly split
  chart proof lemmas have no recorded module in the read snapshot, so there is no
  module to import for them. They are named individually in the proof docstring;
  they are proof prerequisites, not absent objects needed to type this statement.

Edge cases checked against the definitions and the source:

- `U = ⊥`: `U.toScheme` is empty. No nonempty or affine-source assumption occurs.
  Its étale coordinate map and all functorial pullbacks still have the displayed
  types. No dimension or maximum of an empty scheme is used.
- `d = 0`: `Fin 0` is empty, the ordered tower is `Y`, its projection is identity,
  and the zero-fold coefficient is the unit. The published affine counit is the
  identity adjunct. There is no positive-dimension restriction or coordinate choice.
- `n = 1` is included by `P.level_pos`. There is no ramification divisibility or
  additional lower bound. At the bottom coefficient field the exponent is `l^n`.
- Disconnected and nonseparated `X,Y`, and non-affine `U`, remain permitted.
  In particular, `e` need not be injective (an étale chart may be a disjoint union
  of coordinate copies); the statement requires only its actual over-`Y` equation.
- Any scheme universe `u` is allowed. Coefficients use the dependency's prescribed
  `u+1` lift and the actual small pro-étale site; no equality of independent site
  universes or restriction of test schemes was introduced.

Searches performed (the wrapper logs are retained in the sandbox):

- LeanSearch: `diagonal smooth purity orientation etale coordinate chart integration`:
  eight results, headed by `AlgebraicGeometry.IsEtale.instIsSmooth`, and generic
  formal-étale/smooth facts; no equality of the specified purity arrows.
- LeanFinder: `Compatibility of diagonal purity orientation with etale affine-space coordinate adjunction`:
  eight results, including `AffineSpace.map_appTop_coord`, standard étale presentations,
  and `IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`; none states
  the required equality.
- Loogle: `AlgebraicGeometry.Smooth, AlgebraicGeometry.Etale`:
  one hit, `AlgebraicGeometry.Etale.instSmooth`; not an orientation comparison.
- Mathlib grep via msearch: `orientation|dualizing|deformationToNormal` in
  `AlgebraicGeometry`: zero hits.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, and the upstream name
  index, for `orientation.*[Cc]hart|[Cc]hart.*[Oo]rientation|det-sp-orientation-charts`;
  direct grep of the item id in `lean/WeilConjectures`: no upstream exact statement.
  The source search for dualizing/orientation also found generic Verdier-duality
  statements, which do not identify the normalized coordinate arrow.
- The project has `chartOrientation_coordinate_formula_forward` in
  `Sheaf.Paper.DiagonalDncChartNormalization`. Its full signature requires both
  source and target to be affine and states an ordinary-site presentation equality
  for the restricted morphism. It does not state restriction from arbitrary `X`
  over possibly nonseparated `Y`, or the actual displayed pro-étale pullback arrow.
  `chartOrientation_etale_restriction` in that module expresses source locality,
  without the ordered affine integration comparison. Neither is an exact match.
  The existing `DiagonalOrientationNormalization` is a property of an ordinary
  presentation; the new theorem is the actual restricted pro-étale equality for
  the uniquely specified orientation, with all comparison maps retained.

No statement correction, new DAG node, dependency replacement, or disputed
statement is needed. The proposition introduces no separate mathematical notion.
The theorem's only proof is `sorry`; every other line is a definition or an
application of existing constructions and instances. The node's recorded signature
is copied verbatim from the delivered file. All lines of Lean have at most 100
characters and `autoImplicit` is disabled.

Validation: the final module compiled through `scompile.py` in both sandbox and
library modes without errors or warnings (47.0 s and 30.1 s respectively), under
the default per-file 60-second limit. The mandatory delivery preflight and compile
are run through `deliver2.py --no-push` before delivery.

## Second reading by Q64

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
