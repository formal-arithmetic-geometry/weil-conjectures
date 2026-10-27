## Worker report

The module `Sheaf.Paper.DerivedPoincarePairing` defines the finite, completed integral,
rational and common-stage derived Poincare pairings as morphisms of coefficient
complexes, and records the perfectness predicate. All data are constructions;
there are no new postponed theorems, `sorry`s, arbitrary evaluation maps,
arbitrary trace maps, or choices from undetermined existence assertions.
The source read is the current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-identification/def-sf-pairing.md`,
including its `blueprint_update` on the assigned DAG node. The statement is unchanged.

The four main declarations are
`SixFunctorDatum.finitePoincarePairing`, `.integralPoincarePairing`,
`.rationalPoincarePairing`, and `.commonStagePoincarePairing`, all in namespace
`WeilConjectures`. `IsSfPerfectPairing` is the final perfect-pairing convention.
The remaining declarations are coordinate constructions belonging to this definition,
listed individually in `lean.declarations`.

Hypotheses and clauses are rendered as follows.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Finite-field datum, algebraic closure and distinct coefficient prime | `D : FiniteFieldDatum.{u}`, `C : D.CoefficientDatum`; these are precisely the parameters of `SixFunctorDatum D C E ...`. |
| Finite coefficient extension and its valuation-ring, uniformizer and quotient constructions | `E : Type u`, `[Field E]`, `[Algebra (Padic C.l) E]`, `[FiniteDimensional (Padic C.l) E]`, and the existing `Padic.coefficientExtensionRing`; no second ring or uniformizer is constructed. |
| Positive finite exponent | `m : ℕ`, exponent `m + 1`, proof `Nat.succ_le_succ (Nat.zero_le m)`; this covers exactly all `n ≥ 1`, including `n = 1`. |
| The four coefficient categories and six operations | `S : SixFunctorDatum ...`; finite `S.finite`, integral `S.higher.integral`, rational `S.higher.rational`, common `S.closure.commonStage`. |
| Fixed coherent orientation | `O : SfOrientationDatum S`; the traces use its actual components, not an independently chosen purity isomorphism. |
| Finite-type k-scheme and structure morphism | `X : SixFunctorSpace D`, with its existing finite-type property; the map is always `sixFunctorStructure X`, whose underlying map is `X.obj.hom`. |
| Separated | `[IsSeparated X.obj.hom]`. |
| Smooth, of pure dimension d | `d : ℕ`, `[SmoothOfRelativeDimension d (sixFunctorStructure X).hom.left]`, and `_hpure : X.obj.left.IsPureDimension d`. On a smooth geometrically connected scheme the relative-dimension formulation expresses the stated smooth/pure-dimension condition and is the orientation dependency's interface. |
| Geometrically connected | `_hconnected : GeometricallyConnected X.obj.hom`. |
| Proper OR smooth separated geometrically connected finite-type model over k₀ | `_hglobal : SfPairingGlobalGeometry X`; its first disjunct is `IsProper X.obj.hom`. Its second existential binds the model `X₀ : Over (Spec (.of D.k₀))`, all five geometric properties, and an isomorphism over k with the existing `Over.pullback` along `Spec.map (algebraMap D.k₀ D.k)`. The model need not be proper. |
| Constructible exceptional inverse image, with no admissibility restriction | The support/exceptional adjunction and orientation components are those of `S`, exactly as in the recorded orientation and normalized-trace dependencies. No admissibility or global-dualizability binder is introduced. |
| Compactification presentation | `c : Compactification (sixFunctorStructure X).hom.left` is the same presentation parameter as in the dependency cup and trace. It is not an assumption that the structure morphism is proper. |
| Bounded constructible finite-Tor K | The finite/integral input `K` is in the actual `S...finiteTorDomain X` full subcategory. The field-stage inputs use the top full subcategory of the recorded constructible category, as in the datum. |
| Coefficient dual | The four recorded `S.finiteCoefficientDual`, `.integralCoefficientDual`, `.rationalCoefficientDual`, `.commonStageCoefficientDual`, each at `op K`; the same internal Hom into the coefficient tensor unit is used. |
| Site-perfectness on K^∨ | `_hperfect` is respectively `IsFiniteCoefficientSitePerfect`, `IsIntegralCoefficientSitePerfect`, `IsSfRationalCoefficientSitePerfect`, or `IsGeneralAlgebraicallyClosedCoefficientSitePerfect`, applied to that recorded dual. It is not imposed on K. |
| Twist and shift | `sfPairing*Line` is the existing orientation line Λ_X(d)[2d], and `sfPairing*DualTwist` applies the existing finite-Tor/completed/rational/common tensor to K^∨ and this line. Thus the point complex is represented in the canonical shift-inside-the-line coordinates. |
| Point-complex source | The first factor is the point fibre of `S.support` on K. The second is the point fibre of `S.direct` on `sfPairing*DualTwist`. These are RΓ_c(K) and the canonical representative RΓ(K^∨ ⊗ Λ_X(d)[2d]) of RΓ(K^∨(d))[2d]. |
| First arrow | The existing `finitePairingCup`, `integralPairingCup`, `rationalPairingCup`, `commonPairingCup` apply the inverse canonical point tensorator and the datum's projection/pull-direct-counit composite. Their target is the point fibre of support of the actual stage tensor. |
| Evaluation as transpose of the identity | `sfPairingTwistedEvaluation` uses `M.evaluation`, the counit of the recorded tensor-Hom adjunction, preceded by the braiding for its right-tensor convention. This is the argument-first transpose of the identity of K^∨. |
| Twisted evaluation | The same helper explicitly composes inverse associator, tensor of evaluation with the identity of the shifted line, and left unitor. `sfPairing*Evaluation` converts the actual stage tensors to these closed coordinates using canonical inverse-transpose maps. |
| Canonical coordinate maps | `sfPairingTensorComparison` is the inverse normalized partial transpose of the closed adjunction unit. The finite counterpart uses `finiteIntrinsicClosed.transpose`. Both are formulas, not arbitrary supplied comparisons. The dual-twist source itself uses the actual recorded tensor, not the closed presentation's tensor. |
| Second arrow | Each pairing actually applies support and then the point-fibre functor to `sfPairing*Evaluation`. |
| Normalized smooth trace | The final factor is the corresponding `*NormalizedSmoothTrace O X d c`. Its definition applies point fibre to support of O's orientation followed by the SAME exceptional-adjunction counit of S, then the published point unit isomorphism. |
| Target Λ | Each normalized trace ends in the tensor unit of the corresponding module-derived category, i.e. the coefficient ring/field in degree zero, rather than a selected summand of global sections. |
| Perfect pairing of arbitrary point complexes | `IsSfPerfectPairing M s C D b` supplies the MonoidalClosed structure from M's existing adjunction and the braiding, then uses upstream `CategoryTheory.MonoidalClosed.IsPerfectPairing b`. Its sole condition is invertibility of the adjoint D → RHom(C, Λ). No separate perfectness binder on C or D is introduced. |

The shifted-line presentation retains the full complex, not just its degree-zero
or top-degree cohomology. At integral coefficients its line is the existing
`sfOrientationIntegralLineOn`, whose `sfOrientationIntegralShiftIso` identifies
the one-term representative with the degree-zero Tate line shifted by `2*d`.
The finite line is its recorded reduction; the rational line is its localization;
the common line is its recorded base-stage inclusion. Tensor and direct-image
shift identifications read this as precisely the source and intermediate complexes
in the node's display. Evaluation is written with this same line throughout,
so moving the even shift does not change its sign or the selected trace.

Dependency declarations read and used:

- `Sheaf.Paper.SixFunctorDatum`: `SixFunctorDatum`, `SixFunctorClosedDomain`,
  `sixFunctorDomainHom`, its closed/domain fields and coefficient comparisons.
- `Sheaf.Paper.SixFunctorOrientationFamily` (and its public orientation modules):
  `SfOrientationDatum`, the four `SixFunctorOrientation` components,
  `sfOrientationIntegralLineOn`, `sfOrientationReducedLine`, and
  `sfOrientationIntegralComplex_mem`.
- `Sheaf.Paper.SixFunctorDualNotation`: the four coefficient-dual functors and
  their common `sixFunctorCoefficientDual` construction.
- `Sheaf.Paper.SixFunctorMixedSupportCupProduct`:
  `sixFunctorStageMixedSupportCupProduct` and the four stage cup declarations;
  the point-coordinate helpers below use exactly projection then the tensor of
  the pull/direct counit, as these declarations do.
- `Sheaf.Paper.PairingData`: `pairingPointIdentifications`, `pairingFiniteInput`,
  the four point-complex cup maps, and the four `*NormalizedSmoothTrace` maps.
  Only its general-X helpers are used: its narrower model-based `pairingData`
  packaging is not imposed on X. This already-landed node is added to stmt_deps.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteIntrinsicClosed`,
  `constructibleIntegralTensor`, `rationalDerivedTensor`,
  `commonStageDerivedTensor`, and their permitted internal Hom constructions.
- `Sheaf.Paper.DerivedAutomorphismHomEvaluation`: `PodPartialClosed`,
  `podIntegralClosed`, `podRationalClosed`, `podCommonClosed`; these have the
  ordinary-to-completed-unit, scalar-localization and common-stage normalizations.
  Its already-landed node is added to stmt_deps for these normalized transposes.
- `Sheaf.Paper.IntegralResidueTor`: `integral_residue_tor` identifies integral
  constructibility with its finite-Tor predicate, supplying the membership proof
  for the actual completed dual-twist tensor. Its landed node is added to stmt_deps.
- `Sheaf.Paper.SitePerfectComplex`: the four exact site-perfectness predicates.
- `Sheaf.Paper.FiniteCoefficientPoint`: the actual point-fibre constructions;
  `pointFiniteSections` is applied by `Functor.mapDerivedCategory` in the finite
  composite. The higher-stage composites apply the corresponding existing fibres.
- `Sheaf.Paper.CommonStageCompactWeilCohomology` reexports the recorded ordinary
  and compact coefficient-cohomology definitions used to read those point images.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- Mathlib: `SmoothOfRelativeDimension`, `GeometricallyConnected`, `IsSeparated`,
  `IsProper`, `LocallyOfFiniteType`, `QuasiCompact`, `Over.pullback`, `Spec.map`.
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic`:
  `CategoryTheory.MonoidalClosed.IsPerfectPairing`, read with its full docstring
  and `isIso` field; this is reused rather than redefining perfectness. The
  existing `def-pod-perfect-derived-pairing` node is added to stmt_deps.

No new independent notion or dependency-record repair was needed. The four added
landed nodes were checked for paths back to `def-sf-pairing`; none has one.

Edge cases checked before and during elaboration:

- `m = 0` gives exactly exponent one; exponent zero is not admitted.
- `d = 0` retains the zero twist and zero shift, using the trace's actual unit
  normalization; for X = Spec k this is the unit evaluation/trace pairing.
- `K = 0` is allowed; no invertibility of its evaluation is assumed.
- The perfectness predicate on a zero pairing is not asserted; it remains the
  invertibility condition on its actual adjoint.
- Affine space over k₀ is admitted by the nonproper model disjunct. Arbitrary
  proper X over k uses the first disjunct without supplying a model.
- The empty scheme is excluded by geometric connectedness; the helper formulas
  themselves do not require nonemptiness or a choice of a geometric point of X.
- Uniform integral finite Tor is supplied by the published residue-Tor theorem,
  not an extra assumption on the tensor product.
- All universes and variables are explicit. The finite support map needs its
  category family and category instance explicitly specified to prevent Lean
  from leaving a coefficient-module universe metavariable under a maximum.

Searches actually made:

- msearch LeanFinder, `derived Poincare pairing compact support cup evaluation
  smooth trace`: eight generic/integration/Schwartz-related hits; no construction
  of this four-stage geometric pairing.
- msearch Loogle, `CategoryTheory.MonoidalClosed.curry`: generic currying and its
  identities, not the geometric composite.
- msearch grep, `poincarePairing|IsPerfectPairing|smoothTrace`, subdirectory
  `CategoryTheory`: no Mathlib hit for the geometric construction.
- msearch LeanSearch, `derived Poincare pairing as compact-support cup product
  evaluation and normalized smooth trace`: eight hits, consisting of topological
  and linear pairings, root pairings, Petersson and Lp integration; no match.
- `rg` in `lean/WeilConjectures` for Poincare pairings found
  `SixFunctors/Etale/Derived/PoincarePairing.lean`. Its `Etale.poincarePairing`
  is an etale/fixed-coefficient construction, not this four-stage pro-etale one.
  Its tensor-closed perfect-pairing dependency is reused.
- `rg` in `lean/Sheaf` for Poincare pairing, trace, cup, transpose and evaluation
  found the published `PairingData`, the normalized partial closed adjunctions,
  and the coefficient-unit and orientation-line comparisons used above. No
  already-stated whole-item declaration covered this node's four stages and
  proper-or-model geometry with site-perfectness assumed on the coefficient dual.
- The node id search in `lean/WeilConjectures` found the upstream finite-etale
  discussion; the exact specialized signatures were read before rejecting it as
  a whole-item match.

Validation: the complete module passed `scompile.py NA def-sf-pairing` in both
sandbox and library-module coordinates, with no errors or warnings. The required
`deliver2.py --no-push` preflight and final delivery are run after this report.

## Second reading by NA

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
