## Worker report

The module `Sheaf.Paper.LisseDenseOpenRecovery` states
`AlgebraicGeometry.Scheme.isIso_curveLisseRecoveryUnit`. It concerns lisse
algebraic-coefficient sheaves, not just the finite-coefficient recovery theorem
already present upstream. All definitions have explicit data; the two postponed
proofs are named theorems with source references and proof docstrings.

Hypotheses and conclusion, matched to the node:

- The finite field and its characteristic are `D : WeilConjectures.FiniteFieldDatum.{u}`.
- The coefficient prime is `l : ℕ` with `[Fact l.Prime]`, and `hl : l ≠ D.p`.
- The chosen algebraic closure is `Qbar : Type (u + 1)` with `[Field Qbar]`,
  `[Algebra ℚ_[l] Qbar]`, and `[IsAlgClosure ℚ_[l] Qbar]`.
- The curve, source open, and morphism are the fields `c.C`, `c.U`, and `c.j` of
  `c : MiddleExtensionCurve D`, the dependency's existing bundle. This includes
  separatedness and finite type over the finite field, smoothness of `c.C.hom`,
  pure dimension one, an open immersion, and `c.dense : DenseRange c.j.left.base`.
  No additional geometric hypotheses are imposed.
- Lisseness on **all of C** is `F : c.whole.LisseSheaf l hl Qbar`. The real
  construction `c.whole` keeps C and its structure morphism and makes its source
  open C with identity immersion; it adds no requirement on the original j.
  Thus this is exactly the recorded `LisseAlgebraicSheaf` on C. Its noetherianity,
  absolute separatedness, and coefficient invertibility instances are supplied
  by the dependency, not assumed as new hypotheses.
- `curveLisseRecoveryStage` and `curveLisseRecoveryModel` extract the original
  coefficient pair and its actual integral model using `lisseAlgebraicPair` and
  `lisseCoefficientPairModel`. Localization preserves objects, so neither is an
  arbitrary choice from an existence assertion.
- The map η is `curveLisseRecoveryUnit`. Its integral diagram arrow is
  `curveLisseRecoveryDiagramUnit`, the unit of
  `(Etale.upperStarLowerStarAdjunction ... c.j.left).whiskerRight ℕᵒᵖ`.
  Its component at n is the actual unit on that coefficient sheaf.
- The target is ordinary `j_*j^*F`: `curveLisseRecoveryDiagram` applies the
  existing `Etale.upperStar` and **ordinary** `Etale.lowerStar` at every level.
  `curveLisseRecoveryRealization` uses the existing
  `middleExtensionLevelFunctor ... (𝟙 c.C.left)` for site/coefficient transport,
  ordinary `lim`, and `DerivedCategory.singleFunctor _ 0`. The identity lowerStar
  in this realization only identifies C with itself; the target has exactly the
  ordinary j_* already specified in its diagram. There is no Rj_* here.
- `curveLisseRecoveryRealization_mem` is the named proof obligation needed to
  put both explicitly constructed degree-zero objects in the dependency's
  constructible-complete integral stage. It does not choose or alter either
  object's data. Its docstring gives the finite-level unit/gluing argument,
  transition compatibility, and the three integral-stage membership conditions.
- `curveLisseRecoveryPairFunctor` is existing `pbcStageLocalization` followed
  by existing `pbcScalarSystem.ι`, with the coefficient-stage conventions of
  `c.CoefficientCategory`. `curveLisseRecoveryUnit` maps the constructed arrow
  through that functor. Thus its endpoints are the ordinary sheaves interpreted
  in exactly the coefficient category specified by def-wf-middle-extension.
- “is an isomorphism” is `IsIso (curveLisseRecoveryUnit l Qbar c hl F)`.
  No assertion about every finite-level unit is added to the main conclusion.

Dependency declarations read and used:

- `Sheaf.Paper.CurveMiddleExtension`: `MiddleExtensionCurve`, `baseProperties`,
  `coefficientUnits`, `MiddleExtensionCurve.LisseSheaf`,
  `MiddleExtensionCurve.CoefficientCategory`, `middleExtensionLevelFunctor`.
- `Sheaf.Paper.LisseAdicSheaves`: `AdicIntegralDiagram`, `LisseIntegralSheaf`,
  `LisseAlgebraicSheaf`, `lisseAlgebraicPair`, `lisseCoefficientPairModel`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`,
  `Etale.lowerStar`, `Etale.upperStarLowerStarAdjunction`.
- `Sheaf.Paper.FiniteStagePairCategory`: `pbcIntegralStage`, `pbcAmbientStage`,
  `pbcStageLocalization`, `pbcScalarSystem`; its upstream
  `WeilConjectures.CategoryTheory.StageSystem.Basic`: `StageSystem.ι`.
- Mathlib `CategoryTheory.Adjunction.whiskerRight`,
  `CategoryTheory.Functor.whiskeringRight`, `CategoryTheory.Limits.lim`,
  `DerivedCategory.singleFunctor`, and `ObjectProperty.homMk`.

All stated proof-dependency modules are imported, including normal decomposition,
finite etale trivialization, etale normal components, etale restriction, and
constant-sheaf recovery on a normal integral scheme. Pure proof imports are
non-public. No dependency record needed repair.

Edge cases checked: the empty curve and empty open of the empty curve; identity
j; disconnected curves (density meets every nonempty component); zero sheaves;
coefficient level n=0 in the diagram, which denotes the first positive quotient
by the recorded n+1 convention; torsion in a lattice; and systems requiring
varying finite trivializing covers at different levels. Nothing asserts a single
finite cover trivializes an entire l-adic sheaf. The only prime restriction is
the standing l≠p. The universe is exactly the existing scheme/coefficient size
convention; no universe equality is added.

Searches (raw service results are also in searches.jsonl):

- msearch LeanFinder: “A lisse l-adic sheaf on a smooth curve is recovered by
  ordinary direct image of its restriction to a dense open”. Eight results were
  structure-module restriction or counit results, not this statement.
- msearch Loogle: `"upperStarLowerStarAdjunction", "IsIso"`: zero results.
- msearch LeanSearch: “A lisse adic sheaf is recovered from a dense open of a
  normal smooth curve by the adjunction unit”. Eight results were general
  sheafification and adjunction unit formulas, not recovery for lisse sheaves.
- msearch grep: `lisse|isIso_unit_upperStarLowerStarAdjunction` in
  Mathlib/AlgebraicGeometry: zero results.
- rg in upstream WeilConjectures for the item id found
  `EtaleCohomology/Purity/RealSheaves/Boundary.lean`. Read its full signatures:
  `Scheme.isIso_unit_upperStarLowerStarAdjunction` assumes a **finite** ring Λ
  and a finite locally constant sheaf; it does not state recovery for the
  recorded lisse Qbar category. The older audit module path is absent locally.
- rg in project `lean/Sheaf` for lisse recovery and units found the existing
  LisseAdicSheaves coefficient constructions and CurveMiddleExtension, but no
  algebraic-coefficient recovery unit or theorem. The upstream names index was
  also checked. No second definition of the existing functors/categories is used.

The current main-20261015 blueprint lemma and its unit were read. They make the
same recovery claim. No statement correction and no disputed statement.

## Second reading by Q132

Author's separate self-check, as required by the dispatcher workflow; this is
not an independent maintainer review. Reopened the JSON statement and complete
Lean module. Checked the finite field, l≠p, chosen closure, bundled geometric
hypotheses, and whole-curve lisse binder against the node. Followed the map from
the levelwise adjunction unit through the ordinary realization, full-subcategory
inclusion, rationalization, and stage inclusion. The target uses ordinary
lowerStar, with no higher direct-image truncation. Checked that membership
proofs supply only properties of predetermined objects, never their data.
Checked the empty and disconnected cases and that the proof plan uses possibly
different covers at each finite level. The initial draft's unqualified
whiskeringRight was corrected to Functor.whiskeringRight during compilation.
The final signature asserts only invertibility of the algebraic-coefficient
unit; no mismatch with the node was found.
