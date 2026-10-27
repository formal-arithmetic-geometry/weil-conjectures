## Worker report

This delivery states `AlgebraicGeometry.ProEtale.FieldScalar.field_scalar_normalized_systems`
in `Sheaf.Paper.FieldScalarNormalizedSystems`. The sole postponed proof is this
named theorem; its docstring gives the source and the complete six-step proof.
Every helper definition has real data. The exact-system interface is in
`Sheaf.Paper.FieldScalarSystemData`; the reduction interface is in
`Sheaf.Paper.FieldScalarReductionData`. The auxiliary structures package the
conclusions being asserted, and are not assumptions of the theorem. No definition
selects a scalar functor or comparison from this theorem.

Hypotheses and objects:

- `P : WeilConjectures.PurityFiniteSetting` supplies the fixed finite-field datum,
  its algebraic closure, the coefficient prime and the inequality with the
  characteristic. `Family P.coefficients.l T` quantifies over finite-dimensional
  extensions `E,F` of `Padic P.coefficients.l` and the actual algebra homomorphism
  `ι : E →ₐ[Padic l] F`. Thus E is not restricted to a chosen presentation of a
  subfield of the coefficient closure.
- `X,Y`, their `Over` instances, `LocallyOfFiniteType`, `QuasiCompact`, and
  `IsSeparated` instances render separated finite-type schemes over that closure.
  `f`, `f.IsOver`, `SmoothOfRelativeDimension d f`, `IsSeparated f`, and `d : ℕ`
  render the specified smooth separated morphism of pure nonnegative dimension.
  The conclusion is quantified over `T = X ∨ T = Y`.
- `spCoefficientCommRings`, `spCoefficientTowers`, and
  `spDerivedCoefficientTowers` are the recorded varying-ring tower objects and
  ordinary derived categories, not diagrams in derived categories. As in their
  recorded definitions, Lean index `n : ℕ` denotes positive level `n+1`.
- `DA,DB : SpCoefficientTowersAbelian` and `RA,RB : SpReductionTower` are the
  existing normalized presentations of these categories and reductions. The
  result is stated for every such presentation. Their existence is supplied by
  the recorded dependency theorems, not added as a geometric hypothesis.
  The small pro-etale site retains object universe `u+1` and morphism universe `u`.

Conclusions, clause by clause:

- `Coefficients.quotient_mk` fixes the coefficient homomorphism on every residue
  class to `integralScalarIntegerInclusion`. `tower` is a natural transformation
  of whole quotient-ring towers, and `tower_app` fixes it to the actual constant
  quotient homomorphism. `integral_projection` fixes the completed coefficient
  map against every quotient projection. `spIntegralSectionRing` and the
  normalized coefficient isomorphisms of `RA,RB` supply the recorded inverse
  limit coefficient rings.
- `ExactExtension.basis_expansion` gives one integral basis with unique
  coordinates and relative rank `degree = [F:E]` for the indicated inclusion.
  `quotient_basis` uses the reductions of exactly those basis vectors at every
  positive level. `Coordinates.integral` gives the completed sheaf basis;
  `integral_column` identifies its columns with the same constant integral
  vectors. `coordinates_column` identifies the ordinary tower columns with
  reductions of precisely this basis.
- `ExactExtension.ordinary`, `level`, and `transition` describe sheafified tensor
  extension on entire strict systems: the transition is `t(x) tensor q(b)` for
  every inequality of indices, including equality and composites. Additivity,
  finite-limit preservation, and finite-colimit preservation assert exactness.
  The `restriction` functor retains the underlying local sections and transitions
  (`restriction_sections`, `restriction_transitions`). The natural isomorphism
  `coordinates` identifies its composite with extension with one finite power
  of the identity on the actual tower category. `Coordinates.derived` gives the
  corresponding finite sum on the ordinary derived category.
- `ExactExtension.derived`, its universal localization `counit`, and
  `computes_all` say that extension on the unbounded ordinary derived category
  is termwise extension on every complex. `derived_level` identifies its level
  values with the existing derived scalar models `DA.scalar`. Thus it is the
  whole-system scalar extension C_T, not an unconstrained functor with matching
  object values.
- `normalized` asserts preservation of the existing
  `spNormalizedConstructibleTorTowers` predicate. `support_preserved` and
  `tor_preserved` quantify over each pair of integer endpoints and preserve
  precisely that common interval at all positive levels. They do not merely
  assert that some enlarged interval exists.
- `integralScalar` is the existing scalar model for the specified completed
  coefficient homomorphism; its `model.T` is C-hat. `ReductionComparison.isoDerived`
  has exactly the functors C-hat followed by red_S and red_R followed by C_T.
  It is a natural isomorphism with values in the ordinary derived category of
  entire strict B systems, for every integral derived object. Naturality therefore
  includes all derived morphisms, not only those visible at the levels.
- `OrdinaryComparison.iso` is already a natural isomorphism of whole strict
  system functors. `forward` sends `(x tensor s) tensor b` to
  `(x tensor 1) tensor projection(s)*b`; `inverse` sends
  `(x tensor a) tensor b` to `(x tensor 1) tensor image(a)*b` on the other side.
  These are the common multiplication formula and insertion-of-one inverse under
  the single-tensor identification. `ReductionComparison.representative` fixes
  the derived comparison by this very cochain map and the existing universal
  counits on K-flat representatives. It therefore asserts the displayed
  double-derived-tensor associativity at every level while retaining every
  transition before localization.
- `Family.identity` supplies `Identity`: multiplication unitors before
  localization, their universal-counit representative equations, and the actual
  derived reduction square. `Family.successive` supplies `Successive` for
  E → F → L and their composite. Its integral and whole-system compositors are
  normalized on tensor generators by multiplication; `Compositor.representative`
  fixes their derived maps. `Successive.square` is the reduction coherence
  equation for these same maps. The selected bases need not be multiplicative
  under field composition; the canonical scalar comparisons are compositional.
- `Family.cofinal` gives a positive integer h and unit a with ell = a*varpi^h
  and `(ell)^n = (varpi)^(h*n)` for every n, for each coefficient field. No
  unramifiedness hypothesis is present.

Dependency declarations used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public
  coefficient constructions: `Padic.coefficientExtensionIntegers`,
  `Padic.coefficientExtensionUniformizer`, `Padic.finite_coefficientExtensionRing`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`:
  `AlgebraicGeometry.SmoothOfRelativeDimension` and the usual finite-type,
  separated and over-scheme notions.
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients` is the recorded
  general setting vocabulary; the actual categories in this item are its
  recorded pro-etale tower specializations below, rather than a second copy of
  the etale derived category.
- `Sheaf.Paper.SmoothPurityCoefficientTowers`:
  `spEllIdeal`, `spCoefficientTowers`, `spCoefficientConstantQuotient`.
- `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`:
  `spCoefficientCommRings`, `SpCoefficientTowersAbelian`,
  `spCoefficientEvaluation`, and its canonical `scalar` assignment.
- `Sheaf.Paper.SmoothPurityNormalizedTowers`:
  `spDerivedCoefficientTowers`, `spDerivedCoefficientEvaluation`,
  `spNormalizedConstructibleTorTowers`.
- `Sheaf.Paper.SemilinearDerivedSections` and its public scalar-model interface:
  the sheafified scalar models, `systemModelTmul`, and ordinary/derived universal
  counits. The recorded semilinear-derived-sections theorem supplies the
  whole-system interpretation, rather than replacing systems by their levels.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: the recorded twist
  conventions are publicly imported; no twist appears in this node's formula.
- `Sheaf.Paper.SmoothPurityReductionTowerNormalized`:
  `spIntegralSectionRing`, `spIntegralSectionModules`, `SpReductionTower`,
  `spIntegralReductionScalar`, `spTowerLocalization`, `spStrictTransitionSection`.
- `Sheaf.Paper.IntegralScalarExtensionWellDefined`:
  `WeilConjectures.integralScalarIntegerInclusion` and the already constructed
  constant-to-completion morphism (via its public coefficient API).
- Mathlib finite products and exact-functor descent supply `Functor.pi'`,
  `Pi.functor`, `Pi.lift`, and `Functor.mapDerivedCategory`.

Edge cases checked before and during the statement reading: identity field
inclusion (rank one) has explicit multiplication normalization; ramified
extensions are covered by ell powers without a false common-uniformizer
assumption; the empty scheme and zero complexes require no nonemptiness or
nonzero hypotheses; Lean level zero means exponent one, not the zero quotient;
all positive levels and all index inequalities are retained; degenerate and
empty cohomological intervals are preserved literally; neither normalization
nor constructibility is required of the arbitrary integral input K; composite
field extensions use their actual algebra-homomorphism composite. The same
universe u accommodates all scheme and coefficient fields while preserving the
site's distinct object and morphism sizes.

Searches performed:

- `msearch.py ... leanfinder` with "Finite field extension scalar extension
  normalized strict coefficient towers reduction canonical natural isomorphism":
  normal-closure and integral-restriction results, no whole-tower theorem.
- `msearch.py ... loogle` with `ModuleCat.extendScalars`: found the ordinary
  module scalar extension, no normalized strict-system reduction comparison.
- `msearch.py ... grep` with `extendScalars|mapDerivedCategory` in
  `CategoryTheory`: found generic scalar/descent primitives, no matching item.
- `msearch.py ... leansearch` with "finite free scalar extension normalized
  quotient systems integral reduction towers": finite-module and ideal-quotient
  results, no exact whole-system theorem.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the item id: only a
  blueprint documentation reference in `PurSequenceKFlatComparisonShifts`,
  not a declaration of this result. Scalar/normalization/reduction searches
  found the recorded coefficient, scalar-model, and reduction interfaces used
  here, and the finite-free scalar calculus proof dependencies, not this theorem.

No statement correction, disputed statement, or repaired dependency module is needed.
Two definition nodes split the interface into separately compiled modules. The helper records belong to the two new definition nodes and the main theorem's
coherence package; each module lists its declarations in its owning lean record. The source read is
`literature/blueprint/latest/blueprint/sec-smooth-purity/` followed by
`sk-lem-sp-field-extension/sk-lem-sp-field-extension-towers.proof.md`, paragraph (1),
not the dated snapshot named by the historical source metadata.

## Second reading by Q117

No independent second worker was started, as the dispatch brief prohibits it.
Q117 reread the node and this statement clause by clause. The review specifically
checked that the scalar functors are fixed by their local tensor descriptions
and universal derived counits, that the comparison lives in the derived
category of whole strict systems, and that identity and successive-field
coherence are actual equations. The initial draft lacked the explicit identity
and successive-extension squares; these were added. Compiler feedback also
required an explicitly sized sheafification instance and additivity projection
instances. These changes affect elaboration only and add no hypothesis. The
maintainer's independent delivery review remains the independent review.

## New nodes

`def-sp-field-scalar-system-data` defines the exact scalar-extension data and its
basis/restriction/derived-coordinate normalization in
`Sheaf.Paper.FieldScalarSystemData`. Its source is paragraph (1) of the latest
field-extension-towers proof. It asserts no existence theorem. The helper notions
are precisely those used by this item's conclusion. LeanSearch returned eight
algebraic basis/base-change declarations (including `Algebra.TensorProduct.basisAux`
and `Module.Basis.smulTower`), Loogle returned no matches for the queried interface,
and Mathlib grep returned no `ExactExtension`, `ReductionComparison`, or
`systemModelTmul`. Project/DAG grep found unrelated `Coordinates` records but no
field-scalar system data. Blueprint search returned zero matching nodes, and its
ancestor query returned `det-sp-field-extension-towers`. The existing scalar
models and tensor generators are reused.

`def-sp-field-scalar-reduction-data` defines the comparison, its local forward and
inverse normalizations, its K-flat cochain-counit equation, and completed/derived
basis coordinates in `Sheaf.Paper.FieldScalarReductionData`. It uses the previous
node and the existing reduction interface; it asserts no existence. It has the
same source and the same three search kinds/results as recorded in its JSON.
Neither existing generic scalar association nor levelwise tensor results package
this normalized isomorphism of whole strict-system functors. These two modules
were separated after the original combined file exceeded the fixed compiler
limit; no mathematical clause was removed or changed.
