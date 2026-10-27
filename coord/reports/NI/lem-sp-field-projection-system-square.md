## Worker report

The delivery states the scalar projection square as an equality of actual morphisms
in the ordinary unbounded derived category of module sheaves on the ringed sequence
site. The published section-preserving equivalence identifies this with strict
varying-coefficient towers. There is one postponed theorem,
`AlgebraicGeometry.ProEtale.FieldShriekSystem.field_projection_system_square`.
Definitions have real data; no proof is supplied in stage 2.

Clause matching:

- The global datum is `P : PurityFiniteSetting.{u}`. Its `field` is the recorded
  finite-field datum and its `coefficients` contains the prime distinct from the
  characteristic and the fixed coefficient closure. `E F : Index P`, `h : E ≤ F`
  are actual finite intermediate coefficient fields and their inclusion. Thus
  identities and ramified inclusions are included.
- `D : FieldShriekSystem.Models P` is the recorded simultaneous presentation of
  the specified operations, coefficient maps and normalized scalar adjunctions.
  This is operation/presentation data, not an assumed commuting projection square.
  Each `D.coefficients` fixes the quotient inclusion on every residue class.
  `SpTowerShriek.B`, `.tau`, `.S`, `.D` give the positive ell-power constant ring
  towers, their strict systems and their ordinary derived category. Level `n`
  means exponent `n+1`; no positive coefficient level is omitted.
- `X Y : Scheme.{u}` with `Over (Spec (.of P.field.k))`, `LocallyOfFiniteType`,
  `QuasiCompact`, and `IsSeparated` on both structure maps render separated
  finite-type k-schemes. `f.IsOver` says f is a k-morphism.
  `d : ℕ`, `SmoothOfRelativeDimension d f`, and `IsSeparated f` render the specified
  smooth separated map and pure relative dimension d ≥ 0. `c : Compactification f`
  is one common compactification for both coefficient fields.
- `K : SpTowerShriek.D ... Y`, `W : SpTowerShriek.D ... X`, and the two
  `normalized P D E ...` hypotheses are precisely the transported published
  normalized constructible subcategories, with uniform cohomological and Tor
  bounds, not a category of diagrams in derived categories.
- `SpTowerShriek.F` is Rp_* after j_!. `comparison P D h c` is literally the
  recorded proper counit mate after j_!, followed by Rp_* of the open coefficient
  isomorphism. The invertibility theorem of the dependency identifies it with b
  on normalized inputs; no arbitrary b is supplied.
- `ProjectionTensorComparisons.scalar` is C(tensor) ≅ tensor(C,C).
  `scalar_model` is the existing `ScalarTensorComparisonModel` on the sequence
  site, fixing its ordinary balancing formula and each total K-flat summand.
  `symmetry_model` similarly fixes the sign (-1)^(ab) on homogeneous pure tensors
  and the localization through the existing tensor representative comparisons.
  The theorem supplies these canonical comparisons; they are not extra hypotheses
  nor unspecified object identifications.
- `leftProjection` precomposes the existing `SpTowerShriek.projection` with source
  symmetry and postcomposes with compact support of target symmetry. Its middle
  arrow is the actual proper-counit transpose followed by the open projection and
  the recorded geometric pullback compositor, exactly def-exchange-projection.
- `projectionTarget` first applies the scalar tensorator at X, then tensors the
  inverse of `(D.pull E F h f).derived` with the identity. It therefore identifies
  C_X(f_A^*K tensor W) with f_B^*(C_Y K) tensor C_X W, with the prescribed arrows.
- `ProjectionSystemSquare` spells out C_Y(pi_A), b at f_A^*K tensor W, and proper
  image of that target comparison on the left. The right side is the source scalar
  tensorator, tensor(identity,b_W), and pi_B. It is equality in `SpTowerShriek.D`
  before evaluation, not equality of evaluated maps, and has no Cartesian-square
  hypothesis on coefficients.
- The final conjunct quantifies over invertibility witnesses and asserts
  `InvertedProjectionSystemSquare`: b (including the target comparison) followed
  by pi_B inverse equals C_Y(pi_A inverse), source scalar tensorator, then
  identity tensor b_W. The dependency's `tower_shriek_levels` supplies those
  witnesses on the stated two-input finite-Tor etale-origin domain, after
  preservation under scalar extension. Stating the inverse equation conditionally
  on these witnesses keeps that exact domain and does not claim all normalized
  inputs have origin witnesses.
- The tower f^! adjunctions, their units/counits and twists are contextual data;
  the projection square uses the proper geometric adjunction and its counit, not
  an arbitrary exceptional adjoint. No twist occurs in the displayed equation.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`, `WeilConjectures.PurityFiniteSetting`;
  `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.finite_coefficientExtensionRing` and imported integer/quotient constructions.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `SmoothOfRelativeDimension`;
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`,
  `AlgebraicGeometry.Etale.DerivedCategoryModule` and its finite-Tor vocabulary.
- `Sheaf.Paper.SmoothPurityCoefficientTowers`, `spCoefficientTowers`;
  `SmoothPurityCoefficientTowersAbelian`, `SpCoefficientTowersAbelian`;
  `SmoothPurityNormalizedTowers`, `spNormalizedConstructibleTorTowers`.
- `Sheaf.Paper.SemilinearDerivedSections`, `SemilinearDerivedSectionsData`;
  `Sheaf.Paper.SemilinearSystemModels`, `SemilinearSections.ScalarData`,
  `ScalarTensorComparisonModel`, `systemRing`, and `totalTensor`. The latter module
  owns the reused scalar/tensor and sequence-ring constructions.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`, the recorded twist vocabulary
  is publicly available through the comparison dependency; no new twist is defined.
- `Sheaf.Paper.SmoothPurityTowerGluing`, `SpTowerGluing.tower_gluing`;
  `SmoothPurityTowerShriekLevels`, `SpTowerShriek.projection`, `F`, `Laws.projection_iso`.
- `Sheaf.Paper.FieldShriekSystemModels`, `FieldShriekSystem.Models`, `Index`,
  `coefficientMap`, `normalized`, and `comparison`, owned by
  `def-sp-field-shriek-system-models`;
  `Sheaf.Paper.FieldShriekSystemComparison`, `field_shriek_system_comparison`.
  Read with `scompile.py --source`, since these recently landed modules are absent
  locally. The theorem module re-exports the definitions; their own DAG owner is
  now cited directly.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`, `coefficientTensorGenerator`,
  owned by `def-coef-ringed-tensor-hom-model`.
- `Sheaf.Paper.CoefficientRingedSequenceSite`, `coefficientSequenceTopology`,
  owned by `def-coef-ringed-sequence-site`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`,
  `CochainComplex.IsKFlatIndependentCoefficients`, owned by `def-pc-kflat-complex`.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`,
  `SuppliedExchangeProjection.compactificationProjectionFromData`;
  `Sheaf.Paper.RingedExchangeTensorCoherence`, `SheafOfModules.ringedExchangeTensorCoherence`.
- Proof imports also retain `Sheaf.SixFunctors.OpenTensorNormalization` and
  `Sheaf.SecSmoothPurity.ScalarExtensionFunctor` as the DAG proof plan requires.

Source: the current latest blueprint's field-extension towers proof (2), read in
`literature/blueprint/latest/`; the node supplies its reviewed expanded proper/open
pasting argument. No statement correction, dependency repair, or new node is needed.
The comparison helper declarations belong to the square itself and are listed in
`lean.declarations`.

Edge cases checked: E=F uses the recorded identity scalar unit; ramified inclusions
use ell-power quotients, not a false uniformizer inclusion. Zero K or W and empty
schemes remain admitted. Dimension zero is included by ℕ. Purely open/proper
compactifications give the open/proper factors of the same word. Shifted inputs
retain the (-1)^(ab) sign, and all scalars have degree zero. Ordinary derived
morphisms invisible to level evaluations are not identified by this statement.
The pro-etale site retains object universe u+1 and morphism universe u; the
sequence site has the same bounds and coefficients lie in u+1.

Searches actually run:

- msearch leanfinder: "Scalar extension commutes with the compact support projection
  formula as morphisms of derived coefficient systems". Eight hits, chiefly
  ModuleCat.extendScalars associators, none the whole-system projection square.
- msearch loogle: "CategoryTheory.Adjunction, CategoryTheory.MonoidalCategory".
  Twelve hits for monoidal adjunctions; no matching coefficient-tower statement.
- msearch grep: "projection.*scalar|scalar.*projection", CategoryTheory. Zero hits.
- msearch leansearch: "Derived scalar extension tensor projection compact support
  coefficient systems". Eight hits for ordinary module/scalar constructions and
  unrelated compact support; none the requested equation.
- rg in lean/WeilConjectures and lean/Sheaf for the node id, field projection and
  scalar/projection combinations. The upstream ProjectionExtendScalars file states
  projection invertibility for scalar extensions of integral objects, not equality
  of the actual whole-system coefficient/projection words. Existing generic
  ringed exchange/tensor coherence is the proper part only; it has no open factor.

## Second reading by NI

Self-check only; the maintainer's independent review is supplied by the delivery
workflow. No second worker was started, as the dispatch brief forbids delegation.
I re-read the node against the definitions and theorem: the comparison uses the
same c in both fields; the target scalar comparison has the inverse pullback
orientation; source order is K tensor P(W), target order is f^*K tensor W; both
symmetries are present; the displayed statement includes an inverse equation.
The helper normalizations prevent replacing the actual comparison maps by arbitrary
natural isomorphisms. The first draft omitted the explicit inverse equation; this
was added before the final compile. The proof docstring follows all five reviewed
DAG steps, including preservation of the origin domain in the last step.

## Repair of returned delivery 560adf32c5f0

The independent review's H2 identified definition owners missing from `stmt_deps`.
Added all three required owners and both advised owners, each already recorded
in the current DAG:

- `def-sp-field-shriek-system-models`: `Models`, `comparison`, `normalized`,
  `Index`, and `coefficientMap`.
- `def-coef-semilinear-system-models`: `ScalarTensorComparisonModel`,
  `systemRing`, and `totalTensor`.
- `def-coef-ringed-tensor-hom-model`: `coefficientTensorGenerator`.
- `def-coef-ringed-sequence-site`: `coefficientSequenceTopology`.
- `def-pc-kflat-complex`: `CochainComplex.IsKFlatIndependentCoefficients`.

Re-read the five owner nodes and the relevant declaration signatures and
docstrings. The sandbox node matched the current read clone in every field except
its delivery's `lean` record before this repair; its original statement and proof
remain unchanged. The module is byte-identical to the returned delivery. This is
a dependency-metadata correction under brief-stage2 §5's authorization to add
landed owners requested by a return, and requires no `statement_change`. The
review accepted the mathematics and treated the proof-only imports as advisory;
those imports are retained. No dependency module or new node is added.
