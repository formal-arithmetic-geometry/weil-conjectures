## Worker report

This delivery states the compound finite-product coefficient-descent lemma in
`Sheaf.Paper.FiniteProductFieldCoefficientDescent`, namespace
`WeilConjectures.FiniteProductFieldDescent`. Every new theorem has exactly `sorry`
as its proof. Definitions contain actual recorded constructions; chosen comparisons
are determined uniquely by their specified integral or finite-stage representative.
The natural-language statement and proof of the node are unchanged.

Hypothesis-by-hypothesis correspondence:

- `P : PurityFiniteSetting.{u}` supplies the recorded global finite-field datum,
  the prime ell different from its characteristic, and the fixed coefficient closure.
  Its auxiliary finite level and extension do not enter the conclusions. All finite
  subextensions of the fixed closure occur as `E : Index P.coefficients.l P.coefficients.Qbar`.
  `Coefficient.{u}` is the published equivalent small model, not an additional restriction.
- `X : Over (Spec (CommRingCat.of P.field.k))`, `[LocallyOfFiniteType X.hom]`
  and `[QuasiCompact X.hom]` say finite type over k, exactly the recorded conjunction.
- `{I : Type w} [Finite I]`, `Xi`, and `j : ∀ i, Xi i ⟶ X` allow any finite
  index type in an independent universe. Open and closed immersions are the actual
  Mathlib classes on `(j i).left`. `hdisjoint` is disjointness of their ranges;
  `hcover` states that their union is the whole underlying space. No nonemptiness,
  separatedness, smoothness, or extra invertibility assumption is imposed.
- `residueInvertible` transports the published, source-implied stalk unit along
  the residue homomorphism. It supplies the instances needed by the recorded operations.
- `IntegralComparisons.equivalence` uses the actual product restriction `Functor.pi'`;
  `.linear` is O_E-linearity of each actual component pullback. `.tensor` and `.unit`
  are precisely the assumed integral natural tensor and coefficient-unit comparisons.
  `.sourceScalarUnit` and `.componentScalarUnit` record the unit identifications under
  integral scalar extension. `.tensor_scalar` and `.unit_scalar` spell out their
  compatibility squares with the published integral pullback/scalar and tensor/scalar
  isomorphisms, for every inclusion, including identity inclusions.

Conclusion-by-conclusion correspondence:

- `restriction_equivalences.1` states that each actual rational restriction into the
  product is an equivalence; `.2` states this for actual common-stage restriction.
  `rationalCategory` specializes `sfRationalConstructibleCategory`, hence is raw scalar
  localization with unchanged objects. `commonCategory` specializes the recorded
  intrinsic pair category, not a category obtained by adjoining retracts.
- The canonical finite-product tensor isomorphism is the existing `TensorProduct.piLeft`
  from the proof dependency `lem-weil-pbc-tensor-finite-product`. It is valid for every
  finite family of integral component Hom modules, including the empty family.
  `hom_tensor_formula` identifies the actual rational restriction map on pure tensors
  with the integral component map tensored with the same scalar, in the recorded
  Hom-first E coordinates `sfRationalHomCoordinates`. Pure tensors generate, so this
  is the claimed canonical Hom map after the integral Hom bijection and `piLeft`.
- `objects_at_common_field` explicitly gives one finite L, upper bounds for every
  component's field of definition, a rational global object there, and component
  isomorphisms to the transported objects.
- `arrows_at_common_field` gives one L containing both global endpoint fields, one
  actual `StageHom` representative, and equality of every restricted class with the
  prescribed component arrow. With the object-preimage clause this also covers arrows
  between arbitrary component tuples. The actual recorded common-stage pullback
  specifies each component representative at that very L.
- `component_equality_iff_eventual` is the required iff for arbitrary representatives
  at potentially different fields: all component classes agree precisely when their
  actual global transports agree at one further common finite field. No transition
  Hom injectivity is assumed.
- `rational_tensor_existsUnique` and `rational_unit_existsUnique` fix the rational
  comparisons by localization of the given integral maps. Their named comparison
  definitions choose from these determining unique specifications.
- `rationalPullbackScalar` is the published normalized coefficient comparison.
  `rational_tensor_scalar_compatible` and `rational_unit_scalar_compatible` state the
  two cross-stage compatibility squares. The latter uses `rationalScalarUnit`, fixed
  uniquely by the localized integral scalar-unit map. These include identity extensions;
  the published scalar comparisons retain their tower normalization.
- `common_tensor_existsUnique` gives a natural tensor comparison whose class at every
  common L is the displayed path `tensorRepresentative`: pullback comparison, restricted
  tensor comparison, rational comparison, inverse component pullback comparisons, inverse
  tensor comparison. Thus the assertion specifies the canonical comparison and its
  independence of enlargement, rather than just an arbitrary natural isomorphism.
- `common_unit_existsUnique` fixes the unit comparison by its actual finite-stage
  representative, with the published transition identification and coefficient unitor.
  The stage system has no fictitious unit field; the formula uses
  `operationStageTransitionIso` followed by the actual `unitor`.
- Identities and composition are preserved by the actual functors used throughout;
  natural isomorphisms assert naturality on all arrows. Their representative formulas
  use the existing canonical scalar comparisons and therefore include those operations.
- At field coefficients `finiteTorFieldCoefficientCategory` in the original, retained
  `Sheaf.Paper.FiniteTorAmplitude` is literally the identity type abbreviation. Consequently
  both displayed equivalences apply unchanged to both finite-Tor field categories.
  That module is imported alongside the currently recorded finite-level presentation
  `FiniteTorAmplitudeSites`. No finite or integral Tor condition is silently removed.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`,
  `PurityFiniteSetting.coefficientPrime_isUnit_stalk`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`,
  `QuasiCompact`; Mathlib's open and closed immersion classes and its small site `Scheme.ProEt`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, `sfRationalHomCoordinates`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: the intrinsic category,
  `integralTransition`, `transition`, `stageSystem`, `StageHom`, `ofHom`, `transport`,
  and `unitor`; the common-stage objects are the recorded `StageSystem.PairCategory`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleIntegralPullback`,
  `constructibleIntegralTensor`, `rationalDerivedPullback`, `rationalDerivedTensor`,
  the integral and rational scalar comparisons, `commonStageDerivedPullback`,
  `commonStageDerivedTensor`, their object formulas, and their normalized comparisons.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices` and
  `Sheaf.Paper.IntegralScalarExtensionUniverses` retain the recorded ambient operations;
  the constructible operations above restrict those actual constructions.
- `Sheaf.Paper.ConstantCoefficientObjectsConstructible`:
  `integralConstantCoefficientObject`, `integralConstantCoefficient_constructible`.
  Its already landed node is added to `stmt_deps`, because constructing the actual
  unit in the constructible full subcategory uses this exact theorem.
- `Sheaf.Paper.FiniteTorAmplitudeSites` and retained `FiniteTorAmplitude`:
  `finiteTorConstructibleEtale`, `finiteTorFieldCoefficientCategory`.
- Proof imports retain `Sheaf.Paper.SfScalarExtensionComposition`,
  `Sheaf.Paper.IntegralOperationsScalarComparisons`,
  `Sheaf.CategoryTheory.ScalarLocalization`,
  `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`,
  `Mathlib.LinearAlgebra.TensorProduct.Pi` (`TensorProduct.piLeft`),
  and `Mathlib.CategoryTheory.Equivalence` (`Functor.asEquivalence`).

Edge cases checked: empty I is permitted throughout; its cover forces X empty, but
no nonempty binder is introduced. Empty tuples still have common fields, and empty
products are terminal categories with singleton Hom sets. The zero object and zero
arrows remain actual integral objects/arrows and their raw localizations. The equality
criterion explicitly allows differing initial fields and noninjective transitions.
Identity and repeated coefficient extensions are included. The small pro-etale site
retains object universe u+1 and morphism universe u; only the finite index type uses w.
The fixed coefficient closure may be larger than the schemes, since the recorded
small coefficient model transports every finite subextension into the scheme universe.

Searches made: msearch.py LeanFinder query "Finite product equivalence of integral
linear categories descends to rational scalar localization and common finite coefficient
field categories" returned general localization finite-product results, none stating
this coefficient-specific result. Loogle "TensorProduct.piLeft, Functor.IsEquivalence"
initially returned an unknown-identifier diagnostic; the repaired Loogle query
"TensorProduct.piLeft" found the exact generic finite-product tensor equivalence and
its ideal-quotient specialization. msearch grep "piLeft|finite.*[Pp]roduct.*[Ll]ocal"
in `LinearAlgebra/TensorProduct` found Mathlib's `TensorProduct/Pi.lean`.
Repository rg searches for this item id, `FiniteProductFieldDescent`, and
`finite.*product.*[Cc]oefficient` in `lean/WeilConjectures`, `lean/Sheaf`, and the
upstream declaration index found no existing statement; unrelated representation and
coefficient-matrix results do not assert the rational/common-stage descent.
The source blueprint section invariant and all statement-dependency records were read.

No statement correction or disputed claim is proposed. No new nodes or dependency
modules are needed. All helper declarations belong to clauses of this compound node.
The server compilation passes cleanly, both as a sandbox and as the library module (33.2 s and 34.0 s). The delivery preflight is performed through the prescribed wrapper.

## Second reading by Q59

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
