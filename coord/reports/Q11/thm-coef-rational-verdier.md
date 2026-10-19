## Worker report

The module `Sheaf.SixFunctors.RationalVerdier` states
`WeilConjectures.coef_rational_verdier`. Its sole postponed theorem asserts
`RationalVerdier.Conclusion D l hl X`. The structures and predicates in this module only
package the conclusion and its canonical normalization equations; no dualizing
object, functor, comparison, or inverse is defined by choosing arbitrary data
from a sorry-backed existence theorem. All helper definitions contain real data.
The node's statement and dependency lists are unchanged.

Hypotheses and clauses, in their source order:

- The fixed global finite-field datum is `D : FiniteFieldDatum.{u}`. The prime is
  `l : ℕ` with `[Fact l.Prime]`; `hl : l ≠ D.p` excludes the characteristic.
- The separated finite-type k-scheme is `X : Scheme.{u}` with
  `[X.Over (Spec (.of D.k))]`, `[IsSeparated (X ↘ Spec (.of D.k))]`,
  `[LocallyOfFiniteType (X ↘ Spec (.of D.k))]`, and
  `[QuasiCompact (X ↘ Spec (.of D.k))]`. The latter two together are finite type;
  `IsSeparated` is Mathlib's closed-immersion diagonal condition. Properness and
  universal closedness are not assumed.
- Every finite coefficient extension occurs in the first existential family of
  `Conclusion` as
  `(F : Type u) [Field F] [Algebra (Padic l) F]
  [FiniteDimensional (Padic l) F]`. There is no fixed finite list of fields.
  The comparison family and associator conjunct of `Conclusion` quantify arbitrary
  field embeddings
  `F →ₐ[Padic l] G`, including identities and arbitrary towers.
- Integral objects are exactly `sfIntegralConstructibleCategory l F X`:
  ordinary module sheaves over the completed ring on the small pro-etale site,
  derived complete, constructible at every positive finite reduction, with one
  uniform finite cohomological interval. Rational objects are exactly
  `sfRationalConstructibleCategory l F X`, the recorded raw localization. No
  alternate category or idempotent completion is introduced.
- `IntegralFiniteExtension.DualizingDatum` supplies the already recorded integral
  dualizing object and its coherent exceptional reductions. The theorem does not
  require a dualizing datum as an added hypothesis: its conclusion covers every
  such presentation, and the dependency's `dualizingDatum_nonempty` supplies
  these presentations from the integral dualizing proposition. In particular it
  is not a vacuous implication with an arbitrary object called omega.
- `Datum.preserves` restricts the actual ambient
  `IntegralVerdier.dual l F X w.omega.obj`, which is the recorded RHom into omega.
  `Datum.objects` and `.pure` specify its rationalization on unchanged objects and
  every pure tensor. The coefficient factor is unchanged, so there is no scalar
  involution. `.additive` extends this to all sums of tensors.
- Exactness is `Datum.exact`: there exists a shift comparison and the resulting
  image of every distinguished opposite triangle is distinguished for the
  recorded rational triangulation. Anti-equivalence is `.equivalence`, applied
  to this same normalized functor. E-linearity is `.linear`: for every `c : F`
  and every arrow the dual preserves multiplication by `c`, expressed through
  the canonical `sfRationalCoefficientEquiv l F` in the category's actual Hom
  scalar coordinates. This avoids inventing a second linear-category instance.
- The rational dualizing object is literally
  `(sfRationalConstructibleLocalization l F X).obj w.omega`, used as the target
  of `Datum.evaluation` and of `Extension.omega`. It is never replaced by an
  existentially chosen rational object.
- `Datum.bidual` is a natural isomorphism from the identity to `dual.rightOp ⋙
  dual`. `.bidual_integral` identifies each component with localization of the
  actual evaluation-defined `IntegralVerdier.delta`, through the full-subcategory
  Hom constructor. Thus invertibility and naturality concern the specified arrow.
- `Datum.evaluation` uses the existing `rationalDerivedTensor` operation.
  `.evaluation_integral` identifies it with localization of ordinary integral
  evaluation composed with the inverse completion comparison. Evaluation is
  written in the recorded integral adjunction's K-tensor-DK order; its signed
  symmetry gives the equivalent DK-tensor-K convention in the proof sketch. The
  `completionChain` reuses the recorded theorem's actual chain map. Its stated
  quotient-map coordinates on all homogeneous local tensor generators and zero
  shifted coordinates determine it uniquely: those generators determine the
  total-tensor sheaf maps, the product projections determine the first mapping-fiber
  coordinate, and the first and shifted coordinates are jointly monic. Thus this
  is not choice from unspecified existence. `Completion` retains the natural
  derived comparison, invertibility on constructible pairs, and descent of this
  fixed chain map on K-flat representatives. This is
  precisely the normalized ordinary-to-completed comparison from proof step 5,
  not an arbitrary tensor isomorphism. `.evaluation_natural` explicitly states
  the evaluation square for every rational arrow.
- `Extension.comparison` is a natural isomorphism
  `A.dual ⋙ scalar ≅ scalar.op ⋙ B.dual`. The second conjunct of `ExtensionProperties` is exactly
  the localized canonical `IntegralFiniteExtension.beta`, with its ordinary
  tensor presentations retained. Its first conjunct similarly fixes the
  dualizing comparison to the canonical integral `u`.
- The third conjunct of `ExtensionProperties` is the actual evaluation equation using the inverse of
  the recorded `rationalTensorScalarComparison`, extended evaluation, and the
  normalized omega comparison. Its fourth conjunct is the actual delta square:
  `T(δ_K) ≫ β_(DK) = δ_(TK) ≫ D_L(β_K)`.
- The unit conjunct of `Conclusion` supplies a natural unit comparison whose components are the
  rationalized integral tensor multiplication maps; it states
  `β_K = j_(DK) ≫ D(j_K)`. The associator conjunct of `Conclusion` similarly normalizes the natural
  associator to integral tensor associativity and states the equation for the
  two successive beta comparisons versus the direct beta comparison, with
  the final dual associator in its contravariant direction.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` and its separated import:
  `AlgebraicGeometry.IsSeparated`. The node's `IsProper` is not used as a
  stronger hypothesis.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, `sfRationalCoefficientEquiv`,
  `sfRationalScalarExtension`, and the recorded rational triangulation.
- `Sheaf.SixFunctors.IntegralVerdier`: `IntegralVerdier.dual`,
  `.restrictedDual`, `.delta`, `.SignedSymmetry`, `integral_verdier_biduality`.
- `Sheaf.SixFunctors.IntegralDualizing`: `prop_coef_integral_dualizing`.
  Its coherent dualizing input is reused through the existing
  `IntegralFiniteExtension.DualizingDatum`, not reconstructed privately.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleIntegralTensor`,
  `rationalDerivedTensor`, `rationalTensorScalarComparison`.
- `Sheaf.SixFunctors.CoefIntegralFiniteExtension`:
  `IntegralFiniteExtension.DualizingDatum`, `.dualizingDatum_nonempty`,
  `.u`, `.beta`, `.unit`, `.comp`, `coef_integral_finite_extension`.
- Proof-only modules are imported for `integral_residue_tor`, generic rational
  transport, and preservation of constructibility. The normalized completion
  presentation uses the declarations of
  `Sheaf.SixFunctors.ConstructibleTensorCompletion` and the ordinary tensor
  presentation of `Sheaf.Paper.IntegralHomReduction`.
- `finiteFieldDatumPrimeUnit` from `Sheaf.Paper.DirectImagesConstructible` gives
  the inverse of l in each residue field by the structure morphism's actual
  `residueFieldAlgebraMap`. This is constructed in `RationalVerdier.units`,
  so no invertibility hypothesis or file-local instance is added.

Edge cases checked before writing:

- Empty X is permitted: there is no nonemptiness or dimension hypothesis.
- Zero integral objects and torsion integral representatives remain objects of
  the raw rational category; the pure-tensor formula respects their scalar
  localization relations. No lattice freeness is required.
- E = Q_l, identity embeddings, and identity legs of a tower are included in
  the universal field quantifiers and the unit/associator clauses.
- All positive coefficient levels are retained: n : ℕ in the dependencies
  denotes exponent n+1. The completion normalizations quantify every n.
- Each embedding is an actual Q_l-algebra embedding. Different coherent
  presentations of omega are all covered, while the identity equation uses the
  same presentation at both ends, as required for the canonical unit.
- The scheme, coefficient fields and their algebraic closure datum use the
  dependency's common size universe u. The small pro-etale site retains its
  distinct object and morphism universes u+1 and u inside those declarations.
  No equality of the two site universes is imposed.
- The scalar-extension helper uses characteristic parameter 0 solely to match
  the recorded tensor-comparison interface; the actual geometric datum still
  has characteristic D.p. This parameter is absent from the underlying
  completed extension construction and Hom formulas, and adds no condition.

Searches (no exact existing statement):

- msearch leanfinder, “Integral Verdier duality induces an exact linear
  anti-equivalence on a raw scalar localization with evaluation and scalar
  extension coherence”: eight general localization/linearity/derived-category
  results, none with the geometric objects and canonical coherence clauses.
- msearch loogle, `CategoryTheory.Equivalence, CategoryTheory.Linear`:
  `CategoryTheory.Equivalence.inverseLinear` only.
- msearch grep, `Verdier|rationalization|anti-equivalence`, subdirectory
  `CategoryTheory`: general Verdier-localization and opposite-triangle results;
  no coefficient duality theorem.
- msearch leansearch, “Verdier duality on rationalized constructible derived
  categories with finite coefficient field extension compatibility”: eight
  general derived linearity, derived functor and finite-module dual results;
  none is the present statement.
- rg over upstream WeilConjectures and project Sheaf for rational duality,
  `coef_rational_verdier`, `RationalVerdier`, and the node id: the upstream
  point-perfect docstring and unrelated toric results; project
  `SfBidualityClass` has a downstream four-stage statement but does not give
  this theorem's E-linearity, completed evaluation and finite-extension
  unit/associator equations. Its generic duality packaging does not already
  define the normalized conclusion used here. No duplicate theorem is written.

Source review: current blueprint theorem and proof paragraphs 1–3, all seven
DAG proof steps, every statement dependency and its recorded interface, and
maintenance repair note (stage 1, re-splitting only). No statement correction,
new node or dependency repair is needed.

Validation: the final module passed both wrapper compilation modes with the
default limits, with no warnings except the expected theorem `sorry` warning.
The delivery dry run passed the maintainer's preflight and per-file compilation
(`OK (dry run)`, commit fae794fd18). No diagnostic options or check commands remain.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
