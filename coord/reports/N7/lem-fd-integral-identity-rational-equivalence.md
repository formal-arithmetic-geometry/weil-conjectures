## Worker report

Item: `lem-fd-integral-identity-rational-equivalence`.
Module: `Sheaf.Paper.FdIntegralIdentityRationalEquivalence`.
Declaration: `WeilConjectures.fdIntegralIdentityRationalEquivalence`.

The module states existence of the canonical integral equivalence and its exact raw
rationalization, using the existing `FdRationalStageComparison` as data, with the
additional properties in the node stated explicitly. There is one theorem, with
`sorry`, and no new definitions. The module docstring and theorem docstring name the
source; the latter supplies the four-step natural-language proof with the DAG inputs.
No node statement, dependency, proof, or other field is changed; only `lean` is added.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Global finite-field datum | `D : FiniteFieldDatum.{d}`; no structure over its fields is imposed on T. |
| Prime ell different from p | `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`. |
| Algebraic closure Omega/Q_ell | `(Ω : Type w) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]`. |
| T noetherian and finite-dimensional, ell invertible | `(T : Scheme.{u}) [IsNoetherian T] [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)] [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]`. These are the existing datum's exact geometric assumptions. |
| Every finite E inside Omega | `(E : Padic.FiniteCoefficientFields l Ω)`. `pbcFiniteField.{u} l Ω E` is the published canonical `Shrink` model, with its field, Q_ell-algebra, and finite-dimensional instances. It imposes no equality between u and w. |
| Common full integral category and I | `∃ c : FdRationalStageComparison l Ω T E`. Its `integral` is the equivalence of `sfIntegralConstructibleCategory` and `pbcIntegralStage`. Its `integral_identity` is equality of the forward functor followed by the full inclusion with the framework inclusion followed by `integralDetailedTransport`. Thus the equivalence is the specified coefficient restriction, rather than an arbitrary equivalence. |
| Quotient-normalized coefficient isomorphism | The existential `e` satisfies `(adicLisseForget T).mapIso e = integralDetailedCoefficientComparison T l (pbcFiniteField l Ω E)`. The latter is the published unique comparison characterized by all finite projections and `integralCoefficientULift` on quotient representatives. The forgetful functor is fully faithful, so this also uniquely fixes e. |
| Integral O_E-linearity in both directions | The two integral map equations use `a • f ↦ ULift.up a • I(f)` and `a • f ↦ a.down • I⁻¹(f)` with the original constant-section Hom actions. The lift/down is exactly the published PBC coefficient presentation. Both functors are also explicitly additive. |
| Integral exactness in both directions | `c.integral.functor.IsTriangulated` and existential `si : c.integral.inverse.CommShift ℤ` with `c.integral.inverse.IsTriangulated` under that same si. The instance lambda scopes the data; it does not introduce another choice of shift in the inverse formula. |
| Integral forward shift induced by the ambient identity | `c.integral_shift_normalization` in the existing datum compares, after inclusion, with the shift of `(fdCoefficientTransport ...).mapDerivedCategory`. This is the Mathlib exact-functor shift induced by the degreewise identity. |
| Integral inverse is the same ambient identity in reverse | `c.integral.inverse ⋙ (sfIntegralConstructible ...).ι = pbcStageInclusion ... ⋙ pbcDerivedRestrict e.inv`; the following all-integer-shifts equation normalizes its si against the canonical `((pbcRestrict e.inv).mapDerivedCategory).commShiftIso`. |
| Preservation of finite-reduction functors | The final `r` and `α` are natural isomorphisms of the actual restriction squares and derived finite-reduction functors, using each positive quotient. The equation on every section says r is literally the identity, not an arbitrary comparison. The final equation identifies the actual derived adjunction-unit maps through `IntegralCoefficientPresentation.restrictedComparison`; it pins α as the canonical tensor comparison. These are the published coefficient-presentation comparison's normalized reduction clauses restricted to the integral objects. The functor is already exactly the ambient restriction by `integral_identity` and the equation for e. |
| Raw rational equivalence J | `c.rational`, between exactly `sfRationalConstructibleCategory` and `pbcStageCategory`, both the recorded raw scalar localizations. |
| J fixes integral objects | `c.objects`: `c.rational.functor.obj K = ⟨c.integral.functor.obj K.obj⟩`. The explicit inverse object equation gives the reverse formula. These are the identity formulas after the coefficient presentations are identified. |
| J fixes pure tensors | `c.tensors`, with the existing `fdRawTensor`, sends the integral arrow by I and transports the scalar through the canonical `sfRationalCoefficientEquiv`/`pbcRationalCoefficientEquiv`. The theorem explicitly gives the inverse pure-tensor formula using I⁻¹ and the opposite scalar transport. The scalar-first tensor order is the recorded implementation; tensor commutativity gives the node's Hom-first order. |
| E-linearity | The two `fdRawScale` equations are scalar preservation for every morphism and every localized coefficient, identified with E by the canonical coefficient equivalences. The datum supplies forward additivity; inverse additivity follows from being an equivalence of preadditive categories. These equations express field-linearity without choosing additional conflicting Hom-module instances. |
| Rational exactness in both directions | Existing datum fields `exact`, `inverse_exact`, `inverse_triangles`; no replacement triangulation is introduced. |
| Rational shift comparison localizes the integral one | Existing `c.shift_normalization` and the explicit inverse normalization using the datum's actual `c.inverse_exact` and the same integral si. Both quantify over all integer shifts. |
| No added objects or retracts | Both types are literally `ScalarLocalization`, whose only object datum is an original integral object. No Karoubi category appears in the type or module. |

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` (all fields and its source convention).
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`, `sfRationalConstructibleLocalization`, `sfRationalCoefficientEquiv`, and their recorded shift and triangulation instances.
- `Sheaf.Paper.PbcRationalCategory`: `AlgebraicGeometry.Scheme.PbcRationalCategory`, `PbcRationalDerivedCategory`, `pbcRationalization`, and the constant-section integral linearity. The stage aliases in the datum unfold to this same raw category, not a competing notion.
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`: `integralStratifiedPerfectCharacterization`, `integralStratifiedPerfectDetailed`, `integralCoefficientULift`, `integralDetailedCoefficientComparison`, `integralDetailedTransport`; read their complete signatures and proof/source docstrings. The actual transport is exact derived scalar restriction along the normalized ring comparison.
- `Sheaf.Paper.FdCoefficientComparison`: `WeilConjectures.FdRationalStageComparison`, `fdCoefficientTransport`, `fdRawTensor`, `fdRawScale`. Read every field of the stage datum; do not use the larger coherent-system datum as an assumption or existence result.
- `Sheaf.Paper.IntegralCoefficientPresentationComparison`: `IntegralCoefficientPresentation.comparison`, `level`, `derivedSquare`, `restrictedComparison`. Its derived reduction comparison is used directly in the final clause, retaining the normalized adjunction units.
- Proof imports: `Sheaf.Paper.SfIntegralConstructibleTriangulated` (`sfIntegralConstructible_isTriangulated` and isomorphism closure), `Sheaf.Paper.PbcUniformCompleteTriangulated` (`pbcIntegralUniformComplete_isTriangulated`), `Sheaf.Paper.SfIntegralConstructibleLinear` (`sfIntegralConstructible_linear`), `Sheaf.CategoryTheory.ScalarLocalization` (raw category and tensor operations), `Sheaf.CategoryTheory.ScalarLocalizationTriangulated` (`exists_triangulated_scalarLocalization`), and `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` (`Functor.mapDerivedCategoryFactors` and the exact-functor shift/triangulated instances, the recorded Mathlib match for `lem-weil-pbc-exact-functor-derived-factorization`).

The existing stage datatype's supporting modules (`FiniteStagePairCategory`,
`PbcFiniteCompletedCoefficientMap`, and `PbcScalarExtension`) were also read to check
that finite-field shrinking, coefficient lifting, the inclusion, and the rational
triangulation really are the recorded ones. They are inherited through the datum's
imports; no new aliases or structures are declared here.

Edge cases checked before writing and again during the reading:

- Empty T: no nonemptiness or point is assumed; the stalkwise condition is the same one used by the existing datum, and all formulas still make sense.
- Zero objects, zero arrows and zero pure tensors: the same full categories and raw tensor Hom groups are retained; the maps are additive and the equivalences are exact.
- E=Q_ell and degree-one extensions: no proper-inclusion condition occurs, and all coefficient equivalences are the recorded normalized ones.
- Positive finite quotients: the index n ranges over every natural number, with exponent n+1 in the reused definitions, so the first positive quotient is included and a zero-exponent quotient is not substituted.
- Integer shifts: forward and inverse pins cover zero, positive and negative shifts, with no independent twisted shift comparison.
- Universes: the datum D, scheme T and closure Omega have separately bound d,u,w. The existing finite-dimensional `Shrink` model handles a large Omega without an extra size equality.
- The finite-reduction comparisons are natural isomorphisms fixed on sections and adjunction units, not arbitrary identifications of target categories.

Searches (all wrapper calls were made with group N7 and this item; exact service
outputs are also in the wrapper's `searches.jsonl`):

1. LeanFinder: `The identity on integral constructible derived sheaves gives an exact linear equivalence of raw scalar rationalizations fixing integral objects and pure tensors`. Eight hits, led by `ModuleCat.extendScalarsId_inv_app_apply`, `ModuleCat.extendScalarsId`, and `ModuleCat.extendRestrictScalarsAdj_unit_app_apply`; generic module statements, not the required comparison of these integral full categories and raw rationalizations.
2. Loogle: `CategoryTheory.ScalarLocalization.map, CategoryTheory.Equivalence`. Zero hits, unknown identifier `CategoryTheory.ScalarLocalization.map` (this is a project declaration, not Mathlib).
3. Mathlib grep wrapper: `rationalization|scalarLocalization`, scope `CategoryTheory`. Zero hits.
4. LeanSearch: `exact equivalence between scalar rationalizations induced by an integral coefficient restriction functor`. Eight hits including `ModuleCat.restrictScalars`, `ModuleCat.ExtendRestrictScalarsAdj.homEquiv`, and `LinearEquiv.extendScalarsOfIsLocalizationEquiv`; none states the specialized equivalence or its pins.
5. Direct `rg` in Mathlib CategoryTheory for `rationalization|scalarLocalization`: no match. Direct `rg` across `lean/WeilConjectures` and `lean/Sheaf` for `integral.identity|FdRationalStageComparison|integralDetailedTransport|lem-fd-integral-identity-rational-equivalence` located the existing datatype, its consumers, and the canonical ambient transport; no existing theorem states this item. The parent `rationalCoefficientCategoryComparison` asserts a whole coherent system and Frobenius comparisons, so it is a different statement and a downstream consumer, not an existing match.
6. Direct `rg` for `fdIntegralIdentityRationalEquivalence` in Mathlib, upstream and project Lean, and for this name/`FdRationalStageComparison` in `dag/lean_names_upstream.json`: no declaration conflict. The requested item-id search in upstream Lean has no hits.

No missing notion or dependency interface repair is needed. No statement correction
and no STATEMENT-DISPUTED issue was found.

Validation: the prescribed `scompile.py` compiled the sandbox and final library module
cleanly, in 6.1 and 6.3 seconds respectively. Initial elaboration repairs scoped the
integral inverse shift instance and unfolded the existing `pbcDerivedRestrict` when
selecting its canonical shift; these changed no mathematical hypotheses or clauses.

## Second reading by N7

A separate reading pass in this worker reopened the node, the complete module and the
existing finite-stage datum; no other agent was started, as instructed by the dispatcher.
The maintainer supplies the independent review after delivery. This is a self-review,
not a claim that a second person or agent read the file.

The initial datatype-only formulation would have omitted integral linearity/exactness,
inverse pure-tensor and object formulas, and the normalized finite-reduction comparison;
the final theorem explicitly supplies all of them. Its forward pins are exactly the
existing datum's `integral_identity`, `integral_shift_normalization`, `objects`,
`shift_normalization`, and `tensors`. The reverse integral identity is tied to e.inv,
its shift to the exact derived restriction shift, and the reverse rational shift to
that same integral shift. Both rational scalar equations act on arbitrary arrows,
not just pure tensors. The final reduction comparison uses the same canonical finite
coefficient isomorphisms as e; the section identity and unit equation exclude an
arbitrary natural isomorphism. The table above matches each hypothesis and conclusion.
No change to the node's mathematical statement was needed.
