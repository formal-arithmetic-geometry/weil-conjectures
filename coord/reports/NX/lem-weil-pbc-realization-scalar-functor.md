## Worker report

The module `Sheaf.Paper.RealizationScalarFunctor` states
`WeilConjectures.realization_scalar_functor`, with its conclusion packaged by
`WeilConjectures.RealizationScalarFunctorData`. The only new theorem has proof
`sorry`. The record packages data and properties; it chooses no object from an
existence proof, and introduces no alternative coefficient ring, scalar extension,
module category, localization, or constructibility predicate.

The source PDF was opened by `pdftotext`: Lemma 6.8.2 identifies the integral
coefficient limit and field localization; Proposition 6.8.11(3) identifies bounded
constructible integral complexes; Proposition 6.8.14(2) supplies the scalar functor.
Only the construction part of the last result is stated here.

Hypothesis-by-hypothesis matching:

| Node hypothesis | Lean rendering |
| --- | --- |
| Prime ell | `(l : ℕ) [Fact l.Prime]` in the explicitly bound section context |
| Finite normed extension of Q_ell | `(E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]` |
| A is the valuation ring, with a fixed uniformizer | Existing `PbcIntegralRing l E`, `pbcIntegralDatum l E`, `pbcUniformizer l E`; these are the lifted recorded valuation ring and its recorded chosen uniformizer, not additional coefficient parameters |
| k has positive prime characteristic different from ell | `(k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]` |
| T is a scheme over k | `(T : Scheme.{u})` and `[T.Over (Spec (.of k))]` |
| Separated finite type over k | `[LocallyOfFiniteType (T ↘ Spec (.of k))]`, `[QuasiCompact (T ↘ Spec (.of k))]`, `[IsSeparated (T ↘ Spec (.of k))]` |
| Explicit Noetherianity | `[IsNoetherian T]` |
| Explicit finite dimension | `[Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]` |
| ell invertible in local rings | `[Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]` |

Clause-by-clause matching in `RealizationScalarFunctorData`:

| Node clause | Lean rendering |
| --- | --- |
| Small pro-etale completed coefficient A_T | `pbcAdicCompletion T (pbcIntegralDatum l E)`; its inverse-limit construction is reused |
| E_T consists of continuous functions, with the specified A_T-algebra structure | `integralIso` identifies the completion with `integralCoefficientSheaf l T E`; `finiteIso`, `finite_normalization`, `integral_normalization` fix this identification on every positive quotient. `inclusion` with `inclusion_normalization : integralRationalCoefficientNormalized ...` is postcomposition with A included in E. The actual coefficient map is always `integralIso.hom ≫ inclusion`. |
| Archived internal coefficient and sectionwise encoding | `condensedRingObj (Profinite.continuousCoefficientRingObj E) T`, its existing `BoundedConstructible` category, and the composite `sectionModuleEquivalence … |>.trans (ringModuleEquivalenceOfIso …)` written out in full. `coefficientIso` and its profinite-test normalization, followed by `sectionIso` and its pointwise normalization, fix precisely the continuous coefficient chart. The encoding is the existing section-module equivalence followed by existing coefficient-isomorphism transport. |
| Integral I_T | `PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)`; this is the same published general category used by the recorded `pbcBoundedConstructibleComplete` specialization. The specialization for E in Type u lifts the integers, retaining the small-site object/morphism universe convention. |
| Raw R_T | `PbcRationalCategory T (pbcIntegralDatum l E) (pbcUniformizer l E)`; its objects and localized Hom modules are unchanged, without a Karoubi envelope. |
| Actual ambient F_T | The existing `pbcDerivedExtend (integralIso.hom ≫ inclusion)`, not an arbitrary functor variable. `pbcExtend` is its prescribed sheafified ordinary tensor construction and `pbcComplexCounit` is its universal derived comparison. |
| Exact scalar extension | `extension_exact`, `extension_colimits` give ordinary exactness; `ambient_shift`, `ambient_exact` give exactness of the specified unbounded derived functor. `computes` states that the canonical comparison computes it termwise on every complex. |
| Left adjoint to exact restriction | The existing `pbcDerivedScalarAdjunction` has type `pbcDerivedExtend φ ⊣ pbcDerivedRestrict φ`. `restriction_exact`, `restriction_colimits`, `restriction_shift`, `restriction_derived_exact` record exact restriction at both levels. No ambient object is assumed bounded, constructible or complete. |
| Carries I_T into archived C_T^c(E) | `J` lands in the existing `BoundedConstructible (condensedRingObj (Profinite.continuousCoefficientRingObj E) T)`, and `integral` is a natural isomorphism from rationalization followed by J, the full inclusion, and the module encoding to the integral inclusion followed by actual F_T. Thus its image has exactly the archived bounded/local-finite-presentation condition. |
| Exact J | `[additive : J.Additive]`, `[shift : J.CommShift ℤ]`, `exact : J.IsTriangulated` for the existing induced triangulations |
| E-linear J | `linearity` quantifies over every pair K,L, every rational arrow f and every a:E, and equates the images of `a • f` and `a • J(f)` in the faithful existing sectionwise encoding. The domain action is the existing `pbcScalarRationalLinear`; the target action is Mathlib's existing derived `Linear` action of the coefficient section ring, evaluated at the canonical constant section with value `a`. The explicit `SMul.smul` dictionary comes from `SheafOfModules.homLinear` and `DerivedCategory.instLinear`. The continuous constant uses the recorded spectral topology `coefficientExtensionNormedField l E`, exactly as the coefficient sheaf does. This specifies the canonical action, not an arbitrary chosen linear structure. |
| J(K)=F(K) | `integral` is the natural comparison expressing this equality in the two coefficient encodings. It simultaneously fixes the comparison on arrows. |
| J(u/varpi^n)=varpi^(-n)F(u) | `fractions`, for all integral K,L,u and all `n : ℕ`. The source fraction is the localized inverse-power scalar times `pbcRationalization.map u`; the equation composes the two sides with the same components of `integral`. The inverse power is the actual element of E obtained from the recorded uniformizer. |
| Ambient unit is the derived image of m↦1⊗m | `tensor_unit` identifies the ordinary unit on every module, site object and section with `pbcTensorSection ... 1 m`. `unit` then states its derived-image equation on EVERY cochain complex, using exactly `pbcComplexCounit` and the canonical exact-restriction factorization. |
| No full faithfulness or essential surjectivity | No fields assert either property. The conclusion is `Nonempty` of this scalar-functor record, not an equivalence or the stronger realization record. |

Dependency declarations read and reused:

- `Sheaf.Paper.IntegralUniformCoefficient`:
  `AlgebraicGeometry.Scheme.pbcBoundedConstructibleComplete` and its underlying
  published `PbcBoundedConstructibleComplete`. The latter supports both the
  recorded unlifted specialization and the Type-u lifted specialization here.
- `Sheaf.Paper.PbcRationalCategory`:
  `PbcRationalDerivedCategory`, `PbcRationalCategory`, `pbcRationalization`,
  `pbcCompletedScalarSections` and their inherited linear structures.
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing`:
  `Profinite.isCommMonObj_continuousCoefficientRingObj`, the reexported
  `condensedRingObj`, `BoundedConstructible` and `boundedConstructible` framework.
- `Sheaf.Paper.ContinuousCoefficientModuleEncoding`:
  `continuousRingModuleEquivalence`, `ringModuleEquivalenceOfIso`,
  `sectionModuleComapIso`, the regular/free comparisons, and the spectral metric
  and integral-ring identifications. The statement directly composes the existing underlying
  `sectionModuleEquivalence` with `ringModuleEquivalenceOfIso`, so E need not
  be restricted to Type 0; it adds no duplicate encoding declaration.
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction`:
  `continuousCoefficientImmersionRestriction` and the existing continuous
  coefficient rings and normalization predicates.

The constructions are used directly from their owning dependencies. No shorthand
from the stronger `Sheaf.Paper.CondensedERealization` is imported. In particular,
`sectionModuleEquivalence` is from
`Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`, and the scalar
section action is Mathlib's `SheafOfModules.homLinear` transported to the derived
category by `DerivedCategory.instLinear`. This is the usual E action: a scalar
`a` is the compatible section family of constant continuous functions with value
a. Both linearity and the inverse-uniformizer fraction formula use this same
canonical action. No arbitrary scalar structure is supplied as a hypothesis.
`PbcScalarExtension` supplies the existing raw rational triangulation and field
scalar action. The remaining imports are the stated proof dependencies and the
archived bounded-constructible triangulation companion. The normalized finite
quotient identification `integralCoefficientULift` is publicly imported from its
owner `IntegralStratifiedPerfectCharacterization`.

Edge cases checked before and after writing:

- The empty scheme is permitted: no point, nonemptiness, connectedness, affine
  chart or dimension equality is assumed; the local-unit condition is universal.
- Zero objects, zero maps and zero integral local models are included. Target
  constructibility remains the archived predicate with finite presentations,
  including ranks zero; no local-freeness predicate replaces it.
- The fraction exponent is every natural number, including zero. In that case
  the equation reduces to the naturality equation for `integral`.
- Ambient unit and exactness clauses quantify over unbounded complexes without
  imposing the integral predicate or a K-flatness assumption. The ordinary
  normalized unit and universal comparison keep the same coefficient inclusion.
- Arbitrary ramification is allowed; no unramified, algebraically closed,
  characteristic-zero base-field, or smoothness hypothesis was introduced.
- `universe u` is explicit, with E,k,T in the common ambient universe and
  coefficients/modules in the existing u+1 universe. This allows raising the
  ambient universe for any such input and retains small-site object universe
  u+1 and morphism universe u. There is no equality imposed on those universes.

Searches actually run:

1. `msearch.py ... leanfinder` query:
   `Exact scalar extension from integral pro-etale coefficients to a finite l-adic field factors through raw rationalization with the fraction formula`.
   Eight hits: `BDeRhamPlus`, `BDeRham`, `PreTilt.mk_comp_untilt_eq_coeff_zero`,
   `WittVector.exists_frobenius_solution_fractionRing_aux`,
   `fontaineThetaInvertP`, `Algebra.FormallySmooth.exists_adicCompletionEvalOneₐ_comp_eq`,
   `instCommRingBDeRhamPlus`, and
   `WittVector.factorPowSucc_comp_fontaineThetaModPPow`. None is this statement.
2. `msearch.py ... loogle 'DerivedCategory, Functor'`: zero hits.
3. `msearch.py ... grep 'realizationScalar|scalar.*[Rr]ealization'`: zero hits.
4. `msearch.py ... leansearch` query:
   `Exact scalar localization of integral constructible sheaf complexes to continuous field coefficients`.
   Eight hits concern ordinary localization scalar towers, continuous linear or
   alternating scalar restriction, and algebraic module localization. None
   states the specified pro-etale functor.
5. `rg` over `lean/Sheaf` and `lean/WeilConjectures` for realization/scalar,
   `PbcRational`, `pbcRationalization`, and the expected declarations found the
   existing coefficient/encoding/derived/rational interfaces reused above.
   `ContinuousRationalDerivedRealization` and `CondensedERealization` also carry
   stronger equivalence conclusions; neither is exactly this node's statement.
6. `grep -rn 'lem-weil-pbc-realization-scalar-functor' lean/WeilConjectures`
   found no declaration. A final `rg` of Mathlib, both project source trees and
   `dag/lean_names_upstream.json` for the two new full-name suffixes found no
   collision.

No new DAG nodes, dependency modules, or statement corrections are needed.
No statement is disputed.

All lines are at most 100 characters and `autoImplicit` is false in the statement module.

## Returned declaration-list repair (2026-10-21)

The return for immutable head `2f2b6bfb4b71` names two nonexistent entries in
`lean.declarations`: `WeilConjectures.realizationAbSheafify` and
`WeilConjectures.realizationAbBijective`. Both are removed. The item now lists
exactly `WeilConjectures.RealizationScalarFunctorData` and
`WeilConjectures.realization_scalar_functor`, both declared by this module.
Neither removed name is used by the statement.

I read the retained report and first ran the required saved-packet dry run.
That exposed a stale private import in an inherited consumer, and subsequent
checks exposed the expensive `CondensedERealization` dependency. The final
repair removes that unnecessary import. Its shorthand definitions are replaced
by the exact already-existing underlying expressions, not copied definitions.
Its field scalar action is expressed by the existing section-ring action at
constant sections. The isolated constant-section action compiled in 7.7 seconds
(sandbox) and 5.7 seconds (library).

This keeps all coefficient normalizations, ambient functors, adjunction, units,
exactness clauses, integral natural comparison, E-linearity, and fractions.
The theorem signature is unchanged. The old dependency chain through integral
localization continuity is no longer needed simply to name coefficient objects.
No unrelated dependency source is delivered or modified. The item node changes
only in `lean`; its mathematical statement and both dependency lists are retained.

## Second reading by NX

I compared every hypothesis and record field against the node after expanding
the shorthand. The conclusion constructs a functor with the specified action;
it asserts no equivalence, full faithfulness, or essential surjectivity. The
constructibility predicate remains the archived finite-presentation predicate.
The coefficient comparison is fixed on all profinite test functions, every
finite quotient, and all section values. Exactness and the unit concern all
ambient complexes. The fraction equation uses the same integral comparison on
both endpoints, including exponent zero, with the actual inverse power of the
recorded uniformizer as constant scalar section.

Both recorded declaration names exist in the delivered module. Its only `sorry`
is the named theorem with its complete natural-language proof in the docstring.
No definition data, action, comparison functor or ambient adjunction is postponed.
The declared signature in the JSON is copied verbatim from the Lean file. JSON
uses indent 1, unescaped Unicode and a final newline. The maintainer's independent
reading remains required.

## Compilation and delivery check

The final module passed the prescribed `scompile.py` in both sandbox form
(34.5 seconds) and named-library form (41.0 seconds), with no errors or warnings.
The final `deliver2.py --no-push` passed preflight and compilation, producing
reviewable dry-run commit `a448aa52849`. The source was not changed afterward.

A mechanical self-check confirms that the JSON signature equals the source
signature verbatim; both listed declarations are the two declarations in the
module; the module has exactly one `sorry`; all Lean lines are at most 100
characters; and there is exactly one delivered Lean file and one delivered node
file. Comparing with the current shared node shows that every non-`lean` field
is identical, including `statement`, `stmt_deps`, `proof`, and `proof_deps`.
The packet contains no dependency repair, new node, diagnostic file, or auxiliary
theorem. All source reading and all edits respected the read-only clone and
sandbox boundaries; all compilation and delivery used the prescribed wrappers.
