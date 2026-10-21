## Worker report

The module `Sheaf.Paper.RealizationAdjointComparisons` states
`WeilConjectures.realization_adjoint_comparisons`, with its proof postponed. The
natural-language node is unchanged. The auxiliary definitions only name restrictions,
existing adjunctions and comparison isomorphisms, actual scalar transport, and the two
equations. All their data is supplied by the published dependency constructions.
There is one `sorry`, in the named main theorem; its docstring gives all seven DAG
proof steps, including the ambient coefficient-change calculation and the rational
extension. No additional definition node or dependency repair is needed.

Hypotheses and clauses, matched to the Lean:

- The prime is `(l : ℕ) [Fact l.Prime]`. The finite normed extension is
  `(E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. The actual valuation ring and fixed uniformizer are
  `PbcIntegralRing l E` and `pbcUniformizer l E`, the dependency's existing ULift
  presentation. No new ring, uniformizer choice, or coefficient topology is introduced.
- The positive prime characteristic different from l is `(k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]`.
- `T U : RealizationPullScheme l k` is the completed-pull dependency's record: each
  has an actual scheme, its structure over `Spec k`, locally finite type plus
  quasi-compactness (finite type), separatedness, Noetherianity, a finite Krull
  dimension witness, and local invertibility of l. Its object universe and morphism
  universe agree with the published small pro-etale sites, not an artificial
  equality between site-object and site-morphism universes.
- `h : T.scheme ⟶ U.scheme` with `[h.IsOver (Spec (.of k))]` is any k-morphism.
  There is no properness, immersion, or nonemptiness requirement.
- `sT` and `sU : RealizationScalarFunctorData ...` are the specified ambient scalar
  extensions. Their `integralIso`, its residue normalizations, `inclusion`, and
  `inclusion_normalization` supply exactly the completed-to-continuous integral
  coefficients followed by A→E. `s.scalarMap` is that composite. Their `sectionIso`
  and published derived module encoding identify the continuous E coefficient
  operations with the sectionwise operations used here.
- The integral categories are the existing
  `PbcBoundedConstructibleComplete ... (pbcIntegralDatum l E)`. Their defining
  predicate has exactly intrinsic completeness, uniform constructible reductions,
  and compatible etale origins. Their morphisms are all ambient morphisms.
  The raw rational categories are `PbcRationalCategory ... (pbcUniformizer l E)`;
  they use the existing scalar tensor localization and have the same objects.
- `a : RealizationCompletedPullArrow T U h sT sU` is the specified completed-pull
  comparison record, including ordinary and completed integral preservation,
  invertibility of the *actual* strict completion unit, and `alpha` normalized by
  the ordinary scalar comparison on complexes and tensor units. `a.integralCompleted`
  is P_h; `realizationAdjointAlpha a` is precisely a.alpha, re-associated through
  the identity-on-data full-subcategory inclusion. Its definition uses
  `ObjectProperty.liftCompιIso`, not an additional comparison choice.
- `b : RealizationLocalizedPushData l E h sT sU` is the specified push comparison
  record, including ordinary integral constructibility, completed-image agreement,
  invertible beta, its extension/restriction adjunct normalization, and the actual
  continuous direct-image encoding. `b.integralPush` restricts that ordinary
  ambient derived direct image; it does not complete or replace it.
- The conclusion first identifies the two rational coefficient isomorphisms,
  `∃ rationalCoefficients : b.rationalPullback = a.rationalCoefficient`. This is
  concluded, not assumed: both records normalize the same precomposition map.
  The resulting `eqToHom` only aligns their encodings of the same direct image.
- `∃ adj : a.integralCompleted ⊣ b.integralPush` is characterized on *every* Hom
  transpose: its underlying ambient arrow is heterogeneously equal to the
  `pbcActualDerivedAdjunction` transpose after precomposition by
  `pbcActualStrictCompletedPullUnit`. Thus its counit uses the inverse of that
  actual unit, as required. HEq handles the dependency's equal coefficient-map
  presentations of ordinary push without choosing another ambient adjunction.
- `realizationContinuousAdjunction a` is the existing
  `proEtaleRingDerivedAdjunction` with the actual continuous rational coefficient
  isomorphism; its functors are P_h^E and Q_h^E in sectionwise module coordinates.
- `RealizationAdjointEquations` has exactly two conjuncts. Its first is
  `FU.map (adj.unit.app N) ≫ beta.app (P.obj N) ≫ QE.map (alpha.app N) =
  adjE.unit.app (FU.obj N)` for every N. Lean's left-to-right composition gives
  precisely Q^E(alpha_N) beta_PN F_U(eta_N) = eta^E_F_UN.
  Its second is `FT.map (adj.counit.app M) = alpha.app (Q.obj M) ≫
  PE.map (beta.app M) ≫ adjE.counit.app (FT.obj M)` for every M: exactly the
  displayed counit equation. Together these express the asserted mate condition;
  under Mathlib's `mateEquiv` direction convention beta is the mate of alpha.inv.
- The final existential supplies additivity and A-linearity of the *same* integral
  Q, its `ScalarLocalization.transport` (named `realizationRationalPush`), and
  `adjR : a.rationalCompleted ⊣ realizationRationalPush ...`. For every raw object
  its unit and counit are explicitly the rationalization images of the preceding
  integral unit and counit. Thus this is the localized adjunction, rather than
  an arbitrary adjunction between the two functors.
- `alphaR` and `betaR` are natural isomorphisms between the corresponding rational
  composites. Their components at *every* integral object (hence every raw object)
  are prescribed by a.alpha and b.beta, conjugated by `realizationAdjointIntegral`,
  the existing scalar-functor integral normalization. The final
  `RealizationAdjointEquations adjR ... alphaR.hom betaR.hom` states both equations
  for all raw objects. This includes naturality on arbitrary localized arrows;
  no rational lattice and no idempotent completion is used.

Dependency declarations read and used:

- `Sheaf.Paper.IntegralUniformCoefficient`, the recorded specialization
  `AlgebraicGeometry.Scheme.pbcBoundedConstructibleComplete`, and its reexported
  `PbcBoundedConstructibleComplete`/`PbcIsBoundedConstructibleComplete`. As in both
  realization dependencies, the existing `pbcIntegralDatum` ULift specialization
  is used for E : Type u; the other convenience specialization takes E : Type (u+1).
- `Sheaf.Paper.PbcRationalCategory`: `PbcRationalDerivedCategory`,
  `PbcRationalCategory`, `pbcRationalization`, and the published scalar structures.
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing`:
  `Profinite.isCommMonObj_continuousCoefficientRingObj`, reexported coefficient
  ring and internal-module operations. No second continuous ring is defined.
- `Sheaf.Paper.RealizationScalarFunctor`: `RealizationScalarFunctorData`,
  `realization_scalar_functor`; in particular its integral normalization and J.
- `Sheaf.Paper.RealizationCompletedPull`: `RealizationPullScheme`,
  `RealizationCompletedPullArrow`, `integralCompleted`, `rationalCompleted`,
  `continuousPull`, `realizationPullRationalScalar`, `realizationPullIntegral`,
  `realization_completed_pull`.
- `Sheaf.Paper.RealizationLocalizedPush`: `RealizationLocalizedPushData`,
  `RealizationScalarFunctorData.scalarMap`, and `realization_localized_push`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` reexports the general
  ring-sheaf interface; the appropriate `proEtaleRingDerivedPullback`,
  `proEtaleRingDerivedDirectImage`, `proEtaleRingDerivedAdjunction` are used, since
  the recorded constant-ring convenience declaration is not the continuous ring.
- `Sheaf.Paper.PbcRationalTransport`: `ScalarLocalization.transport`, the
  previously stated exact/linear/natural-transformation transport interface.
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction`:
  `continuousCoefficientImmersionRestriction` and its coefficient normalization
  predicates, retained in the scalar/pull/push records; no immersion condition is
  imposed on this theorem's h.
- Proof imports: `Sheaf.CategoryTheory.LocalizationInverseImageCoherence`,
  `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`
  (`proEtaleRingSheafChangeAdjunction`, including its ambient adjunct equation),
  and `Mathlib.CategoryTheory.Adjunction.Mates` (`mateEquiv`, the mathlib match
  of `def-weil-pbc-adjunction-mate`). All other stated proof dependencies are
  among the public imports above.

Sources read: the complete node and its seven-step proof; every statement dependency's
statement and recorded interface, including full record signatures and docstrings;
Bhatt--Scholze Remark 6.8.15 (PDF text, ambient and restricted operations, pp.61–62);
the current blueprint finite-extension proof (integral lattice and rational transport).
Remark 6.8.15 supplies the setting; the equations use the explicit agent calculation
recorded in this node, as its proof_origin already says.

Edge cases checked: identity h (the same actual completion unit is retained), empty
schemes and zero objects (no nonempty or nonzero assumptions), varpi-torsion integral
objects (their scalar realization can vanish), arbitrary fractions and exponent zero
(raw objects unchanged, with the tensor-one unit/counit formulas), and ambient
restriction of a realized object that is not integral constructible (the proof uses
ambient change-of-rings adjuncts; no constructibility assumption on that restriction).
No node fault or statement correction was found.

Searches actually run:

- msearch LeanFinder, `Scalar extension pullback pushforward comparisons preserve
  adjunction units and counits`: eight hits on underived module/sheaf adjunctions,
  scheme conjugate comparisons, and ordinary units; no specified realization result.
- msearch Loogle, `CategoryTheory.Adjunction, "mate"`: twelve hits, including
  `mateEquiv`, `mateEquiv_counit`, `unit_mateEquiv` and composition lemmas. They
  provide the general mate formalism, not these specified comparisons.
- msearch grep, `mateEquiv_counit|localization_unit_app` in CategoryTheory: five
  matches in Localization/Adjunction, Adjunction/Mates and Monoidal/Closed/Functor.
- msearch LeanSearch, `scalar localization adjunction pullback direct image unit
  counit compatibility`: eight hits on generic localized/derived adjunctions and
  the module scalar counit; no theorem for these specified realization maps.
- rg in both `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `realization.*adjoint|Realization.*Adjoint`: unrelated closure/finite-model
  realization files only, no matching statement. Additional rg for each proposed
  helper name and `RealizationAdjointEquations` in both trees and the upstream
  declaration index found no collisions. Source searches for the actual derived
  pull/push adjunctions and transport APIs located the declarations listed above.

Validation: scompile.py compiles the statement both as the private sandbox module
and as `Sheaf.Paper.RealizationAdjointComparisons` against the live published build.

## Second reading by Q09

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
