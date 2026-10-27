## Worker report

The delivery states the unchanged node in `Sheaf.Paper.PodReconstructionRawRationalNaturality`.
The main declaration is `WeilConjectures.PodRawReconstruction.reconstructionRawRationalNaturality`;
`reconstruction_identityCompactSupport` states the node's strict identity-tower clause.
All theorem proofs are `sorry`; all five helper definitions have actual bodies and no
postponed data. There are no new nodes, dependency replacements or statement changes.
The auxiliary predicates and identity comparisons belong to this node's realization,
rather than introducing a second constructible category, completion or rationalization.

Clause-by-clause correspondence:

- `D : FiniteFieldDatum.{u}` supplies the finite field, algebraic closure and characteristic;
  `point D` is the existing Spec(k). `l`, `[Fact l.Prime]`, and `hl : l ≠ D.p` give
  exactly the coefficient-prime hypothesis. `E`, `L`, their Field, Q_l-Algebra and
  FiniteDimensional instances and `ι : E →ₐ[ℚ_[l]] L` express the finite coefficient
  extension. An algebra embedding is the presentation-independent form of E ⊂ L;
  no ramification or equal-uniformizer condition is imposed.
- `A` and `B` are the recorded actual coefficient-system calculi, not extra exactness
  assumptions. `PodCompletionScalar.completion D l E A` is literally A.reduction followed
  by coefficientSequenceLimit. `IntegralRealization` prescribes its underlying objects
  by equality, every derived arrow by HEq, and every unit component by HEq with
  A.adjunction.unit. HEq transports the specified equal endpoints; it does not identify
  arbitrary morphisms. The inverse of this actual unit is `unit.inv`, not new chosen data.
- The categories are precisely `sfIntegralConstructibleCategory` and
  `sfRationalConstructibleCategory`. The former's existing predicate includes completeness,
  constructible reductions and ONE uniformly bounded reduction interval. The latter has
  unchanged objects and its existing tensor Hom groups. No completion or Karoubi envelope
  is substituted. Site objects retain universe u+1 and site morphisms u.
- The first two conjuncts assert ambient O_E/O_L-linearity. The existential H/H' and
  IntegralRealization assertions express restriction to the full constructible categories;
  the following two Linear assertions express their restricted integral linearity.
- `RationalRealization` fixes J's object and every pure-tensor arrow to H's object and
  arrow. Its Additive and Linear conjuncts extend the formula to every finite sum, including
  torsion Hom groups. The library uses scalar-first localization tensors. Its existing
  `sfRationalHomCoordinates` and `sfRationalCoefficientEquiv` identify these with
  Hom_O_E(C,D) tensor E. Thus linearity over Localization.Away(varpi) is exactly E-linearity
  under the fixed coefficient identification; this introduces no alternate rational category.
- The same predicate sets BOTH rational unit and inverse components equal to Q of the
  actual integral components. `unitRat` is a natural isomorphism id ≅ J, hence gives both
  inverse equations. The two displayed equations in the predicate quantify over every
  rational arrow h, not merely arrows in the image of the localization functor.
- The main theorem's beta is an integral natural isomorphism between H followed by the
  existing completed scalar functor and that functor followed by H'. Its inverse-unit
  equation identifies it uniquely with the specified beta in
  `PodCompletionScalar.completionUnitScalarIntertwining`: cancel the invertible unit'.inv
  on the right. This uses the dependency's unit equation and fixes the whole derived
  arrow, including any phantom component; finite-level detection is not used.
- betaRat uses the existing `sfRationalScalarExtension`. Its components are HEq to
  Q_L(beta_C). Its final equality is exactly betaRat followed by v_L equals S(v_E), with
  composition written in Lean's left-to-right convention. NatIso gives naturality and
  invertibility for all rational arrows, without choosing integral lifts of isomorphisms.
- `finiteOpenIdentity` is the actual identity extension-by-zero comparison, transported
  through the published intrinsic-module equivalence; `finiteIdentity` then uses derived
  functor comparison and the fixed global-evaluation identity direct image.
  `finiteRestrictedIdentity` applies this comparison to actual scalar reduction/restriction.
  These definitions contain genuine compositions of already defined natural isomorphisms.
- `reconstruction_identityCompactSupport` supplies the identity compactification, its
  chosen strict tower T from `exists_compactSupportReductionTower`, the level comparisons
  e and whole-tower comparison theta. The first component hk is the derived consequence
  IsUnit(l in k) of hl, existentially supplied rather than assumed. Evaluation of theta,
  then e and finiteRestrictedIdentity, equals A's exact reduction-evaluation comparison.
  The next clause imposes the actual quotient transition for EVERY n ≤ m. Thus this is
  an identification on derived arrows and all transition maps, not just a levelwise claim.
- eta is literally the underlying identity comparison of H with completion. kappa and
  rho have a specified pasting with eta and theta. Every rho projection is the chosen
  Roos projection used in `sfIntegralCompactSupportValue`, so an arbitrary limit
  isomorphism cannot stand in for the compact-support operation. Finally kappaRat is
  componentwise Q(kappa), identifying J with the fixed raw rational identity compact
  support functor. The whole strict identity-tower clause is thereby stated explicitly.

Dependencies (recorded modules and declarations read; proof modules are imported too):

- `def-weil-finite-coefficient-point`: `Sheaf.Paper.FiniteCoefficientPoint`, `WeilConjectures.pointQbarFibre`.
- `def-weil-completed-integral-coefficients`: `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`, `WeilConjectures.integralConstantToCompletionOfUniverses`.
- `lem-coef-derived-system-evaluation-calculus`: `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`, `WeilConjectures.coefficientDerivedSystemEvaluationCalculus`.
- `lem-trf-completion-unit-strict-quotient-model`: `Sheaf.Paper.CompletionUnitStrictQuotientModel`, `WeilConjectures.CompletionUnit.completionUnitStrictQuotientModel`.
- `def-weil-derived-complete`: `Sheaf.Paper.DerivedCompleteOnSlices`, `WeilConjectures.IntegralOnSlice.IsComplete`.
- `lem-pur-normalized-reconstruction-adjunction-calculus`: `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus`, `WeilConjectures.purNormalizedReconstructionAdjunctionCalculus`.
- `def-weil-derived-complete-integral-detailed`: `Sheaf.Paper.SfIntegralConstructible`, `WeilConjectures.sfIntegralConstructible`.
- `def-weil-rationalization-karoubi`: `Sheaf.Paper.SfRationalizationKaroubi`, `WeilConjectures.sfRationalConstructibleCategory`.
- `lem-weil-integral-scalar-extension-well-defined`: `Sheaf.Paper.IntegralScalarExtensionWellDefined`, `WeilConjectures.integralScalarExtensionWellDefined`.
- `lem-pod-completion-unit-scalar-intertwining`: `Sheaf.Paper.PodCompletionUnitScalarIntertwining`, `WeilConjectures.PodCompletionScalar.completionUnitScalarIntertwining`.
- `def-weil-integral-rational-qbar-compact-support`: `Sheaf.Paper.QcqsCompactSupportRealization`, `WeilConjectures.sfQcqsCompactSupportRealization`.
- `lem-weil-compact-support-reduction-tower-functor`: `Sheaf.Paper.CompactSupportReductionTower`, `WeilConjectures.exists_compactSupportReductionTower`.
- `lem-weil-proetale-countable-products-exact`: `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`, `AlgebraicGeometry.Scheme.ProEt.countableProducts_exact`.
- `lem-weil-strict-roos-comparison`: `Sheaf.CategoryTheory.StrictRoosComparison`, `CategoryTheory.strictRoosComparison`.
- `lem-weil-integral-constructible-linear`: `Sheaf.Paper.SfIntegralConstructibleLinear`, `WeilConjectures.sfIntegralConstructible_linear`.
- `def-compact-support-direct-image-detailed`: `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`, `AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport`.
- `def-weil-extension-by-zero`: `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`, `AlgebraicGeometry.Scheme.sfIntrinsicExtensionByZero`.
- `def-weil-derived-direct-image`: `Sheaf.Paper.SfDerivedDirectImage`, `WeilConjectures.SfIntegralDirectImage`.
- `lem-sf-compact-support-restriction-of-scalars`: `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`, `AlgebraicGeometry.ProEtale.intrinsicCompactSupportRestriction`.
- `lem-pur-semilinear-scalar-localization`: `Sheaf.CategoryTheory.SemilinearScalarLocalization`, `CategoryTheory.ScalarLocalization.existsUnique_semilinear_extension`.
- `def-weil-linear-scalar-localization`: `Sheaf.CategoryTheory.ScalarLocalization`, `CategoryTheory.ScalarLocalization`.
- `lem-weil-integral-scalar-extension-constructible`: `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`, `WeilConjectures.sfIntegralScalarExtension_constructible`.

Edge cases checked before finalization: zero objects and zero/empty sums satisfy the
same additive tensor formulas; torsion morphisms may vanish after tensoring and no
faithfulness of Q is assumed. The raw category keeps a torsion object even when it
becomes isomorphic to zero. n=0 denotes the positive exponent n+1=1, and m=n gives
identity transition; there is no missing positive-level restriction. The identity field
extension L=E is allowed, as are ramified extensions and arbitrary embeddings. The
base is the nonempty geometric point specified by the node, so an empty-scheme
hypothesis is not silently added. All rational morphisms, including inverses which
have no integral isomorphism lift, are covered by the universal h binder. The scalar
comparison is characterized by cancellation of an isomorphism, not conservativity of
finite projections. No disputed statement or node fault was found.

Existing-declaration searches:

- `msearch.py ... leanfinder` with "Completion reconstruction is linear and descends to
  rationalized Hom tensor groups with natural unit and inverse and scalar extension
  compatibility": eight ordinary AdicCompletion tensor hits, no matching statement.
- `msearch.py ... loogle` with "Functor.Linear, NatIso": no hit (Functor.Linear unknown
  in that search environment).
- `msearch.py ... grep` with "reconstruction.*rational|rational.*reconstruction" in
  CategoryTheory: zero hits.
- `msearch.py ... leansearch` with "A linear functor extends to scalar localization and
  natural isomorphisms descend": ordinary linear-map/localization and Free.ext hits,
  no actual quotient-system reconstruction comparison.
- `rg` over the prescribed WeilConjectures and Sheaf trees for reconstruction/rational
  names and the item id, and the upstream declaration-name index: no existing declaration
  of this node. Existing scalar localization, actual reconstruction, identity open
  extension and direct image comparisons were reused, rather than copied.

Validation: scompile.py compiled the complete module in both the private sandbox and
its intended library module path, with no errors or warnings. Every theorem has a
source/blueprint docstring with the full natural-language proof plan. The node copy
changes only lean, preserving the accepted split and its statement verbatim.

## Second reading by Q83

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
