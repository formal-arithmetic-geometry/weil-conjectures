## Worker report

Delivery: `Sheaf.Paper.IdentityCompactificationLimitComparisons`, namespace
`WeilConjectures.IdentityCompactificationLimit`. The theorem
`identityCompactificationLimitComparisons` states the two equalities of specified
integral comparisons and their coefficient images. Its only postponed proof is
`sorry`; all helper definitions contain actual maps, and the proper comparison
is an actual isomorphism constructed from the recorded ones.

Source read: the current blueprint at
`literature/blueprint/latest/blueprint/sec-six-functors/sk-lem-finite/prop-cohomological-finiteness.proof.md`,
Step 3 (the proper case). The source has moved from the older chapter/path in the
node's provenance. It says that the proper comparison is canonical and Frobenius
equivariant. The node supplies the detailed agent expansion of the two operation
comparison squares, not an assertion quoted verbatim from Deligne. The module
and theorem docstrings distinguish current Step 3 from expanded DAG Step 6.

Hypotheses and clauses, in order:

- `D : FiniteFieldDatum.{u}` is the recorded tuple p,a,q,k0,k, including primality,
  positive a, cardinality, and the arbitrary fixed algebraic closure.
- `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p` are exactly the coefficient prime data.
  `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`,
  `[FiniteDimensional ℚ_[l] E]` are the abstract finite coefficient field. Its
  integer ring, chosen uniformizer, and quotient rings are the existing Padic
  constructions used by the imported operation models. For a finite field inside
  the chosen closure the last clause specializes E to the existing `Coefficient`
  model of that very subextension. There is no replacement coefficient ring.
- `Y₀ : Over (Spec (.of D.k₀))`, `[IsProper Y₀.hom]` state properness over k0.
  Properness already supplies finite type; no smoothness, connectedness, nonemptiness,
  or projectivity is required. `D.geometricFiber Y₀` is the existing geometric fibre,
  `.left` is Y and `.hom` is a. The point is literally `Spec (.of D.k)`.
- `D.geometricFrobenius Y₀` is gY. g_s is explicitly `Spec.map` of the recorded
  geometric field Frobenius, including its chosen `Fintype.ofFinite` convention.
  No k-linearity hypothesis is imposed on either semilinear map.
- `compactification D Y₀` is `Compactification.ofIsProper` for a, with identity
  open immersion. Its properness witness is Mathlib's base-change witness for
  `pullback.snd`. There is one compactification at every positive exponent.
- `M : sfIntegralConstructibleCategory l E (D.geometricFiber Y₀).left` is the stated
  integral bounded constructible input. `reduction` is the recorded strict-system
  reduction. `systemDirect`, `integralComparisonDerivedSequencePullback`,
  `systemDerivedOpen` and `coefficientSequenceLimit` are respectively F_a, G, J
  and L_s. The last already includes exact restriction to completed-coefficient
  strict towers before the total limit, not a limit of separately chosen evaluations.
- `openIso` is the canonical u: apply `ofNatIsoRight` with the existing
  `integralComparisonSystemUnit` to the recorded open adjunction, then
  `leftAdjointUniq Adjunction.id`. This is the exact canonical normalization in
  `identityCompactificationSystemMate`, not a fresh choice of an isomorphism.
- `systemIso` is F_a(u), whiskered with the actual system direct image.
  `properComparison` is the component of the projection-normalized
  `compactRealization` followed by `coefficientSequenceLimit.mapIso systemIso`.
  This is kappa_M, the actual identity-open comparison of the specified towers.
  The ordinary endpoint is `integralDirectImage`; `directImage_roos` records its
  equality with an `SfIntegralDirectImage` presentation. An arbitrary Roos triangle
  and an arbitrary isomorphism supplied by `properCompactCoincidence` are not used.
- `alphaLeft` is alpha_! followed by L_s(h_S), with h_S = G_s(F_a(u_RM)).
  `alphaRight` is Lg_s^*(kappa_M.hom) followed by the actual `sourceComparison`
  for F_a. Their equality is the first conjunct, with Lean's composition order.
- `betaLeft` is the actual `compactBeta` followed by kappa at
  `(constructibleIntegralPullback l E gY).obj M`, exactly M'.
  `betaRight` is L_s(h_T) followed by the inverse `reductionPullbackIso`, whiskered
  with F_a and L_s. Thus it is the specified beta_* after L_s(F_a(u_GYRM)).
  Their equality is the second conjunct. All whole-system transitions remain in
  the types and in the functors; equality is not inferred by finite evaluation.
- `rationalAlphaLeft/Right` and `rationalBetaLeft/Right` apply the existing
  `ScalarLocalization.localization` to these same composites. The localization
  uses the canonical ambient constant-coefficient linear action. This expresses
  the actual tensor-with-one Hom map: the integral constructible category is full,
  so between these objects its Hom group is the identical ambient Hom group, and
  its raw rational Hom is the identical tensor product. No larger input domain or
  different constructible operation is asserted by this presentation of the Hom.
  The third and fourth conjuncts state exactly their scalar-localized equalities.
- The final quantified clause uses arbitrary `Ω : Type v` with its algebraic closure
  structures, any `E₀ : AlgebraicallyClosedCoefficients.Index l Ω`, and any integral
  representative N at the existing finite model `Coefficient.{u} l Ω E₀`. It states
  both equalities of common finite coefficient-field representatives. The node
  asks for these representatives; their common-stage classes are obtained by the
  recorded stage inclusion, whose Hom map preserves equality. No rational object
  is reduced modulo a uniformizer and no idempotent completion is used.

The residue-field invertibility structures in the definitions are derived from
`hl`: on Y from `sfWeilPrimeInvertible`; on s by mapping
`finiteFieldDatumPrimeUnit` to each residue field and rewriting `map_natCast`.
They are not additional theorem hypotheses. `structureIsOver` and
`structureProper` merely expose the existing geometric structure-map and
base-change instances under their literal `.hom` spelling.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `FiniteFieldDatum.geometricFiber`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the constructions from
  `Sheaf.NumberTheory.Padics.CoefficientExtension`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`;
  its separatedness, universal closedness and finite-type consequences.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`:
  `FiniteFieldDatum.geometricFrobenius`, `galoisMap`, projection equations.
- `Sheaf.Paper.FrobeniusGeometricExchange`: the canonical geometric exchange
  wrappers and their `SystemOperationExchangeRealization` dependencies.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `sfIntrinsicExtensionByZero`; the strict-system open operation is the published
  exact-derived extension with this same presheaf/sheafification normalization.
- `Sheaf.Paper.ProperCompactCoincidence`: `properCompactCoincidence`, the proper
  comparison assertion, and `properCompactPointOver`.
- `Sheaf.Paper.QcqsCompactSupportRealization`: `sfQcqsCompactSupportRealization`
  and its normalization specification, used by the recorded `compactRealization`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleIntegralPullback` and the
  existing rational and common-stage coefficient conventions.
- `Sheaf.Paper.SemilinearDerivedSections`: `SemilinearDerivedSectionsData`,
  `semilinearDerivedSections`, `AdjunctionEvaluation`, `evaluation_mate`.
- `Sheaf.Paper.SfDerivedDirectImage`: `SfIntegralDirectImage` and the canonical
  quotient-transition direct-image tower.
- `Sheaf.Paper.SystemOperationExchangeRealization`: `models`, `reduction`, `realize`,
  `sourceComparison`, `reductionPullbackIso`, `compactRealization`, `compactAlpha`,
  `compactBeta`, `systemDerivedOpenAdjunction`, `systemDirect`, `directImage_roos`.

The recorded proof-only modules are imported without `public`: evaluation calculus,
operation reduction, identity system mate, integral pullback system comparison,
primitive counit comparison, integral direct-image constructibility, isomorphism
pullback, and completed Rlim. The two proof dependencies with no recorded Lean
module (`lem-weil-pbc-proper-base-change`,
`lem-weil-proper-integral-tower-comparison`) do not require an additional statement
interface to type this theorem: proper base change is already the Mathlib instance,
and the actual tower-normalized kappa is constructed from the published canonical
maps, as specified by the item's statement. Their mathematical assertions remain
in the natural-language proof plan for stage 3.

Searches made before writing:

- msearch leanfinder: "Naturality of the canonical source and target operation
  comparisons under identity compactification and total inverse limit". Eight hits,
  including `InverseSystem.globalEquiv_naturality` and condensed comparison results;
  none states these pro-etale operation-comparison squares.
- msearch loogle: `CategoryTheory.NatTrans.naturality`. Nine abstract naturality and
  pullback/pushout hits; no exact statement.
- msearch grep: `identity.*[Cc]ompact|compactification.*comparison` in CategoryTheory:
  no hits.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for the item id and identity
  compactification/limit names: no exact declaration; the coefficient-transport module
  mentions an identity compactification but proves a different compositor statement.
- rg for the new namespace in Mathlib, `dag/lean_names_upstream.json`,
  `lean/WeilConjectures` and `lean/Sheaf`: no collision.

Edge cases checked: M=0; Y empty; Y0=Spec k0; first positive exponent n+1=1;
all proper singular or disconnected Y0; arbitrary finite ramified E; repeated/common
coefficient fields and the identity coefficient embedding. The statements contain
no bound excluding these cases. The small pro-etale site's independent object and
morphism sizes remain those of the published interfaces; the scheme and finite
coefficient universes follow those interfaces, and Ω has independent universe v.
No statement correction, dependency repair, new node or STATEMENT-DISPUTED flag.

Validation: scompile.py compiles the sandbox probe and the named library module
separately against the live published library. Early errors concerned syntactic
parentheses and the structure-map/invertibility instances and were repaired.

## Second reading by Q103

A second in-session reading compared the final theorem and every helper against the
node and its seven-step proof. This is the worker's rereading; the maintainer supplies
the independent delivery review, and no additional agent was started.
The first square has source g_s^*Ra_! M and target L_s G_s F_a R_Y M; the second
has source L_s F_a J G_Y R_Y M and target Ra_*g_Y^*M. Both use exactly the canonical
identity-open cancellation, source counit, and inverse reduction/pullback counit.
The rereading found and removed an unnecessary prime-invertibility theorem binder,
replacing it by the canonical construction from l≠p. It also added the explicit
rational image equalities and common finite-field representative clause, and made
properComparison an Iso rather than only its forward map. The fixed
compactRealization and its inverse occur on the required sides of alpha and beta;
no equality of unrelated model choices or finite evaluations is asserted.
