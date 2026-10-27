## Worker report

The module `Sheaf.Paper.PointFrobeniusTransportNormalization` states
`WeilConjectures.PointFrobeniusNormalization.point_frobenius_transport_normalization`.
Its one proof is `sorry`. All auxiliary definitions have real data and only name the
coordinates and canonical composites appearing in this node. There are no new nodes,
no dependency repairs and no changes to the natural-language statement.

Hypotheses and clauses, with names below in namespace
`WeilConjectures.PointFrobeniusNormalization` unless qualified:

- `D : FiniteFieldDatum.{u}` supplies p, a, q, both fields, the cardinality equation,
  characteristic and algebraic closure. `l`, `[Fact l.Prime]`, and `hl : l ≠ D.p`
  are exactly the prime and excluded-characteristic assumptions.
- `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, and
  `[FiniteDimensional ℚ_[l] E]` give the finite coefficient extension. Its recorded
  valuation ring and distinguished uniformizer ideal are reused through
  `Padic.coefficientExtensionIntegers` and `Padic.coefficientExtensionRing`.
- The point is always `Spec (.of D.k)` and g is `(frobeniusPointIso D).hom`, the
  recorded geometric Frobenius, with no arbitrary automorphism substituted.
- Finite positive exponent r is n+1, with `n : ℕ`. Thus n=0 is the required r=1;
  no exponent-zero quotient is introduced. `integralOperationsFiniteModules`
  is the recorded constant-coefficient module category. The completed case is
  `integralTowerModules` over the recorded completed coefficient sheaf.
- Degree zero is the integer-indexed `CochainComplex.singleFunctor _ (0 : ℤ)` in
  `finiteComplex` and `integralComplex`. The finite-free hypothesis is existence
  of an isomorphism to `SheafOfModules.free (ULift (Fin r))`, including r=0.
  Membership in D^b_c is `intrinsicFiniteTorsionConstructible` at finite level
  and `sfIntegralConstructible` at integral level. No Tor hypothesis is added.
- The coefficient structure is exactly `inverseImageFiniteCoefficientMap` or
  `inverseImageCompletedCoefficientMap`, already built into the recorded exact
  inverse-image module functors. No new coefficient action is chosen.
- `finiteKappa` is `inverseImagePullbackComparisonFiniteIntrinsic`.
  `FiniteNormalization` gives a chain isomorphism e whose hom sends every
  scalar multiple of the specified tensor-unit generator to c inverse(b) x,
  and whose inverse is exactly `inverseImageFiniteComparisonComplex`.
  This specifies multiplication and x to x tensor 1, not merely existence of
  an unspecified isomorphism. `finiteLambda` localizes this very e, retaining
  the intrinsic-pullback and both exact-localization comparisons.
- `FiniteNormalization` explicitly asserts `finiteKappa ≫ finiteLambda.hom = 𝟙 _`.
  An isomorphism and its specified inverse include both chain inverse identities.
- `calculus` is the actual whole-system calculus of `FrobeniusExchange.models`.
  `IntegralNormalization` supplies epsilon with hom equal to its actual
  adjunction unit, and theta with kappa followed by theta equal to G(epsilon).
  `integralLambda` is theta followed by inverse G(epsilon), exactly the node's
  prescribed normalization. The whole derived morphism equation and cancellation
  are asserted, rather than inferred from equality only at projections. These
  equations uniquely determine the maps on this complete domain: kappa is
  invertible because lambda is an isomorphism with kappa-lambda composite identity.
- `IntegralQuotientNormalization` is required in the integral assertion. For
  every good representative of M it gives an isomorphism of the entire strict
  quotient towers. Its components have the scalar multiplication formula and
  inverse x to x tensor 1 at every n. Naturality of a tower isomorphism includes
  all transition compatibilities. Eta is fixed on both the ordinary and shifted
  Roos cone coordinates by `trfQuotientProductComparison`. Its final equation is
  the entire chain-map cancellation of `inverseImageRoosComparisonComplex` with
  the strict multiplication map, against the actual strict quotient augmentation.
  Thus the inverse-limit clause is an equation of whole maps with both cone
  coordinates retained, in addition to the ambient derived equation above.
- `finiteDirectId` is the unique right-adjoint identification induced from
  the canonical derived identity pullback and its adjunction.
  `systemDirectId` is its whole-system counterpart; `integralDirectId` and its
  inverse use that identification and the actual completion unit. The existing
  `GeneratorReduction.inverseOrZero` extends the latter word to ambient objects;
  all asserted formulas are on the complete constructible domain where it is
  the inverse of the unit. The finite and integral predicates explicitly assert
  the exchange identity after these canonical identity-operation maps.
- `finiteOrdinary` and `integralOrdinary` expand the prescribed ordinary
  cohomology recipe for the actual structural map id_s: insert its canonical
  identity comparison, apply the recorded point transport, apply the recorded
  Frobenius square exchange, and remove the identity comparison.
- In each transport clause v is an isomorphism of module SHEAVES from GM to M,
  hence B_s-linear. `finiteSheafIso` and `integralSheafIso` send v to its derived
  image using `HomologicalComplex.singleMapHomologicalComplex` and the exact
  inverse-image localization comparison. The equation is tau followed by
  Gamma(lambda then v), equal to sigma followed by Gamma(v). Sigma is the
  recorded `frobeniusPointFiniteSigmaDerived` or integral counterpart. No
  invertibility of ordinary transport or arbitrary choice of comparison is assumed.
- `TensorDualNormalization` first states that c after restriction fixes every
  actual constant coefficient section. `pointRestrictionScalarAt` includes the
  actual constant-to-completion limit lift, so the integral statement is about
  every element of O_E, not just its residue class.
- Its tensor equation is restriction of the canonical sheafified pure tensor
  equal to the pure tensor of the two restrictions, for finite free factors.
  Its dual equation uses `SheafOfModules.homObj` with codomain equal to
  `SheafOfModules.unit` of the coefficient ring and evaluates at the identity
  slice object. These are the sigma diagrams in the canonical sectionwise
  inverse-image coordinates: the distinguished coprojection is the identity
  in those coordinates. `purTensorSection` and the recorded internal Hom retain
  exactly the canonical comparisons of `inverseImage_tensor_hom_iso`.
- `rationalExtension` is the exact derived extension of actual section modules
  along `pointIntegralToField`. `pointFibreRationalAmbient` is precisely integral
  sections followed by this functor. The rational transport equality is displayed
  in `IntegralNormalization`. `closedExtension` is the exact extension from this
  same finite E stage along each Q_l-algebra embedding into an algebraic closure.
  Its displayed equation is the common-stage image of the rational equation.
  The algebraic closure has independent universe v; `closedExtension` reuses
  `frobeniusCohomologyCoefficientExtension` with the canonical ULift ring equivalence.
  The ULift models are the ambient coordinates of `FiniteCoefficientPoint`;
  its canonical coefficient and size descent identifies them with the recorded
  small fibre/common-stage categories. All earlier identities also pass to these
  scalar images by functoriality. No independent rational or closed-field action
  is introduced.

The site keeps object universe u+1 and morphism universe u. The coefficient and
section lifts use u+1, and derived-localization sizes are pinned where necessary;
there is no equality imposed between site object and morphism universes.

Dependency declarations read and reused (module; primary declaration):

- `def-weil-finite-field-fiber`: `Sheaf.Paper.FiniteFieldFiber`; `WeilConjectures.FiniteFieldDatum`.
- `def-weil-completed-integral-coefficients`: `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`; `WeilConjectures.integralConstantToCompletionOfUniverses`.
- `def-weil-inverse-image-pullback-comparison`: `Sheaf.Paper.InverseImagePullbackComparisonDerived`; `AlgebraicGeometry.ProEtale.inverseImagePullbackComparisonDerived`.
- `lem-weil-isomorphism-derived-pullback`: `Sheaf.Paper.IsomorphismDerivedPullback`; `WeilConjectures.isomorphismIntegralDerivedPullback_termwise`.
- `def-weil-frobenius-point-transport`: `Sheaf.SixFunctors.FrobeniusPointTransport`; `WeilConjectures.frobeniusPointTransportQbar`.
- `def-weil-frobenius-square-exchange`: `Sheaf.Paper.FrobeniusGeometricExchange`; `WeilConjectures.FrobeniusExchange.frobeniusCommonStage`.
- `def-weil-frobenius-cohomology-transport`: `Sheaf.SixFunctors.FrobeniusCohomologyTransport`; `WeilConjectures.frobeniusCohomologyTransport`.
- `def-weil-finite-coefficient-point`: `Sheaf.Paper.FiniteCoefficientPoint`; `WeilConjectures.pointQbarFibre`.
- `def-weil-frobenius-detailed`: `Sheaf.AlgebraicGeometry.FrobeniusDetailed`; `WeilConjectures.FiniteFieldDatum.geometricFrobenius`.
- `lem-weil-isomorphism-derived-pullback-comparison-normalization`: `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization`; `WeilConjectures.isomorphismDerivedPullbackComparisonNormalization`.
- `lem-pur-normalized-actual-reconstruction-maps`: `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus`; `WeilConjectures.purNormalizedReconstruction`.
- `def-weil-derived-complete-integral-detailed`: `Sheaf.Paper.SfIntegralConstructible`; `WeilConjectures.sfIntegralConstructible`.
- `def-pur-sheaf-hom`: `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`; `SheafOfModules.homObj`.
- `def-pur-sheaf-tensor-product`: `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`; `SheafOfModules.cochainModulesMonoidal`.
- `lem-pur-isomorphism-inverse-image-tensor-hom`: `Sheaf.Paper.PurInverseImageTensorHom`; `AlgebraicGeometry.Scheme.inverseImage_tensor_hom_iso`.

The source signatures and docstrings were read, including the entire normalized
comparison theorem and the actual reconstruction unit theorem. Their public
finite and whole-system APIs, rather than copies of pullback or completion, are
used above. The proof imports retain scalar-extension ring-isomorphism,
operation-reduction, derived monoidal comparison, semilinear sections,
point-section exactness, and pullback-composition dependencies. The additional
strict quotient/Roos APIs are the already recorded representation of the same
comparison, publicly available from its normalization dependency.

Edge cases checked by reading the equations: zero sheaf and rank zero; rank one;
first quotient n=0 (exponent one); arbitrary ramification of E; identity restriction
(the generator, scalar, mate and cone equations specialize to identities); every
integer degree in the quotient representative; all positive quotients and both
cone coordinates, rather than just cohomology groups. The finite-field point is
nonempty by its datum; no extra nonzero-section or positive-rank assumption occurs.
The proof stays postponed, as required for stage 2.

Searches for an existing exact statement:

- msearch LeanFinder, `Frobenius transport normalized inverse image derived pullback
  finite free coefficient sheaves`: eight ordinary pullback/free-object results,
  including `SheafOfModules.pullbackObjFreeIso`; no combined normalization theorem.
- msearch LeanFinder, `Point Frobenius restriction transport on finite free completed
  coefficient sheaves cancels the normalized inverse image derived pullback
  multiplication map`: eight unrelated arithmetic Frobenius/Witt vector hits.
- msearch Loogle, `SheafOfModules.pullbackObjFreeIso,
  SheafOfModules.freeFunctorCompPullbackIso`: no hits.
- msearch grep, `frobenius.*transport|transport.*frobenius|pullbackObjFreeIso`:
  five Mathlib PullbackFree hits, none states this node. The earlier narrower
  Frobenius transport grep had no Mathlib hits.
- rg in `lean/WeilConjectures` and `lean/Sheaf`, and exact item-id search upstream:
  no exact combined statement. `PointAutomorphismDerivedTransportInverse` has a
  related general inverse theorem, but lacks this node's identity ordinary
  exchange, prescribed ordinary-transport equation and tensor/dual clauses.
  Its already existing notions are reused from their owning modules.

No statement dispute or source correction was found. The node's selected
normalization is essential: replacing lambda by a scalar multiple would violate
its prescribed coordinate equation and is not permitted by this signature.

Validation: scompile.py compiled the complete module in sandbox and library modes
without errors or warnings. The resumed draft required the canonical
`integralSectionsDerived` instance and moving `fieldSectionsDerived` before its
first use; both use the existing Grothendieck derived-category construction.
The unused partial rewrite was removed from the delivery. The final compile
also checks the independent-universe algebraic-closure transport. The prescribed
`deliver2.py --no-push` dry run passed the server preflight and compile checks
(0b969ff720b); it staged exactly the module, item node and worker report.

## Second reading by Q65

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
