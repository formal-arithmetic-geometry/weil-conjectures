## Worker report

The delivery states lem-pur-finite-compact-support-evaluation-refinement in
Sheaf.Paper.FiniteCompactSupportEvaluationRefinement. Every theorem has proof `sorry`;
all definitions contain actual data. The node is unchanged outside `lean`.
No statement fault or disputed statement was found. No new DAG nodes or dependency repairs.

### Hypotheses and objects

- The finite commutative ring is `B : Type (u + 1)`, `[CommRing B]`, `[Finite B]`.
  Its discrete topology is fixed internally to bottom; no topological assumption is added.
- Schemes are `Scheme.{u}`. The pro-etale site keeps object universe u+1 and morphism
  universe u, with module values in u+1 and derived localization homs in u+2.
  `ordinaryDerivedCategory` reuses the recorded ordinary localization. Giving that instance
  explicitly prevents an unrelated polymorphic IntegralHom module instance from leaving a
  coefficient universe metavariable. It imposes no equality on site universes.
- Separated finite type is `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]` in
  the exchange/evaluation/coherence assertions. Auxiliary ordinaryC invertibility and its
  ratio construction only need the quasi-compactness already implied by this context.
- `x : X' ⟶ X`, `y : Y' ⟶ Y`, `sf : IsPullback x f' f y` give the Cartesian square;
  this is the pullback property underlying the dependency's ChosenCartesianSquare.
  The actual induced inverse-image comparison uses its commuting-square equality.
- `c`, `c' : Compactification ...` supply the open and proper factorizations.
  `si : IsPullback x c'.i c.i s` and `sp : IsPullback s c'.g c.g y` say they are the
  pulled-back compactifications, allowing any supplied canonical pullback model rather
  than requiring a literal fibre-product term. Their projection equalities are `si.w`
  and `sp.w`. No restriction on y, base qcqs hypothesis, density, or residue characteristic.
- `v : c.Refinement d` is the recorded proper Y-morphism fixing X. The properness is its
  existing instance; `i_hom`, `hom_g` are precisely the two compatibility equations.
  `ordinaryC` derives quasi-compactness of its opens from f; the primed formula supplies
  base-change stability explicitly, never as a new hypothesis on y.
- `M : Derived B X`, `n : ℕ` cover arbitrary unbounded derived strict towers and every
  index (n represents positive tower level n+1). Neither evaluation equation has a witness
  or lower-bound premise.

### Every conclusion

- `compositionF B c` is the recorded tower F. `ordinaryF B c = j B c.i ⋙ r B c.g` is
  the ordinary compactification formula. `ordinaryE` takes the proper adjunction mate
  before `openBetaSingle`, in exactly the stated order. `ordinaryC` is the ordinary
  `singleDerivedGamma` of the identity-left clopen-section projector, followed by proper
  image and its identity/composition comparisons. No map is chosen arbitrarily or defined
  by evaluating a tower map.
- `evaluationF` is precisely evalR followed by evalJ, and `evaluationF_isIso` asserts its
  invertibility. `finiteCompactSupportEvaluationRefinement` is the equality identifying
  evaluated tower E with ordinary E, with the explicit source and target evalG/evaluationF
  comparisons on both sides. `refinement_evaluation` does the same for the recorded
  `refinementComparison` and ordinaryC. These are equalities of actual arrows.
- `derived_adjunction_evaluation` includes both derived units and counits under those
  very same comparisons. `pullComp`, `pushComp`, `pullId`, `pushId`, and `square` use
  exact descent and conjugate adjunctions, fixing the normalized ordinary compositors.
- `Origin B X N` retains a bounded-below fixed-module F, the dependency's
  `Scheme.FixedEtaleOriginWitness X B F`, and an isomorphism through the existing canonical
  finite coefficient presentation to N. The ring remains B with identity scalar map;
  this is not the larger ScalarEtaleOrigin domain allowing unrelated finite rings.
  `pullOrigin` states preservation of this exact domain under arbitrary pullback.
- `ordinaryGamma_etale` identifies the ordinary proper/open mate with the exact
  `Etale.ClopenMateNormalization.normalizedComparison` selected by
  properOpenInterchangeCoherence, using existing hJ and hR. Its identity-left specialization
  gives the normalized refinement in the node; applying the outer proper image gives C.
- `ordinaryC_isIso` gives the stated isomorphism at every witnessed N.
  `ordinaryC_identity_composition` gives C_id=1 and C_(v u)=C_u C_v as component equalities
  on the witnessed domain. `ordinaryC_exchange` gives C'_u e_2=e_1 G_a C_u, with all
  primed compactification and refinement compatibility equations explicit.
- `ordinaryI` is literally asIso(C_u1) followed by the inverse of asIso(C_u2), so no
  independent comparison is supplied. `ordinaryI_independence_cocycle` quantifies over
  every common refinement and its arrows and gives both independence and I12 I23=I13
  (Lean uses forward composition). `ordinaryI_exchange` gives the corresponding exchange
  intertwining, retaining any pulled-back Origin witness.
- `finitePresentation`, `presentationPull`, `presentationPush`, `presentationOpen`, and
  `presentationF` are canonical coefficient-presentation comparisons; push is the mate of
  pull, and open is the normalized published open comparison. `presentation_isIso` keeps
  these comparisons invertible. `ordinaryE_specified` explicitly identifies ordinaryE with
  the upstream specified `rightDerivedLowerShriekOfCompactificationBaseChange`, the finite
  ordered proper/open exchange underlying def-exchange-projection and fix-lem-exchanges.
  It therefore also identifies their restrictions on the finite witnessed domain.
- `transport_pasting` transports any equation h1≫h2=h12 through the actual ordinaryI ratios,
  allowing the three corners to arise from different morphisms and different witnessed
  inputs. Together with ordinaryI_exchange, independence, cocycle and ordinaryE_specified,
  this is the stated transport of compactification-relative pasting equations to the
  specified finite exchange maps. It assumes the relative pasting equation, exactly as the
  node's consequent does; it does not assume the conclusion of fix-lem-exchanges.
- `constantTower` is exact descent of actual constant diagrams with identity transitions;
  `constantEvaluation` canonically identifies each evaluation with N. Thus the evaluation
  and witnessed coherence assertions apply to the constant tower on any such finite
  complex. All witnessed assertions are pointwise in N: for general M use its own Origin
  at each n. No common lower bound and no faithfulness of derived evaluation is asserted.

### Dependencies used

The recorded interfaces were read, including their signatures and docstrings:

- ChosenCartesianSquare: AlgebraicGeometry.ChosenCartesianSquare; its Cartesian content
  is used as IsPullback and its inverse-image comparison is the canonical square comparison.
- WeilConjectures.Compactification.RefinementCategory: Compactification.Refinement,
  .category, .Refinement.id, .comp, .isProper, and its projection equations.
- WeilConjectures.Compactification.BaseChange: Compactification.ofIsPullback and its upper
  and lower Cartesian squares. All base-changed models in the statement satisfy these.
- ProEtaleConstantRingOperations (and its public ProEtaleOperations interface):
  Scheme.proEtaleRingModules and .proEtaleRingModules_hasDerivedCategory; the exact module
  inverse image, total direct image and canonical adjunction used by StrictTower operations.
- ExchangeProjectionSuppliedDomains: compactificationExchangeFromData (proper mate then
  open comparison), with the specified finite fixed-module realization used in
  ordinaryE_specified. The published fixed-module derived exchange is reused directly.
- RefinementExchangeCoherence: refinementComparison, refinementCommonComparison,
  refinementExchangeCoherence and refinementFiniteOrigin_pullback.
- ProperOpenInterchangeCoherence: Etale.properOpenInterchangeCoherence; its canonical
  selected comparison is exported by EtaleClopenMateNormalization.normalizedComparison.
- FixedEtaleOriginWitness: Scheme.FixedEtaleOriginWitness, directly retained in Origin.
- ExchangeFunctoriality: the finite domain and exchangeFiniteCompactIdentification;
  the new normalization compares to the very same upstream finite exchange, without
  assuming exchangeFunctoriality as a coherence premise.
- StrictConstantTowerOperations: Modules, Towers, Derived, G, R, adj, ev, moduleGComp,
  moduleRId, evalG, evalR, evalR_isIso. StrictTowerOpenExtension: J, moduleJ, evalJ.
- StrictTowerProperOpenCalculus and its public maps: compositionF, compositionE through
  RefinementExchangeCoherence, normalized gamma and the intrinsic clopen projector.
- TowerMateEvaluationScalars: g, r, j, dAdj, singleDerivedGamma and the derived
  evaluation/transpose/unit/counit/gamma normalization theorems.
- TowerOpenBetaNormalization: openBetaSingle, openBetaFinitePull, openBetaFiniteOpen,
  openBetaEvaluation and openBetaFiniteCompatibility.
- Proof imports: Compactification.CategoryBaseChange (compactifiable cofilteredness),
  FiniteClopenMateSiteTransport, DerivedCategory.CompositionAdjunctionNormalization,
  ProEtale.BaseChange.SmoothBaseChange (comparison_derivedBaseChangeMap), and
  CanonicalFiniteLevelCompactSupportBaseChange (isIso_csAuxiliaryExchange).
  lem-weil-tower-category-levelwise-abelian has no recorded Lean module; the actual
  levelwise abelian diagram structure is already imported by StrictConstantTowerOperations.

### Edge cases and searches

Checked empty source and empty opens, zero complexes and the zero finite ring; no
Nontrivial hypothesis, density, chosen nonempty support or excluded zero index occurs.
Identity refinements/base changes are included. Arbitrary bases, unbounded towers and
varying lower bounds are retained. Finite rings are nonempty as rings, without an added
inhabitedness hypothesis. Pullbacks retain their full site universes.

Searches through msearch.py for this item:

- LeanFinder: "Evaluation of derived strict towers preserves compact support base change
  mates and compactification refinement comparisons" returned eight unrelated condensed,
  profinite and affine-limit declarations; no match.
- Loogle: "CategoryTheory.Adjunction, CategoryTheory.NatTrans" returned zero hits.
- grep: "compactification.*evaluation|evaluation.*refinement" returned zero Mathlib hits.
- LeanSearch: "Evaluation of derived towers commutes with compactification refinements
  and compact support base change" returned unrelated compact support, polynomial tower,
  adic completion and base-change stability declarations; no match.
- rg in lean/WeilConjectures and lean/Sheaf for the item id, finite evaluation/refinement,
  finiteCompactSupport, and the expected names found the dependency operations and
  normalization theorems above, but no existing theorem assembling this statement.
  The normalized single-level mate, open comparison, coefficient realization and retained
  witness were reused. The local CompactObject example is withdrawn; its node correctly
  points to the upstream existing definition, and module layout follows current modules.

Validation: all compilation uses the prescribed scompile.py, each file separately against
published live artifacts. The final module compiles with only the expected sorry warnings.
The required deliver2.py dry run and delivery are run after preparing this report.

## Second reading by Q20

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
