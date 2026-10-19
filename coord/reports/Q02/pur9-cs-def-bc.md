## Worker report

The item is defined in `Sheaf.SecSmoothPurity.ExceptionalBaseChange`, declaration
`AlgebraicGeometry.ProEtale.exceptionalBaseChangeOnOrigin`. The node statement is unchanged.
The construction uses the unconditional finite exceptional functor at each **specified**
compactification. It is the relative transpose of the inverse specified support exchange
followed by the pulled-back counit. No ambient pro-etale exceptional adjunction is assumed.
There are no new nodes and no statement corrections.

Hypothesis and clause correspondence:

- The fixed algebraic closure of a finite field is `D : WeilConjectures.FiniteFieldDatum`.
  The coefficient prime is `l`, `[Fact l.Prime]`, and `_hl : l ≠ D.p`. The finite coefficient
  extension is `E`, `[Field E]`, `[Algebra (Padic l) E]`, and `[FiniteDimensional (Padic l) E]`.
  The integer and positivity condition are `n : ℕ` and `hn : 1 ≤ n`. The actual coefficient
  ring is `Padic.coefficientExtensionRing l E n`, the recorded O_E/(varpi_E^n) construction,
  with finiteness supplied by `Padic.finite_coefficientExtensionRing`. The `ULift` only puts
  the same finite ring in the module-value universe of the actual small sites; it changes
  neither scalars nor modules. Its discrete finite coefficient interpretation is the
  existing fixed-module/constant-ring coefficient realization.
- All four schemes have `.Over (Spec (.of D.k))`. Each structure morphism has
  `LocallyOfFiniteType` and `QuasiCompact`, exactly finite type over k. Every displayed
  arrow has `.IsOver (Spec (.of D.k))`. On f, `IsSeparated`, `LocallyOfFiniteType`, and
  `QuasiCompact` render separated finite type. There is no smoothness or properness
  restriction on f and no restriction on g beyond being a k-morphism.
- `sq : ChosenCartesianSquare g' f' f g` retains the canonical identification of X' with
  the fibre product and its two projection equations. This is the standard equivalent
  Cartesian-square presentation of X' = X ×_Y Y'. The auxiliary compactification is
  literally `c.ofIsPullback (IsPullback.of_iso_pullback ...)`, using the recorded
  `Compactification.ofIsPullback` construction. `c` and `cf'` are the two fixed choices.
  Quasi-compactness of f' is derived from the square in the bodies, not added as a premise.
- `K : DerivedCategory.Plus ...` together with `_hK : finiteTorConstructibleProEtaleModule
  l E n hn Y K.obj` presents D^b_ctf(Y_proet,A). The latter is precisely the existing
  intrinsic bounded constructibility plus finite Tor predicate, transported by the
  canonical coefficient realization. Keeping an explicit D+ presentation imposes no
  restriction: every bounded constructible object is bounded below; D+ is a full
  subcategory and all Hom sets remain the ambient ones. This uses the existing notion,
  rather than substituting an arbitrary etale-origin predicate for constructibility.
- The endpoints use the existing `sfFiniteExceptionalAt` at c and cf', with the existing
  ordinary-etale compact-support left-adjoint theorem supplying their proof-valued
  instances. This is literally Rnu_* followed by the right adjoint of the compact-support
  functor for c (respectively cf'), followed by exact nu^*. It does not use an arbitrary
  pro-etale adjoint. In particular, `HasCompactification.compactification` is not silently
  treated as equal to the supplied c: that Prop-valued class only asserts existence.
- M and its witness are retained by `csExceptionalOrigin`: its etale antecedent is the
  actual etale right adjoint for c applied to Rnu_*K, and alpha is the identity comparison
  with the defining composite. This antecedent is bounded below by
  `specifiedExceptionalEtale_boundedBelow`; the constructible-preservation and origin
  clauses cited in the node ensure it is bounded constructible on this input. The
  definition needs its bounded-below witness, and retains exactly the recorded
  `Scheme.FixedEtaleOriginWitness`, with both `complex` and `iso` as data.
- `csPullbackOrigin` retains the displayed pulled-back witness. Its antecedent is
  `Etale.upperStar ... g' |>.mapDerivedCategoryPlus`, and its isomorphism is the inverse
  of `sfDerivedComparisonPullbackIso` followed by pullback of W.iso. This is precisely
  nu_X'^* u_et^-1 G -> Lu^* nu_X^* G -> Lu^*M. The pullback of K is likewise taken in D+.
  Exact inverse image is `sfFixedDerivedPullback`; the canonical
  `leftDerivedUpperStarIsoMapDerivedCategory` identifies it with Lg^*.
- `canonicalFiniteCoefficientCompactSupportExchange` is the unchanged proper-mate / exact
  open-extension composite into c'. The named obligation `isIso_csAuxiliaryExchange` in
  the repaired finite-level CBC dependency gives its invertibility at every retained
  bounded-below origin. Its proof docstring records the specific j_! antecedent,
  termwise extension-zero comparison, qcqs proper factors, the specified proper mate
  equality, and uniqueness of the open factor by the extension/restriction adjunction.
  Thus it is the source's actual exchange, not a freely supplied isomorphism.
- `csOriginCompactificationIso` is theta_c' at the retained pulled-back witness. It
  conjugates `fixedCompactSupportOriginIso` by the actual W'.iso. That existing comparison
  uses `fixedCompactSupportComparisonIso` and the canonical etale compactification
  comparison. It is the normalized canonical comparison of the recorded class-adjunction
  interface. It has only the etale-origin domain; no ambient comparison is postulated.
- `csChosenSupportExchangeIso` first uses the inverse exact/left-derived comparison at g,
  then the auxiliary exchange, then the direct exact/left-derived comparison at g', and
  finally theta at the pulled-back witness. In exact-inverse-image coordinates this is
  exactly theta_c',Lu^*M composed with Ex_!,square,A,M. Its inverse therefore has the
  required direction Rf'_!Lu^*M -> Lv^*Rf_!M.
- `specifiedExceptionalHomEquiv` constructs the normalized class Hom chain at the literal
  compactification, using alpha, the fixed support comparison, comparison adjunction,
  the ordinary etale adjunction for that compactification, comparison full faithfulness,
  and alpha again. Its result is an actual Equiv, not chosen from Nonempty. Naturality
  is inherited from these canonical factors; the original class-adjunction theorem and
  its coherent-comparison record remain publicly reexported.
- `eps := (specifiedExceptionalHomEquiv ... c M W K).symm (𝟙 _)` is exactly the prescribed
  counit, the preimage of 1_M. The body then applies the f' Hom bijection to
  `(csChosenSupportExchangeIso ...).inv ≫ (sfFixedDerivedPullback A g).map eps`.
  The result has exactly source Lu^*Rf^!K and target Rf'^!Lv^*K. All arrows are ambient
  derived morphisms. Compactness of Y and Y' needed by the boundedness API is derived
  from their given finite-type structure maps via
  `QuasiCompact.compactSpace_of_compactSpace`; no extra hypothesis is imposed.

Dependency declarations read and used (including the recorded general interfaces):

| Node | Module / declaration |
| --- | --- |
| sk-def-sf-operations | Its upstream audit names Etale.upperStar, rightDerivedLowerShriek, rightDerivedUpperShriek, derivedTensor, derivedHom and openImmersionLowerShriek in their Etale operation modules. Only the finite pullback, compact support and exceptional clauses occur here. |
| def-sf-etale-origin-subcategory | Sheaf.Paper.EtaleOriginDerivedCategory / ProEtale.EtaleOriginDerivedCategory, etaleOriginForgetfulPlus, restrictToEtaleOrigin. Here the same retained pair is consumed directly in the fixed-coordinate witness, with ambient Hom sets. |
| def-weil-pbc-etale-origin-witness | Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness / Scheme.FixedEtaleOriginWitness, its complex and iso fields. |
| pur713-def-base-changed-compactification | WeilConjectures.Compactification.BaseChange / Compactification.ofIsPullback and the upper/lower pullback squares. |
| def-compact-support-direct-image-detailed | Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport / Scheme.sfIntrinsicCompactSupport; its fixed-coordinate realization sfFixedCompactSupport is exactly D(j_!) followed by Rp_*. |
| def-weil-exceptional-inverse-image | The record's System interface retains all coefficient stages and publicly imports FixedFiniteExceptionalAt; its finite-stage ProEtale.sfFiniteExceptionalAt is used here. The finite adjoint is attached to the specified c, rather than an opaque existential compactification. |
| thm-sf-ambient-adjoint-class | Sheaf.AlgebraicGeometry.EtaleOriginAdjointClass / ComparisonClassAdjunction, exists_comparisonClassAdjunction; publicly reexported by SpecifiedExceptionalClassHom, which also provides specifiedExceptionalHomEquiv and its finite-amplitude obligation. Its canonical fixedCompactSupportComparisonIso and fixedCompactSupportOriginIso are used. |
| lem-kun-dimension-finite-type | WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType / exists_topologicalKrullDim_le; used by the boundedness proof plan. |
| lem-sf-proetale-constructible-origin | Sheaf.Paper.ProEtaleConstructibleOrigin / constructible_proEtale_origin, ConstructibleOriginComparison; ensures the constructible scope of the retained antecedent. |
| def-weil-derived-pullback-tensor-hom | Finite stage uses sfFixedDerivedPullback and the canonical leftDerivedUpperStarIsoMapDerivedCategory; the recorded DerivedPullbackTensorHom common-stage internal Hom is not needed at this finite coefficient level. |
| prop-weil-pbc-inverse-image-modules-exact | WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact / etaleInverseImageModulesExact; fixed-module exact inverse images are the existing upperStar functors. |
| lem-weil-pbc-comparison-pullback | Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence / supportSiteComparison_pullback_coherent; the derived square is sfDerivedComparisonPullbackIso. |
| pur713-def-shriek-exchange | Repaired CanonicalShriekExchange / canonicalFiniteCoefficientCompactSupportExchange. |
| thm-cbc-finite-level-proetale | GlobalFiniteLevelCompactSupportBaseChange / globalFiniteLevelCompactSupportBaseChange, cbcGlobalExchange and endpoint comparisons; all reexported by CanonicalFiniteLevelCompactSupportBaseChange, adding their raw fixed-coordinate invertibility clause. |
| pur713-def-star-exchange | Sheaf.SecSmoothPurity.FiniteCoefficientDirectImageExchange / Scheme.proEtaleFiniteCoefficientDirectImageExchange; the fixed-coordinate derivedBaseChangeMap is the same normalized mate. |
| def-weil-pbc-ambient-ringed-exchange | Sheaf.Paper.PbcActualRingedExchange / Scheme.pbcActualCompletedAmbientExchange; its generic ringed mate specializes to the same constant-ring fixed-coordinate mate. The completed coefficient operation is not used. |
| lem-weil-pbc-transport-identifies-exchange | WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange / comparison_derivedBaseChangeMap, baseChangeSourceComparisonIso and baseChangeTargetComparisonIso. |
| lem-cbc-proetale-extension-zero-comparison | Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison / openImmersionLowerShriekComparison_coherence and openImmersionLowerShriekComparisonUpperStarIso. |
| lem-cbc-proetale-extension-zero | Sheaf.AlgebraicGeometry.ProEtaleExtensionZero / proEtale_extension_by_zero, openExtensionCochain; actual openImmersionLowerShriekUpperStarAdjunction supplies the open-map uniqueness argument. |
| prop-compactification-coherence-detailed | Sheaf.Paper.CompactificationCoherence / compactification_coherence; the same normalized etale-origin comparison is fixedCompactSupportOriginIso from the class-adjunction dependency. |
| pur713-def-shriek-exchange-chosen | The recorded full ambient theta interface is used as its composition formula on the permitted class, implemented explicitly by csChosenSupportExchangeIso using the actual canonical component; no full ambient theta input is added. |

The smaller finite-stage imports are deliberate. Importing the entire current
ConstructibleExceptionalAdjunctionCoefficients, DerivedPullbackTensorHom or
CompactificationCoherence closure reaches ComparisonGlobalCohomology, whose legacy
ProEtale.Derived.LowerShriek import conflicts with the finite-coefficient one. The compiler
reported the exact duplicate declaration rightDerivedLowerShriekOfCompactification.
Following the launcher's duplicate-import repair instruction, the construction imports
only the smaller modules containing the declarations it actually uses. The chosen-exchange
module likewise inherits the legacy import; its class-restricted composition formula is
written out with the repaired auxiliary exchange and actual canonical theta component.
No missing construction is replaced by a hypothesis.

Edge cases checked before and during writing: n=1 (the residue coefficient level); K=0;
empty X, empty Y' and empty Y (then X is empty); g=id with arbitrary independently fixed
compactifications; a nontrivial base change and a nonidentity theta; arbitrary nonsmooth g;
nonseparated finite-type schemes; distinct small-site object and morphism universes.
No dimension of the empty scheme, maximum over an empty cover, monomorphism assumption on g,
or equality of site universes is needed. In the identity case the canonical comparison
between c and cf' is retained rather than silently set to the identity.

Searches made for an existing exact definition:

- msearch leanfinder: "Exceptional inverse image base change defined as adjoint transpose of
  inverse compact support exchange and pulled back counit"; 8 results, ordinary sheaf and
  module adjunctions (TopCat.Sheaf.pullbackPushforwardAdjunction,
  PresheafOfModules.pullbackComp, SheafOfModules.pullbackComp, Scheme.Modules adjunctions,
  ExponentiableMorphism.ev and conjugateEquiv). No exact exceptional-origin map.
- msearch loogle: "CategoryTheory.Adjunction.homEquiv"; 12 results, abstract Hom adjunction
  bijections and construction lemmas. No specified exceptional exchange construction.
- msearch grep: "upperShriek|exceptional.*[Bb]ase[Cc]hange|compactSupport.*[Ee]xchange";
  zero Mathlib hits. Also read Mathlib CategoryTheory.Iso homFromEquiv / homToEquiv and
  finite/of_equiv to construct, rather than axiomatize, the required Hom chain.
- msearch leansearch: "Exceptional inverse image base change is the adjoint transpose of
  inverse compact support exchange followed by pulled back counit"; 8 results, ordinary
  presheaf pullback, inverse-counit, and exponentiable-morphism declarations. No exact match.
- rg on WeilConjectures and lean/Sheaf for the item id and exceptional/base-change names:
  no declaration for pur9-cs-def-bc. Found smoothExceptionalProEtaleBaseChangeMap,
  sfFiniteExceptionalOpenComparison and sfAmbientExceptionalOpenComparison. The first
  definition permits arbitrary f and g but fixes the target compactification to the base
  change of c and uses the opaque HasCompactification choice in its exceptional functors;
  it does not give this specified-two-compactification class transpose. The other two
  require open g or an ambient exceptional adjoint datum. The similarly named ordinary
  etale-site smoothExceptionalBaseChangeMap is not a pro-etale construction.
- Read the current server UpperShriek, Comparison, LowerShriekIndependence, Etale
  UpperShriek and LowerShriekLeftAdjoint sources via scompile.py --source. They supply the
  canonical finite-stage building blocks, but the ambient named-upper-shriek Hom API uses
  an opaque compactification choice and cannot be identified definitionally with c.

All definitions contain real data. The only postponed declarations are
`specifiedExceptionalEtale_boundedBelow` (owned by thm-sf-ambient-adjoint-class) and
`isIso_csAuxiliaryExchange` (owned by thm-cbc-finite-level-proetale). Their source and complete
natural-language proof plans are in their docstrings. No STATEMENT-DISPUTED issue remains.
All four delivered modules compiled cleanly in the prescribed per-file checks, including
the final ownership split, through scompile.py and deliver2.py --no-push. The two expected
declaration-uses-sorry warnings are the stage-2 postponed theorems named above.

## Dependency modules

`pur713-def-shriek-exchange`: `Sheaf.SecSmoothPurity.CanonicalShriekExchange` is the identical
raw exchange construction with current finite-coefficient imports and a distinct name.
The old module cannot be combined with the recorded exceptional/comparison declarations:
it imports a legacy module declaring the same lower-shriek constant. Only lean is repaired.

`thm-sf-ambient-adjoint-class`: `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`
publicly reexports the full old theorem and record, including its dimension bounds and
coherent comparisons. It adds the evaluable normalized Hom chain for the actual supplied
compactification c, plus the ordinary-etale finite-amplitude obligation for that c.
This repairs the existential/opaque-compactification interface without choosing data from
an unconstrained existence theorem. Its data are entirely the canonical Hom bijections.

`thm-cbc-finite-level-proetale`: `Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange`
publicly reexports the global theorem with its witness and compactification independence.
Its additional named clause states invertibility of that same exchange in the raw
fixed-module coordinates of the auxiliary exchange, at the supplied retained origin.
The earlier ringed coefficient endpoints did not directly accept this fixed-scalar map.
The proof plan explicitly identifies proper mates and open factors, preserving the
specified exchange rather than merely introducing an unspecified isomorphism.

## Second reading by Q02

This is an explicit delivery self-audit, not a claim of an independent second agent:
the dispatcher prohibits starting agents, and the maintainer independently reads delivery.
Reopened the node and every delivered declaration. Checked all binders against the list
above and checked the four-factor chosen-exchange direction and final Hom transpose.
Two actual mismatches were caught and fixed: the legacy lower-shriek import collision,
and the initial use of HasCompactification as though its internal choice were c.
The latter now uses sfFiniteExceptionalAt and the explicit-c Hom chain throughout.
Removed the extra f'-quasi-compact binder and derived it from the Cartesian square.
Derived compactness of both targets from their given structure morphisms. The source
and target of eps, inverse Ex-circ, its pulled-back composite and the primed transpose
now match definitionally in the compiled fixed-coefficient categories. The two retained
witnesses are actual pairs and are passed to the comparisons, not erased to Nonempty.
The class-only theta restriction has no ambient comparison premise. The item module has
only definitions; each postponed property is in its owning dependency's module and record.
