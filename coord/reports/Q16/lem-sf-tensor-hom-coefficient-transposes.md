## Worker report

Repair of returned immutable head `0d7a5c753f0a`, points H2 and H3. The module is
`Sheaf.Paper.TensorHomCoefficientTransposes`. It states exactly the coefficient
transposition and rational/common-stage passages in the assigned node. Every theorem
has proof `sorry`; definitions have real data, and inverse proofs used by definitions
are named theorems of this same DAG node. The node's mathematical statement is unchanged.

Source reread: `literature/blueprint/latest/blueprint/sec-six-functors/
sk-thm-sf-package/fix-lem-tensor-adjunction.proof.md`, Step 1, coefficient-comparison
paragraph, and the integral, rational and algebraically closed coefficient paragraphs;
the assigned node's eight detailed proof steps supply the explicit localization and
common-stage argument. The source's Hom chain is read backwards, as the node specifies.

Hypothesis and clause rendering:

* `D : FiniteFieldDatum`, `C : D.CoefficientDatum`, the field/algebra/finite-dimensional
  instances for E,E', and n,hn,n',hn' retain the common finite-field coefficient and
  positive-exponent conventions. `X Y : SixFunctorSpace D` are the finite-type schemes;
  the separated/locally-finite-type/quasi-compact instances on f give separated finite
  type. The compactification c fixes the recorded compact-support projection.
* `Admissible` is the dependency's actual ambient admissibility at the selected stage,
  over Spec D.k. `tensorHomCoefficientTransposes._hadm` retains it. `ringStage` selects
  finite or integral input coefficients. There is no site-perfectness condition.
* `Domain` abbreviates existing `PodCtfAdjunctionData`, whose supplied preservation,
  closed restrictions and tensor identifications are precisely the node's full-domain
  hypothesis. `PodHomChain.sourceFunctor`, `targetFunctor` and `homEquiv` are A, B and
  Gamma. The chain uses inverse ordinary adjunction, inverse tensor-Hom, inverse
  exceptional adjunction, precomposition by forward PF, then target tensor-Hom.
  The actual PF and fixed-left Hom in this module are `PodCtfPairing.projection/homX`,
  owned by `def-pod-ctf-pairing-maps`; they agree definitionally with the chain's maps.
* `Permitted` lists the actual three sheaf coefficient maps: finite quotient n'≤n,
  integral reduction, and completed extension along E→ₐ[Padic C.l]E'. The same-field
  clauses identify the maps themselves. `_hX/_hY` identify the restricted functors
  with `pbcDerivedExtend` along that map. Integral tensors are the completed tensors
  of the datum, rather than a new tensor construction.
* `TensorComparison.right` is the counit/evaluation-normalized natural transformation;
  it need not be invertible. `Comparison` keeps the ordinary and exceptional
  unit/counit comparisons, tensor-Hom evaluation equations, support-input normalization
  `tensorY_normalization`, and the square for forward PF. Thus intermediate Hom
  invertibility has not been added. Only the endpoint `_hA/_hB` of the specialized
  theorem are required invertible, exactly as in the node.
* `Comparison.source/target` are alpha_A/alpha_B in the stated order. `Square` and
  `coefficient_square` say `TY.map (Gamma z) ≫ alpha_B = Gamma' (TY.map z ≫ alpha_A)`
  for every actual test morphism z. `tensorHomCoefficientTransposes` specializes this
  to the three permitted changes and their actual coefficient functors.
* H3 repair: `successive_square` now takes the direct-change comparison `direct` in
  literal composite coordinates. The four component normalizations are the ordinary,
  exceptional, X-Hom and Y-Hom tower laws of the specified operation comparisons.
  Its CONCLUSIONS explicitly give `direct.source = U(alpha_A^T);alpha_A^U` and
  `direct.target = U(alpha_B^T);alpha_B^U`, followed by `Square direct`. Previously it
  only asserted a pasted two-step square. The docstring explains how the recorded
  tensor/scalar associators and mate-pasting laws supply these component normalizations.
* `integralHomEquiv` is the same Gamma transported through full inclusion to integral
  Hom groups. `localized_bijection` asserts integral O_E-linearity and the linear raw
  localization, with pure-tensor formula, also in E⊗Hom coordinates. No Karoubi
  completion is used. `localized_representatives` retains both inverse identities and
  both postcomposition formulas for a supplied representing integral inverse pair.
* H3 repair: `integralGammaIso` has forward map literally Gamma(1_A) and inverse
  Gamma^{-1}(1_B). `integral_representative_laws` postpones only their inverse proofs.
  `rationalGammaIso` is its image under the actual raw localization and `rationalGamma`
  is postcomposition with this fixed image. `rationalGamma_formula` identifies it
  with the linear localization of the original chain on every pure tensor. Thus these
  maps are the localized Gamma, not an arbitrary family chosen on arbitrary pairs.
* H3 repair: `commonSource/commonTarget` are the inclusion of the actual rationalized
  endpoints at F; `commonGammaIso` is the image of `rationalGammaIso`. `commonGamma`
  is its action on every common-stage test Hom. `stageGamma` is the recorded scalar
  transition of that SAME rational Gamma representative at any common field G.
  `common_stage_bijection` CONCLUDES its transport compatibility for every G≤H and
  existence/uniqueness of the additive common-stage bijection with `[G,z]` mapped
  to `[G,stageGamma_G(z)]`. Compatibility is no longer an arbitrary-family hypothesis.
  The formula on every representative plus the existing equality criterion gives
  independence of fields and representatives, including non-base-field test objects.
* H3 repair: `common_stage_representatives` now has the actual integral representing
  equation for Gamma as hypothesis. It concludes both inverse identities and the
  forward AND inverse postcomposition equations for `commonGamma` on all common-stage
  arrows. `common_stage_postcomposition` states the same fixed Gamma's representative
  formula and inverse on arbitrary common-stage Homs, with no family parameter g.
* H3 repair: `equations_pass_to_fields` states the naturality equation in N and
  precomposition/composition with an arbitrary test arrow t, simultaneously for the
  actual `rationalGamma` and `commonGamma`. It is no longer congrArg on two arbitrary
  arrows. `field_coefficient_square` states the coefficient square for EVERY fractional
  arrow and EVERY common-stage arrow, comparing the actual integral chains at F and G.
  `rationalSourceComparison/rationalTargetComparison` are the localized alpha_A/alpha_B,
  in the scalar-transition coordinates fixed by the natural realization rY. The common
  square includes the canonical `stageSystem.transIso` endpoint identifications.
  Thus recalculating the actual changed chain over G agrees with the F construction.
  This complements the transport equation for `stageGamma`, rather than assuming it.
* `shift_equations_pass_to_fields` retains any integral signed-shift square of these
  SAME canonical representatives and concludes its rational and common equations.
  It keeps the integer sign k and the actual shift functor on the integral category;
  the normalized localization/inclusion shift comparisons identify their images with
  the shifted rational/common objects. Composition is retained explicitly in all
  these equations. The conditional shift hypothesis is exactly the node's phrase
  "equations satisfied at the integral stages", not a field-compatibility assumption.

Dependency declarations used:

* `def-fix-six-functor-datum`: `Sheaf.Paper.SixFunctorOperationDatum`,
  `WeilConjectures.SixFunctorOperationDatum`, its actual finite/higher/closure operations.
* `def-weil-exceptional-adjoint-admissibility`:
  `Sheaf.Paper.ExceptionalAdjointAdmissibility`, its four stage admissibility predicates.
* `fix-prop-adjunctions`: `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions`,
  the specified adjunction normalizations, inherited by the supplied restricted data.
* `def-exchange-projection`: `Sheaf.Paper.ExchangeProjectionSuppliedDomains`,
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionAdjunctionComparison`
  (and its unit/counit normalization; scalar cocycles are read there too).
* `def-weil-rationalization-karoubi`: `Sheaf.Paper.SfRationalizationKaroubi`,
  `sfRationalConstructibleLocalization`, `sfRationalScalarExtension`, raw tensor Homs.
* `def-weil-algebraically-closed-coefficients`:
  `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`, `Pair`, `StageHom`, `transport`,
  `ofHom`, `stageTransition`, `stageSystem`, `inclusion`, and representative criterion.
* `def-weil-derived-pullback-tensor-hom`: `Sheaf.Paper.DerivedPullbackTensorHom`,
  the actual partial/completed/rational/common tensor and Hom used by stage selectors.
* Landed `def-sf-ctf-coefficient-stage-selectors`:
  `Sheaf.Paper.CtfCoefficientStageSelectors`, `PodCoefficientStage` and its selectors.
* Landed `def-pod-ctf-pairing-maps`: `Sheaf.Paper.PodCtfPairingMaps`,
  `PodCtfPairing.projection`, `homX`, `homY` (definitionally the chain's same maps).
* New existing-definition owner `def-sf-tensor-hom-chain-data`: the existing
  `PodCtfAdjunctionData` structure/constructors from `PodCtfAdjunctions` and
  `PodHomChain.sourceFunctor/targetFunctor/homEquiv` from `PodHomChainCounitFormula`.
  Neither `podCtfAdjunctions_exists` nor `counit_formula` is used in the statements;
  the two theorem nodes have been REMOVED from the added statement dependencies.

The imported proof dependencies remain plain imports, as stage 2 requires. Every new
helper has the assigned node's source/blueprint docstring; every theorem docstring
contains the appropriate proof steps. Definitions chosen from sorry existence proofs
are not used: all representatives have literal maps, and their postponed proofs
only verify inverse identities of those maps.

Edge cases checked: equal positive exponents including 1; identity coefficient maps
and repeated fields; empty schemes and zero objects; non-site-perfect finite-Tor
inputs; torsion integral Homs killed by rationalization; arbitrary fractional arrows;
arbitrary common-stage test objects; representatives at a strictly larger field;
identity shifts and both signs; ramified fields (the actual scalar transition is used,
with no assertion that uniformizers agree). All coefficients and schemes use u, as
in the recorded datum; no extra universe equality is imposed.

Searches made before new ownership:

* msearch LeanFinder, "The specified five-arrow tensor Hom adjunction chain and its
  full finite Tor adjunction presentation": 8 hits (Tor, rigid tensor Hom, generic
  Gabriel-Popescu tensor adjunction), no exact four-stage definition.
* msearch LeanSearch, "Full subcategory restriction of ordinary exceptional and tensor
  Hom adjunctions and the composite five adjunction bijections": 8 hits, notably
  `Adjunction.restrictFullyFaithful`; a primitive used by the published data, not the
  whole definition. Loogle `CategoryTheory.Adjunction.restrictFullyFaithful,
  CategoryTheory.Iso.homCongr`: 0 hits. msearch grep
  `PodCtfAdjunctionData|PodHomChain|PodCoefficientStage`: 0 Mathlib hits.
* rg of upstream WeilConjectures for these names: no hits; rg of Sheaf found the exact
  existing definitions at PodCtfAdjunctions:49–120 and PodHomChainCounitFormula:127–189.
  DAG search found theorem consumers and the existing selector and pairing owners,
  but no definition owner for the restriction/chain data. `blueprint_refs.py search
  'Hom chain'` and `'five-arrow'`: 0 matches. Ancestor is fix-lem-tensor-adjunction.
  The new node's search records reproduce the actual launcher search log results.
* Retained original whole-item searches: LeanFinder 8 module localization/adjunction
  hits; Loogle 2 generic curry/uncurry hits; grep 25 generic Hom naturality hits;
  LeanSearch 8 scalar-localization hits. No existing whole-item theorem was found.

No STATEMENT-DISPUTED claim, statement correction, or dependency-interface repair.

## New nodes

`def-sf-tensor-hom-chain-data` is a definition owner with `existing:true`, bound to the
published plain definitions, not to either theorem conclusion. It defines supplied
restricted adjunction presentations and the literal five-arrow composite, citing the
existing selector and pairing owners. Its source is the current blueprint Step 1;
its three search kinds and project/DAG/blueprint searches are recorded. No new module
or duplicate definition is introduced. The item directly cites all three definition
owners. This is the requested H2 repair.

`def-sf-coefficient-gamma-representatives` owns the concrete canonical comparison,
integral/rational/common representative constructions and the explicit field/shift
equation predicates in `Sheaf.Paper.CoefficientGammaRepresentatives`. Its named
inverse-identity theorem is the proof required for the explicitly given representing
isomorphism, and is included in the node statement. Its source is Step 1 and the
coefficient and field paragraphs (node steps 7–8). LeanSearch found eight generic
adjunction/evaluation/Yoneda primitives; Loogle found eleven generic Iso.homCongr
lemmas; Mathlib grep found no names; project and DAG searches found only unrelated
TensorComparison structures. The exact existing chain, selectors, projection,
localization and common-stage categories are reused. It supplies no theorem about
coefficient transposition or field descent: those conclusions remain in the item.

## Second reading by Q16

Reopened the returned node, retained file, current source and definition-owner nodes.
The old report claimed conclusions the old signatures did not state; the repaired
signatures now explicitly contain the direct endpoint cocycles, canonical localized
Gamma, concluded field-enlargement equation, Gamma-linked inverse representation,
actual rational/common naturality equations, and actual rational/common coefficient
squares. The fourth arrow remains precomposition by forward PF. The comparisons'
directions, endpoint invertibility restriction, three actual coefficient changes,
full-domain hypothesis and absence of site-perfectness were retained. This worker
self-check is separate from the maintainer's independent delivery review.

Validation uses only scompile.py and deliver2.py. Final outputs are appended below.

## Definition-module extraction

To keep the expanded statements within the required per-file compile limit, the
concrete endpoint and representative definitions are owned by the new definition
node `def-sf-coefficient-gamma-representatives`, module
`Sheaf.Paper.CoefficientGammaRepresentatives`. The item imports that module. The
module defines the same explicit normalized comparisons, canonical integral,
rational and common Gamma representatives described above. Its only postponed proof
is the named inverse-identity theorem for the two literal Gamma images of identities;
the new node explicitly includes those inverse identities. No arbitrary family or
weaker canonicality predicate remains. The source is Step 1 and steps 7–8; searches
found generic `Iso.homCongr` and evaluation/adjunction primitives, and unrelated
TensorComparison structures, but no existing normalized Gamma representatives.
The module split changes no mathematical hypothesis or conclusion.

Final signature layout: `FieldCoefficientSquare` and
`ShiftEquationsPassToFields` are fully expanded Prop definitions in
`CoefficientGammaRepresentatives.lean`; the item's theorems
`field_coefficient_square` and `shift_equations_pass_to_fields` assert them.
The expanded equations described above are unchanged. This keeps each file below
its per-file elaboration limit. The integral inverse-identity theorem belongs to
the new definition node and its source/blueprint docstring, since it supplies only
the proofs needed to package the two explicitly constructed representative maps.

The final two-file check elaborated both modules successfully; the one unused-proof
binder warning was repaired by naming the predicate's proof input `_h`. A clean
rerun and the prescribed dry run follow. The added definition dependency edges were
searched for a path back to this item and none was found. The unrelated inherited
base graph has an existing deep ring-Hom differential cycle; this delivery adds no
edge to that cycle and edits none of those nodes.

Final validation: scompile.py checked both delivered modules cleanly, with no
unexpected warnings. `deliver2.py --no-push` compiled both modules and the existing
owner declaration probe, then reported `OK (dry run): commit 87a9da8098e passes the
preflight and compiles; nothing pushed`. The final delivery follows the same wrapper.
