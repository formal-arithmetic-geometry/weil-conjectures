## Worker report

The module `Sheaf.Paper.TwistedPullbackSquareScalars` states
`WeilConjectures.TwistedPullbackScalars.twistedPullbackSquareScalars`.
All proofs are postponed in the single named theorem, whose docstring supplies the
whole natural-language proof. The supporting modules and their new definition nodes define the maps, equations,
and normalization records explicitly introduced by this node. They contain no sorry.

Hypotheses and clauses, read against the node:

* `B : FiniteFieldDatum` and `C : B.CoefficientDatum` bind p, the positive finite-field
  exponent, its algebraic closure k, ell different from p, and the fixed coefficient
  closure. `Fields C.l C.Qbar` is the actual finite intermediate-field subtype, with
  its existing finite-dimensional instances. `E L` and `h : E ≤ L` allow equality
  and the ground field; no proper-extension assumption or size collapse is imposed.
* The four `Scheme.Over` instances give the structure morphisms to Spec k.
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` on these four morphisms
  say precisely separated finite type over k. The four `IsOver` instances say all
  arrows are k-morphisms. `IsPullback u f' f v` is the Cartesian square; its `w`
  gives exactly `u ≫ f = f' ≫ v`. Only f is assumed separated and smooth of pure
  dimension `d : ℕ`; v is arbitrary. `Geometry` concludes the Noetherian,
  finite-dimension, invertibility and base-changed smoothness facts, rather than
  making them additional hypotheses. `finiteResidueInverse` constructs the residue
  inverse from the recorded coefficient-prime unit theorem.
* The raw framework category is used as coordinates for the raw PBC category, not
  a Karoubi envelope. `Presentation.integral_identity` fixes the integral functor
  as the recorded coefficient transport; `objects` fixes every rational object;
  `tensors` fixes every localized pure tensor with the actual coefficient-field
  equivalence. Its shifts are pinned by integral coefficient restriction and
  localization. `SquareCoordinates` supplies these presentations for all four
  schemes. `ScalarCoordinates.normalization` fixes scalar relabeling by
  `purScalarModel`, the actual `scalarCompletionIso`, and the specified coefficient
  equivalence counits. `rationalization` uses `pbcScalarLocalizationIso`.
* `PullCoordinates` gives the actual completed-pullback restriction for each of the
  four arrows, including arbitrary u and v. `CoordinatePullbackChain.quotients`
  identifies every unit tensor in every degree and quotient; `shifted` is zero.
  `normalization` is the equality against the actual completed-pullback unit and
  strict resolving-class counit. Thus no independent natural isomorphism can be
  substituted. `PullScalarCompatible` equates the actual specified PBC comparison
  (the inverse of `pbcScalarCompletedPullIso`) with the framework comparison under
  these fixed identifications. The general coefficient type in these helpers
  avoids the Shrink-only interface of `FdPullbackComparison` and does not restrict
  any scheme morphism to an isomorphism.
* `D` is exactly `sfRationalTwistingFunctor (d : ℤ) ⋙ shiftFunctor (2*d)`;
  `H` is pullback followed by D. `T` is the existing strict scalar functor.
  `q` is the scalar shift followed by the tensor comparison and the roots-induced
  scalar map of the Tate line. `a` is q followed by D applied to p. `z` is the
  pullback shift, tensor-pullback comparison and roots-induced pullback of that
  line. The integral maps and their rationalizations are already specified by
  `CanonicalTate` on every root tensor, including the empty tensor at d=0.
* `U`, `V`, `t`, `PU`, `PV`, `m`, `rA`, `rB` are the eight displayed composites,
  with the Cartesian equality inserted between the two integral-normalized
  compositors in t. They use no exceptional inverse image or exceptional exchange.
* `SquareEquations` is the conjunction, in order, of (Z), (C), the two intermediate
  identities, and (M), for every raw rational M or K of its specified category.
  Lean composition `≫` runs left to right, reversing the TeX composite notation.
  `Naturality` gives naturality for q, PU, PV, a, rA, rB, z and m; p and t already
  are components of recorded natural isomorphisms.
* `Coherent` states naturality, the exact coefficient-unit equation, and the
  displayed tower equation using `alpha`. `TowerCoherence` applies it to q at
  X and X', all four p's, PU, PV, both a's and both r's. The associator is the
  recorded scalar tensor associator with the equality of subfield inclusions.
* `ShiftData` fixes the comparison of completed tensor by the degree-zero line
  with the termwise twist on every good representative, through the actual
  completion inverse augmentation and `mapBifunctorSingle₂Iso`. Its beta is
  natural; integral and rational D shifts are fixed by this comparison.
  `ShiftCoherence` applies the actual component shift equation to all seven
  families. `SquareShiftEquations` additionally states the shift equations for
  z, t and m, for every integer shift. Thus Z, C and M commute under these same
  identifications; no independently chosen sign is introduced. The shared shift
  is the even integer 2d and the line complex is concentrated in degree zero.
* `TwistCoordinates` identifies these tensor twists with `pbcTateAmbient` on
  integral objects and after raw rationalization. Its coefficient restrictions
  and round trip act identically on sections; the sheaf comparison is their
  explicit conjugation, and the ambient comparison is normalized on every complex.
* `AdicAgreement` first says rational a is the localization of `integralA`.
  Its second equation says this same integral arrow, after the actual completion
  chi maps and the normalized shifted beta comparisons, is precisely
  `AdicPurityScalarNaturality.sourceScalarComponent`. The scalar-closure proof
  needed by that recorded interface is existentially concluded, at both f and f'.

Dependency declarations read and used:

* `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`, especially
  `coefficientPrime_isUnit_stalk`; its `FiniteFieldDatum.CoefficientDatum` fields.
* `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: `IsPullback` and its
  morphism order, commutativity proof and base-change convention.
* `Sheaf.Paper.PbcRationalCategory`: `PbcRationalCategory`,
  `PbcRationalDerivedCategory`, `pbcRationalization`.
* `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleIntegralPullback`,
  `constructibleIntegralTensor`, `rationalDerivedPullback`, `rationalDerivedTensor`,
  `integralPullbackScalarComparison`, `rationalPullbackScalarComparison`,
  `integralTensorScalarComparison`, `rationalTensorScalarComparison`.
* `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: the integral and rational
  twist coefficients and functors; `PbcCoefficientTwists.pbcTateAmbient`.
* `Sheaf.Paper.PbcScalarExtension`: `pbcRationalScalarExtension`,
  `pbcEmbeddingAmbientTensor`, `pbcEmbeddingIntegralTensor`,
  `pbcScalarCompletedPullIso`, `pbcScalarLocalizationIso`, and the conditional
  integral and rational restrictions (no arbitrary unproved preservation premise).
* `Sheaf.Paper.FiniteSmoothPullbackExchange` and the imported
  `FieldWeilShriekShiftData`: the canonical integral-normalized
  `fieldRationalPullComp` and `fieldRationalPullShift`, valid for arbitrary maps.
* `Sheaf.Paper.AdicPurityScalarNaturality`: `ScalarClosed`, `Cat`, and the full
  `sourceScalarComponent` definition, with its ordinary/completed chi conjugation.
* Additional normalization interfaces: `CanonicalTate.rationalPull`,
  `rationalScalarLine`, `integralScalarLine`; `PuritySourceTransports.scalarShift`;
  `CompletedCoefficientPresentationTransport.purCoefficientModel`, `purScalarModel`;
  `FdCoefficientComparison.fdRawTensor`, `fdCoefficientTransportFactors`;
  `RationalSmoothPurityCanonical.tensorToOrdinaryOnGood` and `ordinaryModel`.

Edge cases checked: d=0 retains the coefficient-unit map and zero shift; identity
coefficient inclusions are present in every unit/tower predicate; towers with one
or both equalities remain included; arbitrary and identity v use actual scheme
pullback rather than an inverse; empty schemes require no nonemptiness hypothesis;
negative cochain shifts are explicitly quantified; the base field is a finite
intermediate field. The adic comparison is on every finite-Tor constructible
integral object, and its rationalization uses all objects of the raw category.

Searches made before construction:

* `msearch.py NH lem-pur-twisted-pullback-square-scalars leanfinder`, query the
  scalar square for twisted derived pullback in a Cartesian square: eight ordinary
  tensor/pullback or pseudofunctor results, no declaration of these equations.
* `msearch.py ... loogle`, query
  `CategoryTheory.NatTrans.CommShift, CategoryTheory.isoWhiskerLeft, CategoryTheory.isoWhiskerRight`:
  no exact result (unknown identifier in the combined query).
* `msearch.py ... grep`, query `twisted.*pullback.*scalar|scalar.*twisted.*pullback`
  in CategoryTheory: no match.
* `rg` of the item id in upstream WeilConjectures: no existing declaration.
  Searches of scalar/twist/pullback in upstream and `lean/Sheaf` found the
  canonical constituents listed above, but no theorem stating this whole node.
  Read the actual definitions, their full signatures and normalization docstrings;
  in particular distinguished the isomorphism-only Fd comparison from arbitrary
  scheme pullbacks and the PBC comparison's inverse direction.

There is no statement correction and no STATEMENT-DISPUTED flag. All helper data
are real constructions or specified normalization records concluded by the main
statement. No arbitrary choice of a noncanonical object is used.

## Second reading by NH

This was a separate pass by the dispatcher worker (no other agents were started,
as instructed), with the full node and all files open. The five equation directions
were checked against TeX, using Lean's left-to-right composition. The main signature
assumes smoothness only of f; the base-changed smoothness and the category geometric
bounds are conclusions. The all-subfield tower quantifiers include equal stages.
Two presentation issues found in the pass were repaired: the PBC pullback scalar
map must be inverted, and a full-subcategory shift must be followed by the inclusion's
commShiftIso before applying ambient beta. The repaired adic formula compares the
same integral a and its localization, and the shift records fix both integral and
rational structures. The PBC coordinate records retain the coefficient identity,
all quotient-unit and zero-coordinate data and all localization pure tensors.
The theorem's proof docstring covers every equation and every coherence clause.

## New nodes

`def-pur-twisted-pullback-square-maps` owns `Sheaf.Paper.TwistedPullbackSquareMaps`: Canonical maps and component equations for a twisted pullback square. Define D_W^R(M)=M(d)[2d], H_h^R=D_source(h)^R Lh_R^*, and T_W=T_{L/E,W}. Define q as the scalar shift followed by the tensor scalar comparison and the roots-induced scalar comparison of the degree-zero Tate line; define p as the recorded scalar/pullback comparison, and a_h=D^L(p_h)q. For a commutative square u:X'→X, f:X→Y, f':X'→Y', v:Y'→Y, define U_R=Lu_R^*Lf_R^*, V_R=Lf'_R{}^*Lv_R^*, t_R=c_{f',v}^R(c_{u,f}^R)^{-1} using its commutativity, and z_u^R by the specified pullback shift, tensor comparison and roots-induced pullback of the line. Define P_U=Lu_L^*(p_f)p_u, P_V=Lf'_L{}^*(p_v)p_f', m_R=D^R(t_R)z_u^R, r_A=Lu_L^*(a_f)p_u and r_B=H_f',L(p_v)a_f'. Define SquareEquations to mean, for every M in C_E(X) and K in C_E(Y), exactly the equations (Z), (C), the two expanded r_A,r_B identities and (M) obtained from these actual maps. All tensor orders are M tensor R_W(d); no exceptional pullback enters. Its source is the current purity-transport proof, Steps 1, 2, 4 and the final base-change/composition compatibility, spelling out the comparison notation used in the item. The LeanSearch, LeanFinder, Loogle, Mathlib/project grep, DAG and blueprint searches are recorded with their actual results in mathlib_searches. Generic pullback and CommShift APIs exist and are reused, but no existing definition node provides this specialized normalized record or component predicate. It asserts no theorem or existence of a coherent datum.

`def-pur-twisted-pullback-coefficient-coherence` owns `Sheaf.Paper.TwistedPullbackScalarFamilies`: Unit and tower predicates for the seven twisted pullback comparison families. A coefficient comparison family on an input V and output W consists of the already specified functors F_R and component isomorphisms w_{S/R}:T_W F_R→F_S T_V, for all finite subfields R⊆S, including equality. Define Natural by the component naturality equation. Define Coherent to mean naturality, w_{R/R,K} followed by F_R of the specified scalar unit equals the output scalar unit at F_R K, and alpha_W(F_R K) followed by w_{B/R,K} equals T_{B/S}(w_{S/R,K}) followed by w_{B/S,T_{S/R}K} and F_B(alpha_V(K)). Here alpha is the recorded scalar associator with the equality of composite subfield inclusions. Define TowerCoherence as this predicate for q at X,X', p at all four arrows, P_U,P_V, a_f,a_f',r_A,r_B. Define Naturality also for z and m in both coefficient fields. Its source is the current purity-transport proof, Steps 1, 2, 4 and the final base-change/composition compatibility, spelling out the comparison notation used in the item. The LeanSearch, LeanFinder, Loogle, Mathlib/project grep, DAG and blueprint searches are recorded with their actual results in mathlib_searches. Generic pullback and CommShift APIs exist and are reused, but no existing definition node provides this specialized normalized record or component predicate. It asserts no theorem or existence of a coherent datum.

`def-pur-twisted-pullback-shift-normalization` owns `Sheaf.Paper.TwistedPullbackScalarShifts`: Normalized shifts for the completed tensor Tate twist. Define the integral twist by the actual completed tensor with the degree-zero d-fold Tate line on its right and integral D by its shift [2d]. ShiftData consists of a natural comparison beta of this integral tensor twist with the recorded exact termwise twist. On every good flat-term K-flat representative, beta is the inverse completion augmentation followed by the ordinary tensor representative comparison, the canonical single-complex tensor comparison and the termwise derived comparison. It includes an integral D shift structure fixed by this beta and the full-subcategory inclusion's shift maps, and a rational D shift structure fixed by localization. Define ShiftCompatible for a specified coefficient family by the full component equation for every integer shift using the specified scalar shifts. No existence or coherence of these data is asserted by this definition. Its source is the current purity-transport proof, Steps 1, 2, 4 and the final base-change/composition compatibility, spelling out the comparison notation used in the item. The LeanSearch, LeanFinder, Loogle, Mathlib/project grep, DAG and blueprint searches are recorded with their actual results in mathlib_searches. Generic pullback and CommShift APIs exist and are reused, but no existing definition node provides this specialized normalized record or component predicate. It asserts no theorem or existence of a coherent datum.

`def-pur-twisted-pullback-composite-shifts` owns `Sheaf.Paper.TwistedPullbackCanonicalShifts`: Composed specified shifts of the twisted pullback routes. Use Functor.CommShift.comp with the structures explicitly specified: the shift on U_R is the composite of the canonical pullback shifts of f and u; the shift on H_h is the composite of the canonical pullback shift and the normalized D shift; the shifts on Lu^*H_f and H_f'Lv^* are the corresponding composites in precisely that order. These constructions take the specified D shift as data and introduce no additional structure choice. Its source is the current purity-transport proof, Steps 1, 2, 4 and the final base-change/composition compatibility, spelling out the comparison notation used in the item. The LeanSearch, LeanFinder, Loogle, Mathlib/project grep, DAG and blueprint searches are recorded with their actual results in mathlib_searches. Generic pullback and CommShift APIs exist and are reused, but no existing definition node provides this specialized normalized record or component predicate. It asserts no theorem or existence of a coherent datum.

`def-pur-twisted-pullback-shift-coherence` owns `Sheaf.Paper.TwistedPullbackShiftCoherence`: Shift coherence predicate for all twisted pullback scalar families. For the four-arrow square and d≥0, ShiftCoherence is a record of normalized ShiftData at X and X' for each finite coefficient subfield, together with ShiftCompatible for q at X,X', all four p families, P_U,P_V, both a families, r_A and r_B. The pullback shifts are the recorded integral-normalized shifts and the composite shifts are exactly the specified compositions. The record is data with these fields, not an assertion that arbitrary shift structures are coherent. Its source is the current purity-transport proof, Steps 1, 2, 4 and the final base-change/composition compatibility, spelling out the comparison notation used in the item. The LeanSearch, LeanFinder, Loogle, Mathlib/project grep, DAG and blueprint searches are recorded with their actual results in mathlib_searches. Generic pullback and CommShift APIs exist and are reused, but no existing definition node provides this specialized normalized record or component predicate. It asserts no theorem or existence of a coherent datum.

`def-pur-twisted-pullback-pbc-coordinates` owns `Sheaf.Paper.TwistedPullbackPbcCoordinates`: Normalized raw PBC coordinates and scalar presentation data. For a Noetherian finite-dimensional scheme W with ell invertible, Presentation is the equivalence between the framework constructible category and the raw PBC category, together with its integral equivalence. Its integral functor is exactly integralDetailedTransport; its rational object map is that integral object map and its maps on localized pure tensors are the recorded coefficient-field transport. Its shifts are normalized by exact coefficient restriction and raw localization. For E⊆L, ScalarCoordinates records the ambient scalar-presentation comparison, its constructible restriction and rationalization. Applying the fixed inverse coefficient model to its ambient component gives purScalarModel followed by ordinary scalar applied to the coefficient-equivalence counit, completion chi, and the inverse target counit. Its integral component is that ambient map, and its rational component is the localization of that integral component through the specified scalar localization comparison. Its source is the current purity-transport proof, Steps 1, 2, 4 and the final base-change/composition compatibility, spelling out the comparison notation used in the item. The LeanSearch, LeanFinder, Loogle, Mathlib/project grep, DAG and blueprint searches are recorded with their actual results in mathlib_searches. Generic pullback and CommShift APIs exist and are reused, but no existing definition node provides this specialized normalized record or component predicate. It asserts no theorem or existence of a coherent datum.

`def-pur-twisted-pullback-pbc-pullback-coordinates` owns `Sheaf.Paper.TwistedPullbackPbcPullback`: Whole-tower normalized PBC pullback coordinates and scalar square. For an arbitrary scheme morphism h:X→Y, CoordinatePullbackChain is the map from the actual ordinary PBC module pullback of the relabeled complex to the relabeled framework strict quotient-tower pullback. Every quotient projection on every pulled-back unit generator is the corresponding actual framework quotient generator, and every shifted cone coordinate is zero. PullCoordinates records preservation of the constructible full category, integral and rational pullback presentation comparisons, and an ambient comparison fixed on every good representative by the completed-pullback unit and the strict-tower derived counit. The integral comparison lifts that ambient map and the rational comparison is its raw localization. Define PullScalarCompatible by equality of the two ambient routes: scalar applied to the integral E pull comparison, then the output scalar-presentation comparison, then relabeling of a_h, equals the inverse specified PBC scalar/completed-pullback map followed by completed pullback of the input scalar-presentation comparison and the integral L pull comparison. No inverse of h or flatness of the finite quotient coefficient map is required. Its source is the current purity-transport proof, Steps 1, 2, 4 and the final base-change/composition compatibility, spelling out the comparison notation used in the item. The LeanSearch, LeanFinder, Loogle, Mathlib/project grep, DAG and blueprint searches are recorded with their actual results in mathlib_searches. Generic pullback and CommShift APIs exist and are reused, but no existing definition node provides this specialized normalized record or component predicate. It asserts no theorem or existence of a coherent datum.

`def-pur-twisted-pullback-pbc-twist-coordinates` owns `Sheaf.Paper.TwistedPullbackPbcTwist`: Normalized PBC coordinates of the tensor Tate twist. For a fixed scheme W, finite coefficient field E and d≥0, TwistCoordinates identifies the completed tensor twist with the actual PBC Tate twist. The comparison of the two coefficient restrictions and their round trip act identically on all local sections. The sheaf twist comparison is the target restriction of the inverse round trip after termwise twist, preceded by the comparison of the two restrictions. The derived comparison is fixed by this sheaf comparison on every complex through the actual mapDerivedCategoryFactors maps. The completed tensor comparison is the fixed beta followed by that termwise comparison; the constructible integral comparison is its inverse on underlying maps, and the rational comparison is its raw localization. All of these are normalization fields of the record, not arbitrary identifications. Its source is the current purity-transport proof, Steps 1, 2, 4 and the final base-change/composition compatibility, spelling out the comparison notation used in the item. The LeanSearch, LeanFinder, Loogle, Mathlib/project grep, DAG and blueprint searches are recorded with their actual results in mathlib_searches. Generic pullback and CommShift APIs exist and are reused, but no existing definition node provides this specialized normalized record or component predicate. It asserts no theorem or existence of a coherent datum.

`def-pur-twisted-pullback-adic-agreement` owns `Sheaf.Paper.TwistedPullbackAdicAgreement`: Predicate identifying the rational twisted scalar arrow with the adic one. For a smooth separated k-morphism h of pure dimension d between separated finite-type k-schemes, define integral q using the integral scalar shift, actual completed tensor/scalar comparison and the roots-induced scalar map of the Tate line. Define integral H as constructible pullback followed by integral D and integral a as integral q followed by integral D applied to the actual integral scalar/pullback comparison. Given the scalar-closure proof required by the recorded adic interface and normalized ShiftData, AdicAgreement means: for every inclusion E⊆L and every finite-Tor constructible integral K, rational a at its raw localization is the localization of this integral a; and ordinary scalar applied to the inverse shifted beta, followed by completion chi, this same integral a, the target shifted beta and the shifted twist/pullback of inverse input chi, equals the recorded adic sourceScalarComponent. The full-subcategory inclusion's actual shift comparison is included in each shifted beta. Its source is the current purity-transport proof, Steps 1, 2, 4 and the final base-change/composition compatibility, spelling out the comparison notation used in the item. The LeanSearch, LeanFinder, Loogle, Mathlib/project grep, DAG and blueprint searches are recorded with their actual results in mathlib_searches. Generic pullback and CommShift APIs exist and are reused, but no existing definition node provides this specialized normalized record or component predicate. It asserts no theorem or existence of a coherent datum.

`def-pur-twisted-pullback-square-coordinates` owns `Sheaf.Paper.TwistedPullbackSquareCoordinates`: Simultaneous normalized coordinates for the scalar pullback square. CoefficientCoordinates at a scheme consists of one normalized Presentation for each actual finite subfield and one normalized ScalarCoordinates for every inclusion. ArrowCoordinates between two such systems consists of their normalized PullCoordinates for each field and the PullScalarCompatible equation for every coefficient inclusion. SquareCoordinates consists of these systems at X,X',Y,Y', their ArrowCoordinates on u,f,f',v, and the normalized TwistCoordinates at X and X' for the same ShiftData used by ShiftCoherence. The same endpoint presentations and scalar maps are used on every arrow, including identities and equality coefficient inclusions. Its source is the current purity-transport proof, Steps 1, 2, 4 and the final base-change/composition compatibility, spelling out the comparison notation used in the item. The LeanSearch, LeanFinder, Loogle, Mathlib/project grep, DAG and blueprint searches are recorded with their actual results in mathlib_searches. Generic pullback and CommShift APIs exist and are reused, but no existing definition node provides this specialized normalized record or component predicate. It asserts no theorem or existence of a coherent datum.

`def-pur-twisted-pullback-square-shift-equations` owns `Sheaf.Paper.TwistedPullbackSquareShiftEquations`: Shift equations of the three comparisons in the twisted pullback square. For component isomorphisms w:F→G and specified coherent shift structures on F and G, define ShiftNatural by w_{K[n]} followed by the G shift comparison equals the F shift comparison followed by w_K[n], for every integer n and object K. SquareShiftEquations for the four-arrow square means ShiftNatural for z_u, t and m at every finite coefficient field, using exactly the pullback shifts and the D shifts from ShiftCoherence and their specified composites. Together with the seven coefficient-family shift equations this fixes the shift identifications of (Z), (C) and (M), with line degree zero and common even shift 2d. Its source is the current purity-transport proof, Steps 1, 2, 4 and the final base-change/composition compatibility, spelling out the comparison notation used in the item. The LeanSearch, LeanFinder, Loogle, Mathlib/project grep, DAG and blueprint searches are recorded with their actual results in mathlib_searches. Generic pullback and CommShift APIs exist and are reused, but no existing definition node provides this specialized normalized record or component predicate. It asserts no theorem or existence of a coherent datum.

The delivery tool requires a distinct owning node for every module, so the specialized definition records are supplied separately. None replaces the existing framework operations, Tate lines, scalar functors or raw rational categories. The existing unrecorded framework/PBC bridge theorem is not restated as a new definition; the new records specify the actual normalized maps needed to state this item, whose existence is concluded in the item itself.

Validation: all twelve delivered Lean modules compiled separately with scompile.py on the server against the live published library, in both sandbox and library-module forms. There were no errors or warnings beyond the expected main-theorem sorry warning. The node records retain the original statement and all original fields, changing only lean and adding the new definition ids to stmt_deps.
