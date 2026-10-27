## Worker report

Item: `lem-fd-raw-localization-scalar-coherence`.
Module: `Sheaf.Paper.FdRawLocalizationScalarCoherence`.
Primary declaration:
`WeilConjectures.FdRawLocalization.rawLocalizationScalarCoherence`.

The module states the conditional raw-localization result for the actual framework
and PBC integral full subcategories and their actual raw rationalizations. Both
four-field contractions are written out. Every theorem proof is `sorry`; every
definition has real data. There is no new category, coefficient ring, arbitrary
comparison map, or Karoubi completion. No statement correction is needed.

### Hypotheses and objects

* The finite-field datum is `_D : FiniteFieldDatum.{d}`; `l`, `[Fact l.Prime]`,
  `_hl : l ≠ _D.p`, `Ω : Type w`, `[Field Ω]`, `[Algebra ℚ_[l] Ω]`, and
  `[IsAlgClosure ℚ_[l] Ω]` give exactly the stated coefficient conventions.
* `T : Scheme.{u}`, `[IsNoetherian T]`,
  `[dT : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]`, and
  `[iT : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]` give the three
  scheme hypotheses. No structure morphism over the finite field is imposed on T.
  The finite-field, scheme and algebraic-closure universes are independent.
* Fields are `Padic.FiniteCoefficientFields l Ω`; inclusions are proofs `h : E ≤ L`.
  Integral fields use the published `pbcFiniteField.{u} l Ω E`; rational clauses use
  `GeneralAlgebraicallyClosedCoefficients.Stage`, with its definitionally equal
  canonical small-field model.
  This is the canonical `Shrink` model of that finite subfield, not a restriction
  on the universe of Ω or an identification of Ω with the scheme universe.
* `stage E : FdRationalStageComparison l Ω T E` supplies the integral identity
  and its exact raw rationalization. Its `integral_identity` fixes the underlying
  coefficient restriction, `objects` fixes integral objects, `tensors` fixes
  every integral-map/scalar tensor, and `shift_normalization` pins the specified
  shifts. We use only this finite-stage part of the existing definition, not
  `FdCoefficientComparison` or its downstream coherence conclusions.
* `I` abbreviates the supplied integral functor; `suppliedJ` abbreviates its
  supplied rational functor. The conclusion provides `family : RationalFamily`:
  `family.identity` identifies the entire transported functors with `suppliedJ`
  by HEq and `family.shift_identity` identifies all their shift isomorphisms.
  `J` abbreviates these transported functors on the owner's named stages.
  This is the same HEq presentation transport used by the landed parent,
  and imposes no additional hypothesis. `hI` records the assumed integral exactness.
* `U` is `sfConstructibleIntegralScalarExtension` on these exact small-field
  presentations, with the harmless datum-free parameter 0 used by the existing
  general framework. `C` is `pbcIntegralScalarExtension`, the constructible
  restriction of the ordinary derived completed-coefficient tensor functor.
* `scalar`, `assoc`, `unit` and `scalarCommShift` are direct aliases of
  `GeneralAlgebraicallyClosedCoefficients.transition`, `associator`, `unitor`
  and `transitionCommShift`. Thus no scalar/associator/unit/shift is implemented
  a second time. `P` is the recorded `pbcScalarSystem`, including literal identity
  transitions. `integralAssoc` and `integralUnit` retain the published integral
  tensor comparisons and coefficient-inclusion equality transport.
* `ordinary h : FdOrdinaryScalarTransport ... h` is the given ordinary transport;
  its `generators` field fixes all sheafified tensor generators.
* `b h : I E ⋙ C h ≅ U h ⋙ I L` is the given integral comparison in the common
  full categories. `hexact` gives exactness of these two integral routes;
  `hshift` gives commutation of both b and its inverse with specified shifts.
* `hlift` is the actual normalized chain-localization equation from the existing
  coefficient datum: the left side is the restricted b followed by the strict
  computation comparison and coefficient-transport counit. The right side is
  the ordinary derived counit followed by `ordinary.completion`, which is the
  actual `completedScalarChainComparison` after generator-normalized transport.
  Its quotient coordinates and zero shifted-product coordinate are retained.
  The `eqToHom` in this equation is exactly `stage L.integral_identity` evaluated
  on U(K); it identifies the ambient coefficient presentation, not a new map.
* `hcocycle` is precisely the displayed integral inverse equation, with Lean
  composition read left to right: b(k) inverse, C(k) of b(h) inverse, then the
  ordinary integral associator equals I(M) of the completed associator followed
  by b(h.trans k) inverse.
* `hunit` says b(E/E) inverse followed by ordinary multiplication is I of the
  completed integral unit. This is equivalent to the node's completeness unit
  after multiplication and keeps its actual nonidentity completeness map.
  Equal-field substitutions of `hcocycle` include both integral unit cases.

### Conclusion, clause by clause

* After the uniquely fixed presentation transport `∃ family : RationalFamily ...`,
  `∃ j : RawComparison ...` gives exact natural isomorphisms with source
  `scalar h ⋙ J L` and target `J E ⋙ P.T h`, i.e. J_L S_{L/E} → P_{L/E} J_E.
  A natural isomorphism includes its inverse and both inverse equations.
* The first conjunction gives `NatTrans.CommShift` for its hom and inv and
  `IsTriangulated` for both routes. These use the existing PBC shift instances,
  the supplied J shifts, and the uniquely integral-normalized framework shift.
* The next conjunction is the specified integral lift, for every integral K
  and its raw representative K'. It is Q_L of `(b h).inv.app K`, followed by
  the inverse of `pbcScalarIntegralComparison` at I_E(K). This last comparison
  is required because P(E/E) is literally identity whereas C(E/E) is tensor
  with the coefficient ring. For distinct fields it is the existing raw
  factorization transport. Thus this formula really is Q_L(b inverse) in the
  specified source and target, including equal fields.
* The following conjunction is the normalized identity-extension value:
  j(E/E) is J_E applied to the specified framework rational unit. No integral
  completeness map is declared to be identity.
* The next universal equation is exactly the displayed three-field equation:
  j(k) at S(h)K, then P(k)(j(h)), then a^p(h,k), equals J_M(a^s(h,k)) then
  j(h.trans k). This is the same equation as the node, with the opposite
  written order solely because Lean's `≫` composes left to right.
* Two separate universal conjunctions state the source-unit and target-unit
  equations. Their right sides use respectively S(h) of the framework unit
  and the framework unit at S(h)K. They are exactly the two identity
  substitutions, retaining the PBC specified unit associators on the left.
* `fourComparison` is precisely D: j_32 at S_21 S_10 K, followed by P_32(j_21)
  and P_32 P_21(j_10). The first four-field equation appends P_32(a^p_210)
  then a^p_320 and equates it with J_3 of `leftContraction` followed by j_30.
  `leftContraction` is S_32(a^s_210) followed by a^s_320.
* The second four-field equation appends a^p_321 at P_10 J_0 K then a^p_310;
  its right side is J_3 of `rightContraction` followed by j_30.
  `rightContraction` is a^s_321 at S_10 K followed by a^s_310. Unlike replacing
  both right sides with the first contraction, this states both displayed
  formulas literally.
* The final equality equates these two right sides. All quantifiers use ≤,
  including all adjacent equalities and the fully repeated-field case.

### Reuse of the owner's shift

`scalar`, `assoc`, `unit` and `scalarCommShift` directly reuse the owner's
`transition`, `associator`, `unitor` and `transitionCommShift`. The duplicate
`scalarCommShift_existsUnique` theorem has been deleted. No new choice or
postponed shift theorem remains. Rather than forcing elaboration through the
definitionally equal raw-category presentations, `RationalFamily` follows the
parent's HEq approach: it existentially supplies the identical functors on the
owner's stages and identifies their entire shift isomorphisms with the supplied
ones. It carries no scalar comparison, cocycle, unit law or exactness assumption.
All the rational conclusion clauses are then stated on the owner's declarations.
This changes presentation only: `family.identity` and `family.shift_identity`
ensure the same objects, maps and shifts. The coefficient and scheme universes
remain independent. Every integral hypothesis is unchanged.

### Dependency declarations used

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
* `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, `sfRationalScalarExtension`, and their
  original raw tensor-Hom and triangulation structures.
* `Sheaf.Paper.PbcRationalCategory`: `PbcRationalCategory` through the recorded
  PBC finite-stage categories and localization.
* `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`:
  `integralDetailedTransport` and its quotient-normalized coefficient identity,
  used through `FdRationalStageComparison.integral_identity`.
* `Sheaf.Paper.FiniteFreeCompletedScalarComparison`:
  `completedScalarChainComparison`, through `FdOrdinaryScalarTransport.completion`;
  its definition has the actual quotient coordinates and the strict cone lift.
* `Sheaf.Paper.SfScalarExtensionComposition`: `sfIntegralScalarComp`,
  `sfIntegralScalarUnit`, `sfRationalScalarComp`, `sfRationalScalarUnit`.
* `Sheaf.Paper.PbcScalarExtension` and its `FiniteStagePairCategory` interface:
  `pbcIntegralScalarExtension`, `pbcIntegralScalarAssociator`,
  `pbcIntegralScalarUnit`, `pbcScalarIntegralComparison`, `pbcScalarSystem`.
* `Sheaf.Paper.FdCoefficientComparison`: `FdRationalStageComparison`,
  `FdOrdinaryScalarTransport`, `FdOrdinaryScalarTransport.completion`, and
  `fdCoefficientTransportFactors`. Its owning definition node is added to
  stmt_deps because these already-landed interfaces name hypotheses of this item.
* `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`, owned by
  `def-weil-algebraically-closed-coefficients`:
  `integralScalarCommShift_existsUnique`, `transition`, `associator`, `unitor`,
  `transitionCommShift`, and the imported
  `AlgebraicallyClosedCoefficients.coefficientInclusion_laws` used in the integral
  and rational associativity/unit transports.
* `Sheaf.Paper.CommonStageCalculus`: `pbcScalarRestrictCommShift`,
  `pbcAmbientScalarCommShift`, `pbcIntegralScalarCommShift`, now owned by the new
  `def-fd-integral-scalar-shift-structures` attachment. The rational instances
  `pbcScalarCommShift`, `pbcRationalHasShift`, `pbcRationalizationCommShift` belong
  to the landed `def-per-common-stage-shift-structures`. Both definition owners
  are cited; `prop-weil-pbc-common-stage-calculus` is removed from stmt_deps.
* `Sheaf.CategoryTheory.SemilinearScalarLocalization` is a proof import for the
  node's planned semilinear localization argument, not a new scalar construction.

### Edge cases checked

The empty scheme, zero objects and zero morphisms are allowed. Nothing requires
T nonempty or separated or finite type. No strict inclusion is used anywhere;
E=L, L=M, M=N and E=L=M=N have the same typed equations. In particular the
identity P branch still retains ordinary multiplication through
`pbcScalarIntegralComparison`, while j(E/E) uses the framework completeness
unit after multiplication. The zero shifted-product component is inherited
from the actual chain map even for ramified extensions. Coefficient and scheme
sizes remain independent; finite fields use the existing canonical small models.
The prime and distinct-characteristic conditions are explicit.

### Searches made

All service calls used `msearch.py Q63 lem-fd-raw-localization-scalar-coherence`.

* LeanFinder, `raw localization scalar coherence`: eight module-localization
  scalar identities (`IsLocalizedModule.mk'_smul_mk'`, `LocalizedModule.smul_def`,
  `IsLocalization.smul_mk'`, etc.); none states the categorical coefficient
  comparison, integral lift or four-field contractions.
* LeanSearch, `Raw rationalization of a comparison between ordinary derived
  scalar extension and strict completion preserves cocycles units and four field
  associativity`: eight hits about abstract completion, valued extensions,
  number-field completion, CauSeq, uniform completion and Laurent series;
  no matching theorem.
* Initial Loogle, `Localization, scalar, coherence`: invalid identifier `scalar`,
  so this is an invalid query, not evidence of absence.
* Successful Loogle, `CategoryTheory.Functor.map_comp`: six hits, including
  `CategoryTheory.Functor.map_comp` and presheaf map composition; these provide
  elementary functor laws, not this statement.
* Mathlib grep, `semilinear.*localiz|localiz.*semilinear|four.field`: six hits in
  fractional-ideal operations, quaternion descriptions, structure sheaves and
  finite-product monoidal structures; none matches.
* Project rg/grep for the node id in `lean/WeilConjectures`: no declaration.
  Searches for raw/localization, scalar/coherence and four-field concepts in
  `lean/WeilConjectures` and `lean/Sheaf` found the generic semilinear theorem,
  and `FdCompletionInverseScalarCoherence`. The latter is the downstream parent:
  it asserts existence of an entire normalized comparison without the conditional
  b input and uses this item in its DAG proof. It is not an exact match and is
  intentionally not imported (avoids a circular dependency).
  The generic `StageSystem.Morphism` was read, but assuming such a morphism here
  would already assume the cocycle being concluded. The statement instead
  explicitly quantifies the raw natural isomorphisms and concludes all equations.

### Validation

The prescribed server `scompile.py` compiled the repaired file cleanly in both
sandbox (29.1 seconds) and library (15.3 seconds) modes, with no errors or
unexpected warnings. The sole postponed theorem is the item's
`rawLocalizationScalarCoherence`. The delivery dry run checks the full packet.

## Repair of the return on c57e5c6c62bd

1. H2, shift ownership: remove `prop-weil-pbc-common-stage-calculus` from the
   item's statement dependencies, cite the existing rational shift definition
   `def-per-common-stage-shift-structures`, and add the existing-data attachment
   `def-fd-integral-scalar-shift-structures` for the integral and ambient shifts.
2. H2, coefficient owner: add `def-weil-algebraically-closed-coefficients`, whose
   declarations are used for the normalized integral shift and coefficient-map
   composition and identity laws.
3. H4, duplicated owner declarations: delete `scalarCommShift_existsUnique`;
   replace the scalar/associator/unit/shift definitions by direct aliases of the
   coefficient owner's declarations. State every rational clause on those stages,
   using `RationalFamily` to identify the supplied functors and shifts by HEq.
   All integral hypotheses and every accepted mathematical clause are retained.

## New nodes

`def-fd-integral-scalar-shift-structures` attaches definition ownership to the
already implemented `pbcScalarRestrictCommShift`, `pbcAmbientScalarCommShift` and
`pbcIntegralScalarCommShift` in `Sheaf.Paper.CommonStageCalculus`. The construction
is degreewise scalar restriction, its derived adjunction mate, and fully faithful
restriction of that mate to the integral full subcategory. This is the shift
data needed by the coefficient comparison underlying the trace-function unit.
The current blueprint source is the trace-function definition; the implementation
cites the original common-stage calculus order 1307. No module or data is copied.
The new node cites the landed rational shift definition as requested. DAG grep
finds only the theorem owner; blueprint_refs search finds no definition node.
LeanSearch, LeanFinder, Loogle and Mathlib grep found generic shift constructors,
including `Functor.CommShift.ofComp`, but no project-specific coefficient shifts.
Project grep located the exact existing data in CommonStageCalculus:645,651.
All actual queries and results are recorded in the new node's mathlib_searches.

No independent second reading is claimed: the dispatcher instructed this worker
to deliver directly, and the maintainer performs the independent review.

## Second reading by Q63

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
