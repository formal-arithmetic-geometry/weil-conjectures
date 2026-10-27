## Worker report

This is the stage-2 repair of returned immutable head `fc2b4dd0d36a` for
`lem-sf-package-verdier-coefficient-realization`. The delivery now contains
`lean/Sheaf/Paper/VerdierCoefficientRealization.lean` and the item's JSON with a
verbatim Lean signature. The only postponed theorem is
`WeilConjectures.verdier_coefficient_realization`, whose proof is `sorry`.
`WeilConjectures.VerdierCoefficientRealizationOn` is a fully written conjunction
of the published geometric and coefficient assertions; it constructs no unknown
object and introduces no alternative coefficient category, dual, evaluation or
exchange arrow.

Source read: `literature/blueprint/main-20261015/blueprint/sec-six-functors/`
`sk-thm-sf-package/prop-functor-package.proof.md`, the paragraph beginning
“For (7)”, and the live item and its statement/proof dependencies. That paragraph
names general geometric biduality, the boundary consequence, and all three
coefficient-passage anti-equivalences. The exchange's published construction is
`Sheaf.Paper.VerdierExchange`, read in particular at `StageData.epsilon`,
`StageConclusion`, `Package`, and `Assertion`. The owning definition node is
`def-sf-verdier-exchange-data`.

Hypotheses and conventions, matched to the node:

| Node hypothesis or object | Lean rendering |
| --- | --- |
| The finite-field datum, with k an algebraic closure of a finite field of characteristic p | `D : FiniteFieldDatum.{u}`; `D.k` is the recorded closure, not an arbitrary field |
| A prime ell different from p and a chosen algebraic closure of Q_ell | `C : D.CoefficientDatum`; its instance `C.prime`, inequality `C.different`, and `C.Qbar` |
| A finite extension E/Q_ell | `E : Type u`, `[Field E]`, `[Algebra (Padic C.l) E]`, `[FiniteDimensional (Padic C.l) E]` |
| R, its uniformizer, and A_n, n positive | The dependency constructions `Padic.coefficientExtensionIntegers`, `Padic.coefficientExtensionUniformizer`, and `Padic.coefficientExtensionRing`; positive levels are indexed by `n + 1` |
| Schemes separated and of finite type over k | `[T.Over (Spec (.of D.k))]`, `[IsSeparated (T ↘ Spec (.of D.k))]`, `[LocallyOfFiniteType (T ↘ Spec (.of D.k))]`, `[QuasiCompact (T ↘ Spec (.of D.k))]`; the theorem repeats these for X and Y |
| f a separated finite-type k-morphism | `(f : X ⟶ Y)`, `[f.IsOver (Spec (.of D.k))]`, `[IsSeparated f]`, `[LocallyOfFiniteType f]`, `[QuasiCompact f]` |
| All separated finite-type schemes T, with a_T their structure maps | The first universal quantifier of the theorem and `T ↘ Spec (.of D.k)` |
| The operation datum, finite-Tor categories, completed integral category, raw rationalization and common-stage field category | Imports the recorded six-functor datum and uses its existing coefficient constructions through the finite, integral, rational, common-stage and exchange interfaces listed below; it supplies no extra operation/ambient-adjoint hypothesis |

Clauses, matched to the node and the actual unfolded conclusions:

1. Finite-stage exact anti-equivalence and the invertible evaluation-transpose
   delta: the first conjunct of `VerdierCoefficientRealizationOn` is
   `∀ n, FiniteProEtaleVerdierBiduality C.l E (n+1) ... T a_T`.
   This unfolds to `IsExactAntiEquivalenceOn` on the fixed-scalar presentation of
   the finite-Tor constructible category and `HasInvertibleBidualityOn` for the
   canonical ambient pairing. Its dual is the actual internal Hom into the
   comparison-class exceptional value at the unit. The pairing's equations fix
   evaluation and its transpose, with signed symmetry; no arbitrary double-dual
   isomorphism replaces delta. The module of `thm-fix-general-biduality` is
   publicly imported, as is the operation datum.
2. For all locally closed pieces and closed immersions, the boundary comparisons
   are conclusions: the second conjunct is
   `∀ n, ProEtale.BoundaryDualityInput D C.l C.different E n T a_T`.
   Its index n is the positive level n+1. I read `Piece`, `Boundary`,
   `CanonicalOperations`, `Data`, `Assertions`, and the final definition in
   `BoundaryDualityInput.lean`. They quantify over all the pieces and boundaries,
   assert preservation, and make the specified evaluation-transpose beta
   invertible, including the delta compatibility square. Nothing of this type
   occurs as a theorem hypothesis.
3. Integral coefficients, the dualizing object, and actual reductions: the third
   conjunct existentially supplies
   `w : IntegralFiniteExtension.DualizingDatum C.l T D C.different E`.
   Its `omega` is in the recorded completed integral constructible category;
   `reduction` gives the canonical finite dualizing targets and `coherent` retains
   the quotient-transition equation. A structure-map exceptional `System` and an
   object `U` at the coefficient point are supplied as conclusions. The first
   displayed `Nonempty` identifies U, under the actual inclusion, with
   `VerdierExchange.ringUnit`; the next identifies its exceptional image with
   `w.omega.obj`. Thus the asserted dualizing object is the structure-map
   exceptional value at the coefficient unit, with no arbitrary coefficient-point
   object allowed.
4. Equality of bounded constructibility and the uniform finite-Tor domain,
   preservation, exact anti-equivalence, dimension bounds, finite comparisons,
   evaluation, transposes, and actual delta: this is
   `IntegralVerdier.Conclusion ... w.omega w.reduction` on that SAME w.
   Its clauses include the equality of predicates, restricted dual equivalence,
   exactness, invertibility of `IntegralVerdier.comparison`, evaluation and
   transposition equations, transition evaluation, reconstruction, and natural
   invertible `IntegralVerdier.delta`. Its `_tor_bound` quantifies over every
   nonnegative dimension bound d and every common input interval [a,b] with a<=b;
   the output is exactly `[-b - 2 * (d : ℤ), -a]` at every reduction.
5. Rationalization gives the actual E-linear dual, internal Hom and unit value:
   the integral conjunct additionally supplies `r : RationalVerdier.Datum ... E w`
   and `RationalOperations.HomIdentification ... w r` together with
   `RationalOperations.DualizingIdentification ... S { carrier := E } w`.
   Datum retains the object and pure-tensor functor formulas, canonical coefficient
   coordinates, linearity, exactness, rationalized evaluation and the rationalized
   integral delta. HomIdentification identifies this same dual with the actual
   derived internal Hom and its evaluation. DualizingIdentification identifies its
   omega with the exceptional image of the explicit rational coefficient unit.
6. Coherent finite coefficient-field extension of these rationalized maps:
   `RationalVerdier.Conclusion D C.l C.different T` is the next conjunct. It
   simultaneously covers every finite field and every coherent integral dualizing
   presentation (including the selected w), retaining normalized integral origins
   of the scalar comparisons and their evaluation/delta, unit and associator
   equations. In particular it includes the identity extension.
7. Common-stage exact anti-equivalence, actual internal Hom, exceptional-unit
   omega, evaluation, delta, scalar extensions and retracts: the final conjunct
   supplies `B : CoefQbarVerdier.Duality ... C.Qbar T`,
   `CoefQbarVerdier.InternalHom ... B` and `CoefQbarVerdier.Dualizing ... B`.
   B contains one `SfClassDuality` with the finite-origin normalizations in
   `DualityProperties`. Those include coefficient scalar action, finite dual
   comparisons, evaluation descent, biduality compatibility and the explicit
   evaluation and delta equations for every split retract. InternalHom uses the
   actual evaluation transpose as its universal map. Dualizing identifies B.omega
   with the exceptional image of the coefficient unit. Only these duality clauses
   of `CoefQbarVerdierConclusion` are retained; the extra arbitrary-morphism formula
   for exceptional functors from that dependency is not added to this item.
8. The canonical exchange, naturality, signed shifts and specified coefficient
   comparisons at all four stages: the second conjunct of the theorem is
   `VerdierExchange.Assertion C.l C.Qbar D C.different f`.
   This is the existing assertion, not an unspecified isomorphism between the
   endpoints. It yields `Package` on every choice of the existing normalized
   operations and compactifications. `Package.conclusion s` is a
   `StageConclusion (stage s)`, and its field
   `components (M) : epsilon.hom.app (op M) = d.epsilon ... M`
   PINs the exchange precisely to `StageData.epsilon` of
   `def-sf-verdier-exchange-data`. I read its definition: it applies projection and
   evaluation, then the exceptional homEquiv, c, tensor-Hom transpose and ordinary
   pull/star homEquiv. `RingRealization` and `RingProjection` identify the operations,
   evaluation, adjunction and projection with the actual derived constructions.
   Integral compositor normalization fixes c; `ringScalar`, `rationalization`,
   `rationalScalar` and `common` retain the specified scalar equations and their
   shift comparisons. No ambient exceptional-adjoint admissibility assumption is
   introduced. Finite stages retain the finite-Tor domain; the integral category
   equality above covers the higher integral inputs, and field finite-Tor equals
   constructible by the published definition.

Dependency declarations read and used:

| Module | Declarations |
| --- | --- |
| `Sheaf.Paper.SixFunctorOperationDatum` | `WeilConjectures.SixFunctorOperationDatum` and its Verdier/domain projections, with the public stage constructions |
| `Sheaf.SixFunctors.BoundaryDualityInput` | `AlgebraicGeometry.ProEtale.BoundaryDualityInput` and its `Assertions`, `CanonicalOperations`, `Piece`, `Boundary` definitions |
| `Sheaf.Paper.FiniteStageVerdierBiduality` | `WeilConjectures.FiniteProEtaleVerdierBiduality`, `finite_stage_verdier_biduality` |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | `WeilConjectures.IntegralFiniteExtension.DualizingDatum` |
| `Sheaf.SixFunctors.IntegralVerdier` | `WeilConjectures.IntegralVerdier.Conclusion` and its `dual`, `comparison`, `delta` constructions |
| `Sheaf.SixFunctors.RationalVerdier` | `WeilConjectures.RationalVerdier.Datum`, `Conclusion` |
| `Sheaf.SixFunctors.RationalOperations` | `WeilConjectures.RationalOperations.structureSystem`, `HomIdentification`, `DualizingIdentification` |
| `Sheaf.SixFunctors.CoefQbarVerdier` | `WeilConjectures.CoefQbarVerdier.Duality`, `InternalHom`, `Dualizing` |
| `Sheaf.Paper.VerdierExchange` | `WeilConjectures.VerdierExchange.Assertion`, `ringUnit`, `StageData.epsilon`, `StageConclusion.components`, `Package` |
| `Sheaf.Paper.FiniteTorAmplitudeSites` | The recorded finite/integral/field Tor-domain constructions, used in the proof plan |
| `Sheaf.Paper.DualityPairing` | Canonical ambient evaluation/biduality constructors, used in the proof plan |
| `Sheaf.SixFunctors.BoundaryDualityDischarge` | `AlgebraicGeometry.ProEtale.boundary_duality_input`, proof dependency |
| `Sheaf.SixFunctors.IntegralDualizing` | `WeilConjectures.prop_coef_integral_dualizing`, proof dependency |

The statement dependencies now name definition nodes only. Seven new definition nodes
record exactly the already published declarations used by the signature, with
`existing: true`; they add no Lean modules. The seven theorem nodes named in the
return are absent from `stmt_deps`. The existing `proof_deps` are preserved verbatim;
`lem-coef-integral-finite-extension` remains a transitive proof prerequisite through
the rational-coefficient theorem. The item statement and accepted split are unchanged.

Searches made through the prescribed msearch wrapper (2026-10-22):

- LeanSearch: `Evaluation-defined constructible Verdier duality integral rational and algebraic closure coefficients`;
  eight integral/algebraic-closure hits, no geometric duality/coefficient package.
- LeanFinder: `Verdier duality evaluation biduality constructible coefficient passage integral rational common finite stage`;
  eight unrelated profinite/Nobeling/evaluation hits, no matching theorem.
- Loogle: `CategoryTheory.Equivalence.op`; twelve generic opposite-equivalence
  results, useful background but not this geometric assertion.
- Mathlib grep: `verdierDual|biduality|Verdier`; twenty-five hits, primarily
  Verdier-localization and bibliographic occurrences, no matching coefficient
  realization assertion.
- `rg` in the source `WeilConjectures`, published `Sheaf`, and upstream name index:
  `VerdierCoefficientRealization|verdier_coefficient_realization` gives no existing
  declaration. The item id also gives no existing source declaration. A broader
  source search `verdierDual|biduality|Verdier` finds finite-site and abstract
  duality APIs and Weil-complex duals. These do not state the simultaneous finite,
  integral, rational and common-stage constructible conclusion. The required
  individual interfaces are reused as above rather than copied.

Edge cases checked before accepting the signature: the finite level n=1 is its
zero index, while n>1 retains finite Tor as an additional condition. A residue
module over R/(varpi^2) is not silently admitted as finite-Tor merely for being
constructible. At integral coefficients the common interval is quantified over
reductions of ONE derived-complete object, not arbitrary unrelated complexes.
The zero object and the empty scheme are allowed; there is no Nonempty scheme
hypothesis, and the dimension predicate accepts d=0 for the empty scheme. At d=0
the output is [-b,-a]. Identity f and identity scalar extensions are allowed,
including the normalization equations already in the dependency interfaces.
Integer shifts include negative integers and the signed opposite-category law.
Retracts use contravariant D(p) in evaluation and covariant D^2(p) in delta;
the common-stage interface retains both inverse and forward delta equations.
No independent site/coefficient-universe equality was added; the construction
uses the published common size convention of the operation datum.

There is no STATEMENT-DISPUTED finding and no mathematical statement correction.
The outstanding sorries in dependency modules are not presented as proved facts.
Validation: the complete delivered module passed scompile.py in both sandbox and
library modes, with no errors or non-sorry warnings. The final dry run and push
are recorded by the delivery wrapper.

## Repair of the returned delivery

- H1: supplied an actual statement module, a node lean record, and this report.
  The three lemma nodes from the re-split are excluded from this stage-2 packet.
  Their existing packet passed `deliver.py --no-push` and was pushed through the
  S1 lane at `0443738a0c3`, as the return requested.
- H2/H7: rebuilt the node from the live item. This packet changes only lean and
  adds definition-node statement dependencies; no proof, proof_deps, proof_origin,
  status or split_report edit is delivered. The re-split has its own S1 commit.
- Epsilon normalization: the conclusion is the published Assertion whose
  StageConclusion.components requires equality with the exact StageData.epsilon
  construction owned by def-sf-verdier-exchange-data; it is not a bare Nonempty
  isomorphism between the exchange endpoints.
- H8: the module and both declarations have source/blueprint docstrings, and the
  theorem's docstring carries the full seven-step source proof plan.
- H11: both required report headings are present. The fresh reading below checks
  the actual predicates and maps rather than just their names. No independent
  agent was started, in accordance with the dispatch brief.

## Second reading by Q20

This is a second pass by the same dispatched worker; no other worker or independent
agent is claimed. The maintainer's independent immutable-head review remains
required. I reopened the live node and the delivered Lean module and checked the
following correspondences against the definitions, including the maps underneath
the packaging predicates.

The theorem has exactly the fixed finite-field/coefficient data and separated
finite-type k-schemes and morphism of the item. Finite type is locally finite type
plus quasi-compact. There is no boundary input, admissibility predicate, choice of
a duality, invertibility assumption, dimension bound, or operation System in its
hypotheses. The universal scheme clause covers all T and therefore both X,Y and
the boundary pieces. The chosen finite coefficient field E remains universally
variable, not fixed to Q_ell or to the algebraic closure.

I checked the subtle index issue against BoundaryDualityInput's final definition:
its parameter n already uses coefficientExtensionRing ... (n+1). The finite
biduality interface instead takes an explicit positive exponent, and the file
passes n+1 and its positivity proof. These therefore refer to the same levels;
there is no level-zero omission or extra zero-ring assertion. I clarified this
in the predicate docstring during this reading.

The finite conclusion is a pro-etale statement on the full finite-Tor domain,
with the canonical evaluation transpose. The boundary conjunct is quantified as
a conclusion and retains its canonical map, rather than merely an endpoint
isomorphism. Integral Conclusion is applied to the SAME coherent dualizing datum
whose exceptional-unit identification is in the preceding conjunct. Its category
equality, preservation, exact equivalence, evaluation, delta and precise dimension
interval are all present. The rational datum uses that same integral datum and has
an actual HomIdentification; the separate simultaneous rational Conclusion
provides the scalar coherence including identities and triples. The common-stage
conclusion keeps Duality, InternalHom and Dualizing and retains the explicit
retract equations, while omitting the dependency's extra formula about arbitrary
exceptional inverse images, which the item does not assert.

I reread StageData.epsilon and StageConclusion.components in full. The former is
a definition with real adjunction/projection/evaluation data; the latter equates
the hom component of the natural isomorphism to that definition. Assertion yields
Package with these components at every coefficient stage, ambient realization and
signed shift/comparison fields. This exactly addresses the return's normalization
requirement. I added an explicit explanation naming the owning definition node
to the module docstring. I also added a public import and statement-dependency
edge for the already published coherent integral dualizing-datum interface,
whose type is explicitly used in the statement.

The live item's statement and seven-step proof remain verbatim in this S2 node
copy; the separately submitted S1 commit contains the re-split, rather than mixing
its lemma nodes or split metadata into this packet. The JSON lean.statement was
extracted from the actual theorem signature up to :=, not paraphrased. All Lean
lines meet the 100-character limit; all variables and the universe are explicit;
the only theorem body is sorry. No further mismatch was found on this reading.

## Repair of immutable head fc2b4dd0d36a

H2 / theorem-stmt_dep rule: removed all seven theorem edges named by the return
from the delivered statement dependencies. They are replaced by the seven
`existing: true` definition records below, covering exactly thirteen declarations.
The original two definition dependencies and the published exchange-data definition
are retained. None of the definitions chooses a witness from the owning theorem.
No existing definition is moved, copied, renamed or rewritten. Rebased the node
on the current read clone: only `lean` and the permitted `stmt_deps` delta differ.

The advisory concerns a future restatement linking the coefficient dual data more
directly to the exchange package. This repair preserves the statement judged sound
by the return: the existential integral System is among the Systems universally
quantified by Assertion; its operation and unit are already explicitly identified.
StageConclusion.components continues to pin epsilon to StageData.epsilon. No bare
exchange isomorphism replaces it, and no new hypothesis is introduced.

## New nodes

`def-sf-finite-verdier-biduality-predicate` records finite pro-etale verdier biduality predicate. Its existing declarations are `WeilConjectures.FiniteProEtaleVerdierBiduality` in `Sheaf.Paper.FiniteStageVerdierBiduality`. Its source is the item source paragraph “For (7)”; its statement spells out the data/predicate rather than asserting its existence. Its prerequisites are `def-fix-six-functor-datum`. The shared LeanSearch query returned eight algebraic-closure/integrality hits, Loogle returned twelve generic opposite-equivalence results, and Mathlib grep returned zero hits. The DAG definition-record search and blueprint search found no definition node owning these exact declarations; the source grep located their existing implementations. Thus the record reuses these implementations, with no new module.

`def-sf-coherent-integral-dualizing-datum` records coherent integral dualizing presentation. Its existing declarations are `WeilConjectures.IntegralFiniteExtension.DualizingDatum` in `Sheaf.SixFunctors.CoefIntegralFiniteExtension`. Its source is the item source paragraph “For (7)”; its statement spells out the data/predicate rather than asserting its existence. Its prerequisites are `def-fix-six-functor-datum`. The shared LeanSearch query returned eight algebraic-closure/integrality hits, Loogle returned twelve generic opposite-equivalence results, and Mathlib grep returned zero hits. The DAG definition-record search and blueprint search found no definition node owning these exact declarations; the source grep located their existing implementations. Thus the record reuses these implementations, with no new module.

`def-sf-integral-verdier-conclusion-predicate` records integral verdier compatibility predicate. Its existing declarations are `WeilConjectures.IntegralVerdier.Conclusion` in `Sheaf.SixFunctors.IntegralVerdier`. Its source is the item source paragraph “For (7)”; its statement spells out the data/predicate rather than asserting its existence. Its prerequisites are `def-fix-six-functor-datum`, `def-sf-coherent-integral-dualizing-datum`. The shared LeanSearch query returned eight algebraic-closure/integrality hits, Loogle returned twelve generic opposite-equivalence results, and Mathlib grep returned zero hits. The DAG definition-record search and blueprint search found no definition node owning these exact declarations; the source grep located their existing implementations. Thus the record reuses these implementations, with no new module.

`def-sf-rational-verdier-data` records rationalized verdier data and coherence predicate. Its existing declarations are `WeilConjectures.RationalVerdier.Datum`, `WeilConjectures.RationalVerdier.Conclusion` in `Sheaf.SixFunctors.RationalVerdier`. Its source is the item source paragraph “For (7)”; its statement spells out the data/predicate rather than asserting its existence. Its prerequisites are `def-fix-six-functor-datum`, `def-sf-coherent-integral-dualizing-datum`. The shared LeanSearch query returned eight algebraic-closure/integrality hits, Loogle returned twelve generic opposite-equivalence results, and Mathlib grep returned zero hits. The DAG definition-record search and blueprint search found no definition node owning these exact declarations; the source grep located their existing implementations. Thus the record reuses these implementations, with no new module.

`def-sf-rational-verdier-identifications` records rational internal-hom and dualizing identifications. Its existing declarations are `WeilConjectures.RationalOperations.structureSystem`, `WeilConjectures.RationalOperations.HomIdentification`, `WeilConjectures.RationalOperations.DualizingIdentification` in `Sheaf.SixFunctors.RationalOperations`. Its source is the item source paragraph “For (7)”; its statement spells out the data/predicate rather than asserting its existence. Its prerequisites are `def-fix-six-functor-datum`, `def-sf-coherent-integral-dualizing-datum`, `def-sf-rational-verdier-data`. The shared LeanSearch query returned eight algebraic-closure/integrality hits, Loogle returned twelve generic opposite-equivalence results, and Mathlib grep returned zero hits. The DAG definition-record search and blueprint search found no definition node owning these exact declarations; the source grep located their existing implementations. Thus the record reuses these implementations, with no new module.

`def-sf-common-stage-verdier-data` records common-stage verdier data and realization predicates. Its existing declarations are `WeilConjectures.CoefQbarVerdier.Duality`, `WeilConjectures.CoefQbarVerdier.InternalHom`, `WeilConjectures.CoefQbarVerdier.Dualizing` in `Sheaf.SixFunctors.CoefQbarVerdier`. Its source is the item source paragraph “For (7)”; its statement spells out the data/predicate rather than asserting its existence. Its prerequisites are `def-fix-six-functor-datum`, `def-sf-rational-verdier-data`, `def-sf-rational-verdier-identifications`. The shared LeanSearch query returned eight algebraic-closure/integrality hits, Loogle returned twelve generic opposite-equivalence results, and Mathlib grep returned zero hits. The DAG definition-record search and blueprint search found no definition node owning these exact declarations; the source grep located their existing implementations. Thus the record reuses these implementations, with no new module.

`def-sf-all-stage-verdier-exchange-package` records all-stage normalized verdier exchange package. Its existing declarations are `WeilConjectures.VerdierExchange.Package`, `WeilConjectures.VerdierExchange.Assertion` in `Sheaf.Paper.VerdierExchange`. Its source is the item source paragraph “For (7)”; its statement spells out the data/predicate rather than asserting its existence. Its prerequisites are `def-fix-six-functor-datum`, `def-sf-verdier-exchange-data`. The shared LeanSearch query returned eight algebraic-closure/integrality hits, Loogle returned twelve generic opposite-equivalence results, and Mathlib grep returned zero hits. The DAG definition-record search and blueprint search found no definition node owning these exact declarations; the source grep located their existing implementations. Thus the record reuses these implementations, with no new module.

## Second reading by Q20 — returned-head dependency repair

I reopened the unchanged delivered module, all thirteen recorded signatures and
structure/predicate bodies, the seven new JSON nodes, and the current item. This
is another reading by the same dispatched worker; no independent agent was started.
The seven records cover precisely finite biduality, coherent integral dualizing data,
integral Conclusion, rational Datum/Conclusion, common-stage Duality/InternalHom/
Dualizing, rational structureSystem/HomIdentification/DualizingIdentification, and
exchange Package/Assertion. The original exchange-data record already owns ringUnit,
StageData and StageConclusion; its new package node supplies only Package/Assertion.
The new nodes have no theorem statement dependencies, no proof steps, and no existence
assertions masquerading as definitions. They preserve the real evaluation, reduction,
scalar, shift, and retract normalizations. The existing theorem signature still has
the same hypotheses and eight clause correspondences listed above. Positive n+1,
empty schemes, identity morphisms/scalar extensions, negative shifts, and d=0 remain
covered. The only mismatch found was definition ownership through theorem stmt_deps;
this repair changes those graph edges and records only. All new signatures were
extracted verbatim from their present source files. No statement correction or
STATEMENT-DISPUTED finding is needed.
