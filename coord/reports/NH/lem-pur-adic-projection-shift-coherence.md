## Worker report

Item: `lem-pur-adic-projection-shift-coherence`. Module:
`Sheaf.Paper.AdicProjectionShiftCoherence`; main declaration:
`WeilConjectures.adicProjectionShiftCoherence`.

The mathematical statement and the Lean module are unchanged. The delivery adds the
Lean record and definition-owner dependencies for the canonical ringed/completed
models, signed shifts, exceptional-adjunction presentation data, tensor calculus, and
canonical ringed projection maps. One new existing:true definition node owns the two
already-published projection definitions; no dependency record is changed.

### Hypotheses and objects

- `D : FiniteFieldDatum.{u}` supplies the fixed finite-field datum and its algebraic
  closure k. `C : D.CoefficientDatum` supplies `C.l`, its primality, `C.different`
  (ell != p), and the fixed coefficient algebraic closure `C.Qbar`.
- `F : Type u`, `[Field F]`, `[Algebra ℚ_[C.l] F]`, and
  `[FiniteDimensional ℚ_[C.l] F]` are the arbitrary finite extension E/Q_ell.
  The actual coefficient sheaf is `PurCompactSupport.completed C.l F`, the limit
  of the existing positive quotient rings of its integer ring. No finite level is
  fixed or introduced into the integral statement.
- `X Y : Scheme.{u}`, their `Over (Spec (.of D.k))` instances, and
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` on both structure maps
  express separated finite-type k-schemes.
- `f : X ⟶ Y`, `[f.IsOver (Spec (.of D.k))]`, `[IsSeparated f]`,
  `[LocallyOfFiniteType f]`, `[QuasiCompact f]` give the separated finite-type
  k-morphism. `c : Compactification f` is its chosen compactification. The theorem
  is universal in c.
- `T : finiteTorConstructibleIntegralCategory C.l F X` is exactly the full
  derived-complete constructible category with one uniform finite Tor interval
  for all positive reductions. There is no concentration hypothesis on T.
  `K` ranges over the same recorded full category on Y.
- `S : ConstructibleExceptionalCoefficients.RingSystem ...` presents the actual
  exceptional adjunction, with its recorded `left` realization identifying its
  left functor with the proper/open integral compact support on every arrow.
  This is universally quantified normalized presentation data, not an additional
  admissibility hypothesis. The statement uses this bound datum and its normalized
  left realization; it does not invoke `exists_system`. Right adjoints with their
  Hom transposes are unique.
- `d : RingedModels C.l F`, `b : RingedOpenComparisons C.l F d` are the
  already-recorded presentations of the canonical tensor, pullback, and open
  comparisons. Their fields fix the ordinary maps, K-flat representatives,
  quotient/Roos completion units, and open Hom transpose. They do not allow an
  arbitrary replacement projection or a lift chosen only after finite evaluation.

### Every clause of the conclusion

1. `adicProjection` is inverse source completion, then the recorded
   `ringedCompactificationProjection`, then target completion. In the last arrow
   it inserts the ordinary-to-completed pullback unit in the second tensor slot.
   This is precisely the canonical projection in completed coordinates, with
   the proper counit mate, open tensor comparison, and pullback-composition
   identification in their recorded order. The underlying maps and tensor
   symmetries are inherited, not redefined.
2. `hχ`, `hA`, `hPF` are existential conclusions, not hypotheses. They say the
   source completion comparison is invertible on these inputs; that
   `T completedTensor pull(K)` belongs to the same full finite-Tor category
   (needed to type its exceptional transpose); and that the displayed canonical
   projection itself is invertible, respectively. Inverses take precisely these
   witnesses. Proof irrelevance makes the chosen invertibility witnesses immaterial.
3. `adicTraceTensor` is t tensor identity followed by the canonical unit
   identification. It is expressed through ordinary tensor and its actual
   completion unit; `d.tensorClosed` identifies the ordinary tensor with the
   recorded closed structure and its coefficient unit. `adicTraceMap` is exactly
   inverse PF followed by `adicTraceTensor`, thus the node's u_K.
4. The first two conjuncts state `AdicProjectionShiftSquare` separately for
   `Compactification.ofIsProper f` and `Compactification.ofIsOpenImmersion f`.
   In these compactifications the other constituent is the identity. Their
   recorded unit/counit normalizations identify these maps with the proper mate
   and open extension comparison. The universally quantified theorem applies
   to the proper and open maps of any c, including first input j_!T for its
   proper map. This gives the constituent squares, not just a claim that their
   composite commutes.
5. The explicit projection equality is PF at K[1], followed by the second-input
   comparison and compact-support shift, equal to the tensor shift followed by
   PF_K[1]. `adicTensorPullShift` uses `fieldIntegralPullShift` and the
   representative-normalized `(tensorShifts ...).integralRight`: on first
   degree a the latter is the sign (-1)^a. `adicTensorInputShift` also includes
   the fully faithful subcategory-inclusion comparison. This retains the
   proper-derived and exact-open shifts through `image.commShiftIso`.
6. `adicSupportShift` transports this actual proper/open shift across
   `S.left` and the fully faithful inclusion, instead of using an unspecified
   shift on an abstract exact functor. `adicExceptionalShift` is its adjunction
   mate. The `∃! σ` conjunct uses
   `Adjunction.CommShift.CompatibilityCounit` for this left shift. It is the
   characterization by the counit shifted by one, among all natural comparison
   isomorphisms; no extra coherence assumption narrows the uniqueness claim.
7. The final universally quantified t has type `P(T.obj) ⟶` the actual coefficient
   tensor unit on Y. Its first equation says u_{K[1]} followed by the inclusion
   shift equals P of the tensor-pullback shift, then P's shift, then u_K[1].
   These are the fully typed identifications suppressed in the displayed node.
8. `adicTranspose` uses the actual `S.operation ... .adjunction.homEquiv` after
   `S.left`, and projects its arrow through the full inclusion. Its input object
   has the property `hA K`, so it is not an adjunction assumed on an unrestricted
   pro-etale derived category. The last equality is gamma_{K[1]}, followed by
   `adicExceptionalShift` and the inclusion shift on G(K), equal to the
   tensor-pullback input shift followed by gamma_K[1].

### Dependency declarations used

- `Sheaf.Paper.PurityFiniteSetting`: `PurityFiniteSetting`, with the reused
  `FiniteFieldDatum` / `CoefficientDatum` fields relevant at the integral stage.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`; quotient constructions used by
  `PurCompactSupport.completed` are the existing coefficient-extension ones.
- `Sheaf.Paper.FiniteTorAmplitudeSites` (publicly reexporting `FiniteTorAmplitude`):
  `finiteTorConstructibleIntegral`, `finiteTorConstructibleIntegralCategory`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: recorded integral operations
  `integralDerivedPullback`, `integralCompletedTensor`, underlying the constructible
  pullback and tensor restrictions. The theorem uses their ambient objects and
  the recorded full-subcategory predicates, not private category copies.
- Mathlib: `HasShift`, `ObjectProperty.FullSubcategory`, its inclusion shifts,
  `Functor.CommShift.ofComp`, `Adjunction.rightAdjointCommShift`, and
  `Adjunction.CommShift.CompatibilityCounit`.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `SuppliedExchangeProjection.compactificationProjectionFromData`, used by the
  recorded ringed compactification projection.
- `Sheaf.Paper.QcqsCompactSupportRealization`: `sfQcqsCompactSupportRealization`
  identifies `PurCompactSupport.image` with exactly the strict quotient-tower
  integral compact support. The RingSystem's `integralLeft_normalized` retains
  that identification; it is not merely an objectwise isomorphism.
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  `Scheme.sfIntrinsicExtensionByZero`, used in the finite constituents of the
  recorded completed proper/open construction.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`:
  `RingSystem`, `Operation`, `RingSystem.left`, `RingSystem.integralLeft_normalized`,
  `integralTriangulated`. These definitions and the closure interface are owned by
  `def-weil-exceptional-inverse-image`; the imported module publicly reexports
  `ConstructibleExceptionalAdjunctionCoefficientsData`. `exists_system` is not used.
  `adicFiniteTorTriangulated` only applies the last existing theorem to an explicit field package so instance synthesis
  can see the inherited full-subcategory shift. It proves no new theorem.
- `Sheaf.SixFunctors.IntegralSystemCanonicalBridge`:
  `RingedModels`, `RingedOpenComparisons`, `Expression.completionMap` and their
  representative/completion normalization. The helper's projection formula is
  the component of this existing completion-map conjugation.
- `Sheaf.SixFunctors.IntegralCompactificationSystemRealization`:
  `ringedCompactificationProjection`, `ringedProperProjection`, owned by the new
  definition node below. `calculus` and its fixed closed coefficient unit come from
  `Sheaf.SixFunctors.IntegralSystemOperations`, owned by
  `def-sf-integral-system-operations`. The simultaneous realization theorem remains
  a proof dependency already present in the base DAG.
- `Sheaf.SixFunctors.IntegralOperationShiftData`: `tensorShifts`, `integralShifts`;
  `fieldIntegralPullShift` is reused from its public dependency.
- Proof imports: `CompactSupportProjectionFormula`, `ProjectionMateExact`,
  `ProEtaleExtensionZero`, the recorded upstream `OpenLowerShriekProj`,
  `IntegralRealizationShiftCoherence`, and upstream `IntegralCoefficients`.
  The old `prop-coef-integral-exceptional-adjoint` binding is ordinary-etale;
  no substitution of that category for the completed pro-etale category is made.
  The already-landed normalized integral adjunction interface above supplies
  precisely the bound adjunction data used here, through the definition owner
  `def-weil-exceptional-inverse-image`.
- The proof dependencies `lem-pur-system-level-projection-formula-coherence` and
  `lem-weil-pbc-adjunction-shift-compatibility-unique` have no recorded Lean module
  in this checkout. They are described in the theorem's proof plan. The latter's
  generic shift characterization is already available in Mathlib. All proof
  dependencies with recorded modules are imported, with statement imports public.

### Edge cases

Read the statement with T=0, K=0, and t=0: every composite still has its indicated
type; the equation specializes to the zero-arrow equation. Empty X or Y imposes
no nonemptiness condition; the zero full derived category and the proper/open
constructions still apply. Identity morphisms and proper-only and open-only
compactifications are expressly included. T may be any shift of any finite-Tor
object, especially O_E(d)[2d]; no connective, degree-zero, amplitude endpoint,
rank-one or invertibility assumption is present. The sign depends on each actual
first-input degree and is not replaced by 1. Although the theorem asks for shift
one, negative degrees of T and K are unrestricted. Coefficient reductions use
positive exponents n+1 in the existing construction and never the zero quotient.
The small site keeps object universe u+1 and morphism universe u; no equality of
these universes is imposed. The named source and main-20261015 purity-transport
text were both read; this node is the adic-step compatibility calculation, not
an assertion of purity or smoothness.

### Searches and compilation

- msearch.py, leanfinder: “compact support projection isomorphism commutes with
  cochain shifts and trace adjoint transpose integral coefficients”. Eight generic
  cochain/Hom shift hits; no matching integral compact-support statement.
- msearch.py, loogle: `CategoryTheory.NatTrans.CommShift, CategoryTheory.Adjunction`.
  Four generic adjunction shift/unit/counit constructors; no completed projection
  and trace-transpose statement.
- msearch.py, grep: `projection.*[Ss]hift|[Ss]hift.*projection`, CategoryTheory.
  No direct matching Mathlib declaration.
- rg over shared `lean/WeilConjectures` and `lean/Sheaf`: the item's id has no
  declaration. `LowerShriekProjectionShift` states the ordinary-etale projection
  shift, and `ProjectionMateExact` the generic ringed mate shift. Neither states
  the normalized integral completed projection together with its trace transpose.
  Integral realization and signed completed-tensor interfaces were found and reused.
- Searched the planned declaration names in both source trees and the upstream
  name index. No public declaration of these names already exists. The unrelated
  private helper `adicTranspose` in `CompleteCoefficientDatum` has a mangled private
  name and concerns underived scalar adjunctions, not this exceptional transpose.
- Every compiler call used the prescribed scompile.py. Correct module-mode probes
  resolve the apparent legacy duplicate-import errors; no library repair is needed.
  The final module compiles in sandbox and library mode without errors or warnings
  (approximately nine seconds each under the default sixty-second cap).

No STATEMENT-DISPUTED flag and no mathematical statement correction.

## Second reading by NH

This is a second read-through by the writing worker, not a fabricated independent
review. The dispatcher explicitly forbids starting other agents and assigns the
independent delivery review to the maintainer.

With the node and module open, I matched the global field and prime data, finite
coefficient extension, both separated finite-type structure morphisms, and the
morphism's base/separated/finite-type hypotheses with the section binders. I checked
that every quantified T and K belongs to the original completed pro-etale uniform
finite-Tor category. I replaced an initial ordinary-etale exploratory draft in full:
it was the wrong coefficient category and did not state the trace equations.

I then traced the actual canonical maps: inverse source completion, proper mate,
open tensor comparison, completed pullback unit and target completion; inverse PF,
t tensor identity and coefficient unitor; finally the full-subcategory exceptional
Hom transpose. No arbitrary map or unspecified endpoint isomorphism appears.
The closure/invertibility data are outputs. The proper and open constituent clauses
are explicit. The projection, u and gamma equations use the recorded second-slot
sign and retain all full-subcategory shift identifications. The right shift is the
mate of the canonical support shift and its counit characterization is unique among
all natural comparisons. The final compiler checks validate these source and target
types. No concentration or smoothness hypothesis was introduced. The remaining
independent mathematical review is the maintainer's delivery review.


## Repair of return L (immutable head 3fe5bb70672f)

The saved packet first passed deliver2.py --no-push (commit 5a83a7788fc), but that
mechanical check did not repair the reviewer's H2 ownership objection. I compared
the saved node with current main: only `lean` and added `stmt_deps` differ, and all
original main dependencies are retained in order. The repair addresses both
numbered points and the additional calculus-owner request:

1. Replace the added theorem dependency
   `lem-sf-constructible-exceptional-adjunction-coefficients` with the already-landed
   existing:true definition node `def-weil-exceptional-inverse-image`. The statement
   binds S; it uses its RingSystem/Operation/left data and inherited integral
   triangulated interface, not the `exists_system` assertion.
2. Replace the added theorem dependency
   `lem-sf-integral-compactification-system-realization` with
   `def-pur-integral-ringed-projection-maps`, the existing:true definition owner of
   `ringedProperProjection` and `ringedCompactificationProjection` on their unchanged
   published module. The realization theorem remains an original proof dependency.
3. Add `def-sf-integral-system-operations`, the recorded owner of `calculus`.

The mathematical statement, proof plan, proof dependencies, all original node
metadata, and all Lean declarations are retained. The module SHA-256 before and
after this repair is
`a8d53e3d1e5c578066e449754960a0c8d750aef1afc1ead4e864bd8688dfff9d`.
The reviewer explicitly checked its Lean substance as sound and requested this
byte-identical preservation. The report above now distinguishes definition data
from existence and realization assertions.

## New nodes

`def-pur-integral-ringed-projection-maps` owns exactly the existing canonical
ringed proper projection and ringed compactification projection definitions in
`Sheaf.SixFunctors.IntegralCompactificationSystemRealization` (lines 130 and 161).
Its source is the final projection paragraphs of current-blueprint
`sec-six-functors-basics/sk-def-sf-exchanges/def-exchange-projection.md`. The proper
map is the right-adjoint projection mate of the normalized tensor/pullback map;
the compactification map is this proper map, the open tensor comparison, and the
inverse pullback compositor plus the compactification equation, in that order.
The new node asserts no isomorphism or realization property. Its exact existing
signature is copied from the published module. No new Lean file is introduced.

Searches for this owner: LeanSearch returned eight ordinary scheme-projection
hits; Loogle returned no hit (unknown indexed identifier
`CategoryTheory.Adjunction.rightAdjointProjectionMap`); msearch grep over
Mathlib/CategoryTheory returned zero hits. Exact rg over the DAG found only the
theorem owner `lem-sf-integral-compactification-system-realization`; exact rg over
both source trees found these definitions in the published module and no upstream
copy. `blueprint_refs.py search ringedCompactificationProjection` returned zero;
`search compactification projection` returned `def-sf-pf`,
`det-sp-tower-shriek-levels`, and `thm-sf-pf-adic`, none owning these two maps.
All search outputs are recorded in the new node's mathlib_searches. This is an
existing:true binding, not a second definition of either map.

I re-read the new node against both definition bodies: the proper mate is exactly
`rightAdjointProjectionMap (Functor.curry.mapIso (ringedTensorPull ...) ...).hom`.
The three factors in the compactification formula match the three displayed
composites of `ringedCompactificationProjection`. Arbitrary integral objects are
allowed in this definition; finite-Tor and invertibility restrictions belong to
the consumer theorem. Zero objects, empty schemes, identity arrows, and proper-only
or open-only compactifications introduce no extra hypothesis in either definition.
The existing definition binders use a single explicit scheme/coefficient universe
u and retain the original small-site sizes.

The second reading by NH includes the ownership repair and new node. This is a
self-check, as required by the dispatcher prohibition on starting other agents;
the maintainer supplies the independent review. No mathematical statement
correction or STATEMENT-DISPUTED flag is needed.


Validation after the ownership repair: scompile.py compiled the preserved module
cleanly in sandbox mode (9.3 s) and library mode (9.1 s). The local packet self-check
confirmed the exact original metadata, unchanged Lean hash and verbatim main
signature, retention of every base dependency, and equality between the new node's
bracket citations and its stmt_deps. The repaired dry run also checks both existing
projection declarations through the server.


The repaired packet's first live preflight found one stale ancestry field: the
server item's blueprint.from.via includes lem-pur-adic-purity-scalar-naturality,
which the read clone omits. I set the new node's blueprint.from.via to exactly
[lem-pur-adic-projection-shift-coherence, lem-pur-adic-purity-scalar-naturality],
as the diagnostic requires. No Lean or mathematical statement changed.
