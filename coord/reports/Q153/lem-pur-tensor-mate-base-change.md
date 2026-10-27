## Worker report

This stage-2 delivery states `AlgebraicGeometry.ProEtale.tensorMateBaseChange` in
`Sheaf.Paper.TensorMateBaseChange`. Its proof is `sorry`; all helper definitions contain
actual canonical maps. The accepted stage-1 statement, split, and dependency lists are
unchanged. The inherited unchanged-node rejection came from the earlier stage-1
handoff; the current item has no Lean record and is being delivered with deliver2.py,
as clarified in coord/brief-stage2.md section 0.

Hypothesis-by-hypothesis and clause-by-clause reading:

- `P : WeilConjectures.PurityFiniteSetting.{u}` retains the fixed finite-field datum,
  the coefficient prime distinct from the characteristic, the specified finite
  subextension E of the fixed coefficient closure, and the positive level. The
  coefficient is exactly `P.Coefficient = ULift P.Ring`, where `P.Ring` is
  `Padic.coefficientExtensionRing P.coefficients.l P.extension P.level`.
  No field or coefficient datum is replaced by an arbitrary finite ring.
- `Scheme.{u}` and the four `Over (Spec (.of P.field.k))` instances are the four
  k-schemes. Each structure map has `LocallyOfFiniteType` and `QuasiCompact`,
  exactly finite type over the fixed field. None has absolute separatedness.
- The four `IsOver` instances assert that all four arrows are k-morphisms.
  Only f is assumed `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`.
  There is no separatedness assumption on g or g'.
- `sq : IsPullback g' f' f g` is the Cartesian square, including every realization
  of the fiber product. X, Y, X', Y' respectively denote T, U, T', U' in the node;
  f, g, g', f' respectively denote u, v, w, u'.
- `c : Compactification f` is arbitrary. The equation definitions install the
  available compactifications of f and f' from c and `c.ofIsPullback sq`.
  The canonical upstream compact-support exchange includes the comparison from
  this proper-then-open computation to the chosen compact-support functors.
  HasCompactification is propositional; it is not asserted that its choice is
  definitionally the supplied c. Independence and canonical refinement comparisons
  are retained by the upstream exchange construction. No independently specified
  exchange is an input to this statement.
- The first conjunct quantifies over every actual small pro-etale derived object
  K with `DerivedCategory.constructibleFiniteTor` and asserts that actual
  `(upperStar _ g).leftDerivedFunctor.obj K` has the same property.
  Its further universal quantification over a, b preserves every Tor interval
  `DerivedCategory.torAmplitudeIn _ Y a b K`, rather than merely asserting
  existence of some interval. In particular zero objects and every admissible
  wider interval are included.
- `standingExceptionalBaseChangeCompared` is nu_X'^* applied to the existing
  etale `rightDerivedUpperShriekBaseChangeMap` at the retained origin. The latter
  is, by its definition, `mateEquiv` of the inverse of the canonical compact-support
  exchange. Hence its transpose is inverse exchange followed by pullback of the
  counit, with exactly the node's direction. It is a map, not an assumed isomorphism.
- The comparison coordinates are the same ones already used by the recorded
  `finiteComparedTensorClause` and `finiteComparedBaseChangeClause` in
  def-pur-co-smoothness: source and target are comparison images of the ordinary
  etale expressions. The canonical pullback comparison and the normalized
  right-adjoint comparison identify them with the displayed pro-etale endpoints.
  `finiteSiteExchangeTransposes`, `finiteSiteThetaTransport`, and
  `finiteSiteOriginIndependence` provide the specified counit/transpose and
  origin-independence identifications. No ambient pro-etale exceptional adjunction
  or mere choice of an endpoint isomorphism replaces them.
- `tensorMateBaseChangeUnitNormalization` states comparison of b at the coefficient
  unit followed by G' applied to `leftDerivedUpperStarUnitIso`, equals comparison
  of `dualizingComplexBaseChangeMap`. By functoriality this is the same composite
  as the transported b followed by the transported unit normalization. Its endpoints are the
  precise unit-normalized endpoints; no arbitrary lift of the unit is quantified.
- The last conjunct quantifies over every etale K whose comparison image is Dctf.
  Every pro-etale Dctf object has such an origin. Naturality in an origin isomorphism
  and the normalized site Hom bijection identify this equality with the equality
  for the original pro-etale object; no input is lost or restricted to perfect
  coefficient complexes or invertible objects.
- In `tensorMateBaseChangeIdentity`, the left composite is comparison of pullback
  of the omega-first upstream theta, followed by the standing b component. The
  right composite first applies `leftDerivedUpperStarTensorIso` to omega tensor
  pullback(P), then beta tensor identity, then the canonical
  `derivedSquareUpperStarIsoInvApp` in the second factor, then theta' at g*P.
  Both sides are actual pro-etale derived arrows after comparison. Distributing
  comparison over the left composite gives the recorded
  `standingExceptionalBaseChangeCompared` component preceded by the pullback
  of theta. Writing comparison once around the entire composite avoids expensive
  elaboration of its expanded source/target types and changes no morphism.
  This is the
  coefficient-first equation in the node precomposed with the canonical symmetry:
  theta_coefficient = symmetry followed by theta_omega. Pullback/tensor comparison
  preserves symmetry, and its naturality identifies (1 tensor beta) followed by
  symmetry with symmetry followed by (beta tensor 1). Cancelling this common
  source isomorphism identifies the two equations exactly. This is also the
  convention in the dependency's `finiteComparedTensorClause`. No arbitrary
  endpoint isomorphism or independent choice of braiding is introduced.
- Neither the theorem nor its helper definitions assume cohomological smoothness,
  invertibility of P, or invertibility of theta, b or beta. The only inverted maps
  are the upstream canonical projection/exchange and comparison isomorphisms.

The main theorem docstring includes the node's six proof steps, including the
preservation argument, injectivity of the constructible transpose, proper/open
exchange identification, inverse projection/exchange calculation, equality of the
two transposes, and the coefficient-first symmetry calculation. No theorem is proved.

Dependency declarations read and used:

- Sheaf.Paper.PurityFiniteSetting: `WeilConjectures.PurityFiniteSetting`, `.Ring`,
  `.Coefficient`, and its existing coefficient instances (via the public comparison module).
- Sheaf.Paper.FiniteTorAmplitudeSites: recorded intrinsic/etale predicates and its
  public upstream `ProEtale.DerivedCategory.constructibleFiniteTor` specialization.
- Sheaf.Paper.DerivedPullbackTensorHom: the recorded finite intrinsic operations;
  its public import keeps the original constant-ring presentation available. The
  statement uses the fixed-ModuleCat presentation recorded in the repaired finite-Tor
  dependency and already used by the recorded co-smoothness dependency.
- Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients: the recorded `System`
  and its finite transported exceptional inverse image, with the same finite stage.
- Sheaf.Paper.CohomologicalSmoothnessFiniteComparison:
  `finiteComparedDualizing`, `finiteComparedTensorClause`,
  `finiteComparedBaseChangeClause`, and `finiteComparedCoefficientFinite`.
- WeilConjectures.Compactification.BaseChange: `Compactification.ofIsPullback` and
  `.baseChange`, with the source read for the full signature and geometric factors.
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange:
  `Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`, the specified
  proper-then-open exchange on D+; the unbounded canonical exchange and its mate
  are from its published canonical extension in UpperShriekCanonicalMaps.
- The unavailable StandingExceptionalBaseChange dependency is repaired below.
- WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps:
  `rightDerivedUpperShriekBaseChangeMap`, `dualizingComplexBaseChangeMap`, and
  `dualizingComplexTensorMap`; their entire definitions, signatures and docstrings
  were read. `leftDerivedUpperStarTensorIso` and
  `derivedSquareUpperStarIsoInvApp` are the canonical tensor/square comparisons.
  The symmetry identification is the canonical Koszul symmetry of this same
  tensor structure, as in the recorded co-smoothness tensor clause.

All recorded modules of stated proof dependencies are imported without public
visibility. This includes constructible origins and Tor comparison, exact inverse
image and constructible pullback, the stalk Tor test, pullback comparison, tensor
preservation, the specified exceptional Hom bijection, finite dimension,
compact-support base change, ringed exchange identification, open-extension
comparison, projection/exchange coherence, counit/projection transport, the finite
compact projection formula, and canonical ringed tensor pullback.

Edge cases checked before and during transcription: f or g identity (the canonical
unit/composition maps retain the identity square); the zero input and every Tor
interval; n=1 (no assumption on ramification divisibility); the empty source and
empty base change; nonseparated finite-type schemes; arbitrary nonseparated g;
and f not cohomologically smooth. All occur within the binders. The same small-site
object/Hom universes u+1/u are retained, with ModuleCat values in u+1.

Searches: the retained searches.jsonl records msearch.py leanfinder
"Canonical exceptional tensor map commutes with arbitrary Cartesian base change as
a counit mate of compact support exchange" (eight unrelated general adjunction/
module comparison hits), loogle `"dualizingComplexTensorMap"` (no Mathlib match),
and Mathlib CategoryTheory grep `dualizingComplexTensorMap|rightDerivedUpperShriekBaseChangeMap`
(no hits). Added LeanSearch "Exceptional inverse image tensor mate commutes with
arbitrary cartesian base change" returned ordinary module base-change/Cartesian
monoidal results, not this assertion. Direct rg searches of WeilConjectures and
Sheaf found the canonical component maps, the Prop-valued
`smoothTensorBaseChangeCoherence`, and a private literal-pullback calculation in
SmoothExceptionalBaseChange. These give useful canonical maps/calculation templates
but none states the node's full unconditional constructible preservation plus unit
normalization plus arbitrary Cartesian-square equality. No duplicate theorem is
introduced. The blueprint id search in WeilConjectures found no declaration.
The compact-object example module has been withdrawn in the present checkout;
its node now records the identical existing upstream notion. The delivered modules follow the
required module-mode header and explicit universe/variable conventions.

No mathematical statement correction or STATEMENT-DISPUTED flag is needed.

## Dependency modules

`pur9-cs-def-bc`: its Lean record explicitly says its module was deleted on
2026-10-20 because the node was then considered unreached. The file is absent
locally and scompile.py --source reports "Module source unavailable". Section 1(B)
authorizes a Lean-only repair, not a wait on a downstream coherence theorem.
`Sheaf.Paper.StandingExceptionalBaseChangeCompared` supplies the specified mate's
component in the canonical comparison coordinates already used by the co-smoothness
definition. Both compactifications are retained; the item passes c and its actual
base change, while the definition also allows an independently chosen primed
compactification as in the dependency node. Its data is comparison of the existing
`Etale.rightDerivedUpperShriekBaseChangeMap`; that existing map is precisely the
counit mate of the inverse specified proper/open exchange, including canonical
compactification comparisons. No arbitrary map or Nonempty choice is used.
Only the dependency's lean field changes. This replacement does not redefine
exceptional inverse image or impose an ambient pro-etale adjunction.

## Second reading by Q153

No independent local reader was started: the dispatched brief prohibits subagents
and requires direct delivery for the maintainer's independent review. The worker's
own rereading checked each binder and conjunct above against the node and both
modules. It caught the missing canonical braiding instance in the initial explicit
coefficient-first presentation. The final omega-first coordinates avoid repeatedly
elaborating that symmetry and match the recorded dependency's convention; the
equivalence of the equations is explained above and in the definition docstring.

## Validation

Both delivered modules compile cleanly using the prescribed scompile.py on the
current published library, separately and in dependency order. The final main
statement takes 8.1 seconds in the sandbox and 6.8 seconds under its library name.
Generic finite-ring helper definitions are specialized to the actual P.Coefficient
in the main theorem; this avoids repeatedly unfolding the coefficient quotient
inside the canonical tensor maps. Neither the statement nor its domain changes.
The source files have explicit universe u and autoImplicit false, no diagnostic
commands, no file-local instances or notation, and no line longer than 100
characters. Only the two lean fields differ from the shared DAG.

The deliver2.py dry run passes preflight and compiles both modules (dry-run commit
5c0d05fc0ab). The initial dry-run metadata failure was repaired: the signature
record starts at `def`, omitting its preceding `noncomputable` modifier.
