## Worker report

The delivery defines the compact-support transport and its scheme-Frobenius form in
`Sheaf.Paper.PurityCompactSupportTransport`. All data are explicit composites. There are
no new axioms, postponed theorems or sorry terms. The node's mathematical statement and
statement dependencies are unchanged.

Clause and hypothesis correspondence:

- The global finite-field datum, distinct coefficient prime, finite coefficient extension
  and positive quotient level are `P : PurityFiniteSetting`, with `P.field`,
  `P.coefficients`, `P.extension`, `P.level`, `P.level_pos` and `P.Ring`. No extra choice
  of coefficient quotient or algebraic closure is made.
- The finite-type models are `X₀ Y₀ : Over (Spec (CommRingCat.of P.field.k₀))`, with
  `LocallyOfFiniteType` and `QuasiCompact` on their structure morphisms. The separated
  finite-type morphism is `f₀`, with `LocallyOfFiniteType f₀.left`,
  `QuasiCompact f₀.left` and `IsSeparated f₀.left`. Its geometric base change is
  `P.frobeniusMap f₀`, and relative smooth dimension is
  `SmoothOfRelativeDimension d (P.frobeniusMap f₀)` for `d : ℕ`.
- The schemes are exactly `(P.frobeniusFiber X₀).left` and the analogous Y. The
  horizontal arrows are the dependency's actual `P.frobeniusGaloisMap X₀` and Y version;
  these use geometric, not arithmetic, Frobenius.
- The chosen compactification and its base change are `c c'`, `gbar`, `properSquare`
  and `openSquare`. The latter two impose the two Cartesian squares of the proper/open
  factorization with the specified geometric horizontal arrows. They are presentation
  data for the chosen base change, not an additional condition on f. Their pasting
  gives precisely the first Frobenius square; no Cartesian condition on the
  scheme-Frobenius square is used.
- `M : finiteTorConstructibleCategory P.coefficients.l P.extension P.level P.level_pos
  (P.frobeniusFiber X₀).left` is exactly the finite-stage `Dᵇ_ctf` object. Its strict
  datum is the specified isomorphism `φM : Lg_X^* M.obj ≅ M.obj`. This is the
  strict-isomorphism notion used by def-pur-tate-datum, expressed in the intrinsic
  finite coefficient presentation in which this node's ambient formula is written.
- `finiteCompactSupportTransportExchange` applies the recorded
  `proEtaleAmbientRingedExchange` for `properSquare` to `j_! M`. Its second factor is
  proper direct image of `constantOpenSquareExchange ... openSquare`, the canonical
  open base-change comparison in the intrinsic constant-ring presentation. The
  coefficient compatibility proof rewrites both routes by
  `proEtaleConstantRingCompositeCoefficients_eq` and applies `congr_arg_heq` to the
  square's commutativity. There is no arbitrary exchange transformation input.
- `finiteCompactSupportWeilTransport` follows this exchange by the supplied chosen-
  compactification comparison and by `Rf_!` applied to `φM.hom`. Thus both endpoints
  use the same specified compact-support functor, even if c' differs from c. The
  comparison is explicit data, as required by the node and def-exchange-projection;
  compactification independence is not asserted.
- For higher coefficients the node explicitly works relative to supplied operations
  on closed full domains. `compactSupportWeilTransport` takes exactly the recorded
  `SuppliedExchangeProjection.ExchangeProjectionStage`, with X'=X and Y'=Y. It uses
  its constructed `s.compactExchange`, the supplied compactification identification,
  then `s.compactSupport.map φM.hom`. The categories here are the supplied coefficient
  domains, so this definition can be instantiated at each of the three higher stages;
  it asserts neither existence of domains nor preservation outside them.
- The integral specialization `completedCompactSupportWeilTransport` uses
  `completedCompactSupportExchange` itself for its first arrow. Its `d`, generating
  tuple `a` with `ha`, intrinsic completeness of `M`, and proper/open squares are
  precisely the interface of that recorded dependency. For this node d is the
  supplied integral coefficient datum. The formula uses `d.completedPull`, rather
  than ordinary inverse image for discrete non-torsion constants. It then applies
  the chosen compactification comparison and the proper/open composite to `φM.hom`.
  The helper is defined on every complete object where the formula makes sense;
  restriction to the supplied bounded constructible finite-Tor domain changes no map.
- `compactSupportWeilTransportRepresentative` constructs, rather than accepts as an
  unconstrained map, the supplied-stage transport and passes it through the recorded
  `exchangeProjectionCoefficientRepresentative`. With the supplied integral-to-
  rational localization it is the rationalized map; with the supplied common finite
  field inclusion it is the common-stage morphism class. The comparison/cocycle and
  identity normalizations are those of def-exchange-projection; no reduction from
  rational to finite coefficients is introduced.
- `finiteSchemeFrobeniusForm` is `P.schemeGeometricFrobeniusComparison T₀` evaluated
  at N, followed by `φN`. It permits every N on the actual geometric fibre, in
  particular M and the chosen Rf_! M; it does not require the transported map to be
  certified invertible. `schemeFrobeniusForm` is the same ordered composite for
  the supplied completed/rational/common-stage realization of kappa. It has no
  compact-support assumption, as the final clause applies to every object with a datum.

Dependency declarations inspected and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting` and its Ring.
- `Sheaf.SixFunctors.SchemeGeometricFrobenius`:
  `PurityFiniteSetting.frobeniusFiber`, `.frobeniusMap`, `.frobeniusGaloisMap`,
  `.frobeniusSchemeMap`, `.schemeGeometricFrobeniusComparison`, and the square signature.
- `Sheaf.Paper.PurityTateDatum`: strict-isomorphism convention, its finite intrinsic
  presentation and `CondensedStrictWeilDatum` coefficient-stage signature. This module
  also exposes the recorded `finiteTorConstructibleCategory` from FiniteTorAmplitude.
  No second strict-datum structure is declared here.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`, its
  `.compactExchange`, and `exchangeProjectionCoefficientRepresentative`.
- `Sheaf.Paper.CondensedAmbientExchange`: the general ring-sheaf
  `AlgebraicGeometry.Scheme.proEtaleAmbientRingedExchange` publicly reexported there;
  its condensed analogue was also inspected. The finite factor uses the general
  ring-sheaf version with the actual constant coefficient sheaves.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange`:
  `AlgebraicGeometry.ProEtale.ordinaryOpenExtensionBaseChangeIso` was read in full.
  In intrinsic constant-module coordinates the corresponding existing normalized
  map is `AlgebraicGeometry.Scheme.constantOpenSquareExchange`, exposed through
  PurityTateDatum. It is not replaced by a supplied arbitrary isomorphism.
- `Sheaf.Paper.CompletedCompactSupportExchange`:
  `AlgebraicGeometry.Scheme.completedCompactSupportExchange`, including its strict-
  tower normalization and the completed open factor.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison`:
  `proEtaleConstantRingCompositeCoefficients_eq`, the coefficient compatibility used
  to supply the ambient mate's proof input.

Edge cases checked: the zero complex and empty schemes require no new nonemptiness
hypothesis; n=1 and d=0 are allowed; no division by d occurs. No separatedness of
X₀ or Y₀ over the field is imposed by the finite definition. The input datum must be
an isomorphism, but the output is a morphism, as displayed in the node; no invertibility
assertion has been smuggled into the definition. Arbitrary canonically identified
base-changed compactifications are retained. The scheme-Frobenius comparison points
from LPhi* to Lg_gamma*, hence the final composition has the correct orientation.
The small sites retain object universe u+1 and morphism universe u, and every universe
and variable is explicitly bound (`autoImplicit false`).

Searches performed:

- msearch LeanFinder: "Transport a strict geometric Weil datum along compact support
  direct image using the canonical exchange and convert to scheme Frobenius by kappa".
  Eight hits concerning Witt vector isocrystals; none matches.
- msearch Loogle: "CategoryTheory.Functor.mapIso, CategoryTheory.Iso.trans".
  Twelve generic functor/isomorphism hits, including mapIso_trans; no full match.
- msearch grep: "WeilDatum|compactSupport.*Frobenius|Frobenius.*compactSupport" in
  Mathlib AlgebraicGeometry: zero hits.
- msearch LeanSearch: transport of a Weil datum along compact support direct image
  by exchange and composition with the scheme-Frobenius comparison: eight hits
  on Witt vector Frobenius and a Weierstrass variable change; no exact match.
- rg of WeilConjectures and Sheaf for lowerShriekWeilDatum, compactSupportWeilTransport,
  compact-support/Frobenius transport terms and this node id. Read the upstream
  EtaleCohomology/Purity/Smooth/WeilEquivariance compactSupportWeilTransport and the
  pro-etale FiniteCoefficient/Derived/CompactWeilDatum lowerShriekWeilDatum.
  They supply respectively an etale finite-coefficient construction and a pro-etale
  construction with a Frobenius-compatible fixed compactification. Neither gives
  the full supplied-domain completed/rational/common-stage definition and the actual
  scheme-Frobenius convention of this node. Existing exchange and comparison data
  are reused; no module can be attached as an exact existing match.
- rg of dag/lean_names_upstream.json, Mathlib and both project roots checked the
  new full declaration names; no collision in WeilConjectures.Purity was found.

No statement dispute, correction, new node or dependency-record repair is needed.

Validation: scompile.py compiled the final module cleanly (sandbox 9.8 seconds,
canonical module path 7.4 seconds). No warnings, including no sorry warnings.
The initial coefficient compatibility elimination was replaced with the existing
Mathlib dependent congruence lemma; no new theorem was required.

## Second reading by NH

A second pass by this dispatcher worker reread the node, the current blueprint and
all seven declarations in the delivery; no separate agent was started, as the brief
forbids that. Independent review is the maintainer's delivery review.

The finite definition binds every geometric hypothesis and the actual finite-Tor object.
The exchange's proper factor is the ambient ringed mate, and its open factor is canonical
base change. The extra written factor before Rf_!(phi) is the explicitly supplied
compactification comparison, required because the source and base-changed presentations
need not be definitionally equal. The integral helper uses completed pullback in both
positions. The abstract higher-stage function uses the dependency's supplied closed-domain
record; it does not claim the datum exists for arbitrary unrestricted categories.
The field helper now constructs the canonical supplied-stage transport internally before
applying the coefficient inclusion; an initial draft's unconstrained component parameter
was removed. The last formula is kappa followed by phi, for any N, and covers the
transported image as well as M. No change to the node statement was made.
