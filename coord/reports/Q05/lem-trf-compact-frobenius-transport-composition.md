## Worker report

States `WeilConjectures.compact_frobenius_transport_composition` in
`Sheaf.TraceFormula.CompactFrobeniusTransportComposition`. Its proof is `sorry`.
The five helpers give the powers and direct maps explicitly introduced in this node;
all data are constructions from existing declarations, with no new postponed helper theorem.
The natural statement, proof and proof dependencies are unchanged.

Hypothesis and clause correspondence:

- Global p, a, q, k₀, k: `D : FiniteFieldDatum.{u}`. Its fields record primality,
  positive a, q = p^a, the cardinality of k₀, and the fixed algebraic closure k.
- The prime l distinct from p and the fixed coefficient algebraic closure:
  `C : D.CoefficientDatum`, with `C.prime`, `C.different`, `C.Qbar` and its algebraic
  closure instance. No Weil structure or descent datum is stored here.
- The finite extension inside that fixed closure: `F : Padic.FiniteCoefficientFields
  C.l C.Qbar`. The coefficient type used in all maps is the existing
  `AlgebraicallyClosedCoefficients.Coefficient.{u} C.l C.Qbar F`, namely its canonical
  small field model through `Shrink.algEquiv`, retaining the original inclusion.
  Its valuation ring, chosen uniformizer and quotient ring are the dependency's
  `Padic.coefficientExtensionRing`. No independent coefficient ring is supplied.
- Positive finite coefficient level: `(n : ℕ)` indexes the source's exponent n+1.
  `Nat.succ_pos n` supplies positivity, so every exponent at least one occurs.
  In particular this is not a restriction to a fixed exponent or to a field coefficient.
- The separated finite-type k₀-scheme: `X₀ : Over (Spec (.of D.k₀))`, with
  `[LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]`.
  Locally finite type plus quasi-compact is the project's finite-type convention.
- X and its structure map: `(D.geometricFiber X₀).left` and `.hom`, exactly the
  recorded base-change object and projection.
- One fixed model compactification: `(c₀ : Compactification X₀.hom)`. Every helper
  uses `frobeniusCohomologyCompactification D X₀ c₀`, including its same middle model
  `zlCompactificationMiddle` and open map `zlCompactificationOpen`. There is no
  independent compactification indexed by r, m, M or coefficient level.
- g is `galois D X₀`, the same arrow as `D.geometricFrobenius X₀`. h is
  `pointFrobeniusAut D`, the existing `frobeniusPointIso D`. These are geometric,
  inverse-q-power Frobenii; no k-linearity is assumed for them.
- P_r is `compactPowerPullback ... n r`, the recorded `finiteDerivedPullback` along
  the r-th power in `End` of g. This is pullback along a scheme power, rather than
  a power of an arbitrarily chosen endofunctor. The point power is the recorded
  `((pointFrobeniusAut D)^r).hom`; `map_pow (Aut.toEnd _)` supplies its exact
  identification with the endomorphism power used by the geometric square theorem.
- H(M) = Fib_s(Ra_X! M) is `compactPowerCohomology ... c₀ n`, exactly
  `sfIntrinsicCompactSupport c A ⋙ (pointFiniteSections D.k A).mapDerivedCategory`.
  The source's fixed functor is represented using c as expressly permitted in the
  statement. The point functor is the underlying sections functor of the dependency's
  finite point fibre; equality of maps in its full subcategory is equality of these
  underlying maps. Its module carrier and derived universe are the recorded u+1 sizes.
- The direct exchange e_r is `compactPowerExchange ... c₀ n r`: the existing
  `FrobeniusExchange.finiteCompact` applied to g^r, g-bar^r, h^r. That declaration
  is the proper-image mate followed by proper image of the canonical open exchange.
  Its Cartesian open square and proper-square commutativity come from the recorded
  `frobenius_open_square`, whose last clause is the middle model's projection identity.
  Thus this is the specified exchange recipe, not an arbitrary transformation or
  an iteration of the degree-one exchange.
- iota^(r) is exactly `pointPowerTransportFinite ... r n`, from the landed
  point-transport-composition module: restriction, distinguished comma insertion,
  sheafification, tensor-unit comparison, and localization. Its sigma map is selected
  from an existence-and-uniqueness theorem fixing its value on every section.
- tau^(r) is `compactPowerTransport ... c₀ n r M`, defined as that iota followed
  by point sections of e_r. The two outer `openSquareDerivedPullbackModel` factors
  only move between the dependency's intrinsic and tensor pullback coordinates.
  At r=1 the recipes are those of `frobeniusCompactTransportFinite`: `pow_one`
  identifies the arrows; the uniquely section-normalized point map and the
  canonical exchange specify the same maps. No one-step map is substituted for
  a direct higher-power recipe.
- M in D^b_c(X,A): the main theorem binds M in the exact existing
  `intrinsicFiniteTorsionConstructible ... .FullSubcategory`. The explicit helpers
  extend to the ambient derived category, so their use at P_m M requires no extra
  preservation hypothesis. The recorded isomorphism-pullback theorem supplies
  bounded constructibility mathematically; no finite-Tor condition is imposed.
- m at least one: `(m : ℕ) (hm : 1 ≤ m)`.
- c_m is `(compactPowerPullbackStep ... n m).inv.app M.obj`. The step starts with
  `pow_succ` and the inverse of the normalized canonical pullback compositor
  `integralFiniteCanonicalPullbackComposition`, expressed in intrinsic coordinates
  by the fixed unit-normalized `openSquareDerivedPullbackModel`. Its inverse has
  exactly source P_1(P_m M) and target P_(m+1) M.
- The final displayed equality is written with Lean's left-to-right `≫`:
  direct tau_(m+1) equals tau_m, then tau_1 at P_m M, then H applied to that inverse
  comparison. This renders the source's right-to-left composition without reversing
  any arrow. No morphism P_1 M → M, no Weil structure and no invertibility of tau
  is a hypothesis.

Dependency declarations read and reused (including their full relevant signatures and
construction/proof docstrings):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`,
  `.CoefficientDatum`, `.geometricFiber`.
- `Sheaf.Paper.TraceFormulaCoefficientConventions`:
  `WeilConjectures.TraceFormulaCoefficientConventions`, `.coefficientField`,
  `.coefficientRing`, `.boundedConstructible`, `.derivedPullback`, `.pointFibre`,
  `.compactSupportComplex`. The theorem unbundles these same choices so that the
  positive coefficient level is uniformly represented by n+1.
- `Sheaf.SixFunctors.SchemeFrobenius`:
  `WeilConjectures.FiniteFieldDatum.geometricGaloisFrobenius`; this is the same
  geometric arrow used by `FrobeniusExchange.galois`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `WeilConjectures.finiteDerivedPullback`.
- `Sheaf.SixFunctors.FrobeniusPointTransport`: `frobeniusPointIso`,
  `frobeniusPointTransportFinite`, with the normalized finite sigma construction.
- `Sheaf.Paper.FrobeniusGeometricExchange`: `FrobeniusExchange.galois` and its
  reexported `finiteCompact` from `Sheaf.Paper.SystemOperationExchangeRealization`.
- `Sheaf.SixFunctors.FrobeniusCohomologyTransport`:
  `frobeniusCohomologyModelMap`, `frobeniusCohomologyCompactification`,
  `frobeniusCompactTransportFinite`.
- `Sheaf.Paper.IntegralFinitePullbackComposition`:
  `integralTowerGeneralPullbackComposition` and the actual normalized constant-ring
  specialization `integralFiniteCanonicalPullbackComposition`.
- `WeilConjectures.Compactification.Refinement`:
  `AlgebraicGeometry.Compactification.Refinement` and the existing compactification type.
- Added landed statement dependency `lem-trf-point-transport-composition`, module
  `Sheaf.TraceFormula.PointTransportComposition`: `pointFrobeniusAut`,
  `pointPowerTransportFinite`, `point_transport_composition`. The first two are used
  in the direct helper recipe and the theorem is Step 3 of the proof plan.
- Added landed statement dependency `lem-trf-frobenius-open-square`, module
  `Sheaf.AlgebraicGeometry.FrobeniusOpenSquare`:
  `WeilConjectures.FiniteFieldDatum.frobenius_open_square`, the exact power-square
  and semilinearity interface used to construct e_r. These two additions reuse
  existing nodes; no node or declaration is newly duplicated.
- Proof imports include `Sheaf.SixFunctors.FrobeniusSquareCartesian`,
  `Sheaf.Paper.IsomorphismDerivedPullback`, `Sheaf.Paper.CondensedAmbientExchange`,
  `Sheaf.Paper.PullbackCoefficientIterateCoherence`,
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`,
  `Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange`,
  `Sheaf.SixFunctors.FrobeniusPointTransportNatural`, and
  `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates`. Their relevant recorded
  declarations are respectively `frobenius_square_cartesian`,
  `isomorphismFiniteDerivedPullback_termwise`, the ambient exchange reexports,
  `trf_pullback_coefficient_iterate_coherence`, `proEtaleConstantRingDerivedPullback`,
  `constantOpenSquareExchange` (including its underlying exchange datum's pasting),
  `frobeniusPointTransport_natural`, and `mateEquiv_whiskerTop_whiskerBottom`.
  Mathlib's `mateEquiv_vcomp`, `mateEquiv_hcomp`, and the conjugation compatibility
  signatures were also read. The theorem docstring retains all seven DAG proof steps,
  including the specified comparison conjugation for an alternative representative.

Sources: opened the current blueprint's
`sec-trace-formula/sk-d-weil/lem-trf-frobenius-operator-compact-description.proof.md`
and extracted/read Deligne Weil II printed pp. 151--153 from the local PDF
(PDF pages 16--18). These distinguish transport of scheme/sheaf pairs from a Weil
structure and specify the induced compact-support action. The derived finite-level
coherence is the auxiliary statement in the DAG, not a claim that Deligne prints
this derived equation verbatim.

Edge cases checked before drafting:

- n=0 means coefficient exponent one, which is included; exponent zero is absent
  as required by the source. No assumption makes A a field for higher exponents.
- m=1 compares direct power two with two one-step transports, with the comparator
  ending at P_2 M. The formula is not silently normalized by setting c_m to identity.
- Helpers are also defined at r=0, using genuine identity powers; the main theorem
  asserts only the required positive composition cases.
- Empty X₀, zero M, and disconnected/reducible models satisfy the same type-level
  hypotheses. There is no nonempty, smooth, proper-X₀ or finite-Tor assumption.
- The semilinear maps are scheme maps, not required to be k-morphisms. The same
  middle scheme and compactification are retained even if they are not smooth.
- Every universe and variable is explicit, with both auto-implicit options disabled.
  The coefficient field's small model and the point target use the dependencies'
  existing size transports; no extra universe-equality hypothesis was added.

Searches for an existing statement (all msearch calls used group Q05 and this item):

- `leanfinder`: "Compact support transport along powers of geometric Frobenius is
  compatible with composition". Eight hits, headed by `iterateFrobeniusEquiv_add`
  and `_symm_add`; these are ring automorphism identities, not compact cohomology.
- `loogle`: `"frobenius", "comp"`. Twelve hits including identities for
  `frobeniusEquiv` and categorical Frobenius morphisms; none has this statement.
- `grep`: `compact.*[Tt]ransport|[Tt]ransport.*[Cc]omp`. Fifteen Mathlib hits concern
  order-isomorphism transport and unrelated compositions; no matching theorem.
- `leansearch`: "Compact support Frobenius transport composition along powers of
  a scheme automorphism". Eight hits including `iterateFrobenius_eq_pow`,
  `iterateFrobenius_add`, `HasCompactSupport.comp_homeomorph`; no derived theorem.
- `rg` in the upstream `WeilConjectures` and shared `lean/Sheaf`, first with
  `compact.*[Tt]ransport|[Tt]ransport.*[Cc]omp` and then exact new names and
  `frobenius.*transport.*composition`: the broad query finds existing one-step
  transports and unrelated transport prose; the narrow query finds only an
  unrelated docstring. Exact item-id search in both source roots found no declaration.
- The source-name index `dag/lean_names_upstream.json` was also searched with the
  transport patterns; no exact compact-support power-composition declaration.
  The existing point-power construction was found and reused, rather than restated.

No statement correction, disputed statement, new node or dependency-record repair.
Initial compile diagnostics were repaired with the standard `Aut.toEnd` map_pow
comparison and the recorded point derived-category instance; neither changes the
mathematical statement. Validation uses only the prescribed scompile.py wrapper.

## Second reading by Q05

The dispatcher expressly starts one worker and prohibits other agents. This section
records this worker's separate self-check; the maintainer performs the independent
review, as the dispatcher brief specifies. It is not claimed to be an independent reading.

Reopened the node and completed module and checked all binders and clauses above.
The initial generic helper coefficient E did not explicitly retain the fixed algebraic
closure in the theorem signature; the final theorem instead uses `C` and its finite
intermediate field `F`. Confirmed c₀ occurs unchanged in every power map, the point
power map is the landed restriction-insertion recipe, e_r is the direct proper/open
exchange, and the inverse comparator has source P_1 P_m and target P_(m+1).
Confirmed only M's bounded constructibility and m≥1 are assumed. The ambient
helpers do not add a finite-Tor requirement or an arbitrary comparison map. The sole
sorry is the owning node's theorem, whose docstring includes the complete proof route.

The final self-check also made D, X₀ and all three scheme-property hypotheses
explicit in the theorem binder itself. This retains separation even though the
chosen-compactification helper constructions do not require that global variable.

## Returned-delivery repair validation (2026-10-18)

Resumed the retained packet rather than restarting the statement construction. The
return on immutable head c5727a1abb46 reported a 60-second timeout while compiling
the dependency `Sheaf.Paper.DerivedPullbackTensorHom`. The prescribed first dry run
now passes against the current published overlay: `OK (dry run): commit d58f9f4259
passes the preflight and compiles; nothing pushed`. No Lean or mathematical
statement change was required to resolve that returned compilation failure.

Reopened the complete module, the current node and this report for the required
self-check. Confirmed that the fixed model compactification is shared by all
powers; the direct point transport and compactification exchange define each
power independently; and the final map is H of the inverse of the canonical
composite-to-iterated pullback comparison. The theorem still quantifies over
every positive finite coefficient level, every bounded constructible M and
every m at least one, without a Weil structure. Checked verbatim agreement of
the recorded signature, the single owned theorem sorry, explicit implicit-variable
options and 100-character line width. Against the current shared node, only lean
and the two already-landed statement dependencies differ; the natural statement,
proof and all other fields are unchanged. Retained the saved Lean module intact.
