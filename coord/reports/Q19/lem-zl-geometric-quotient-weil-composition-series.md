## Worker report

The module `Sheaf.Paper.GeometricQuotientWeilCompositionSeries` states
`RealSheaves.geometricQuotientWeilCompositionSeries`, with its only proof postponed
by `sorry`. Its small helper abbreviations specialize the recorded classical etale
adic objects, maps and representations, and its instances project existing curve
hypotheses or apply existing geometric-base-change structures. They introduce no
new mathematical construction or choice.

Hypotheses and clauses, read against the unchanged item statement:

* Finite fields, q, prime different from the characteristic, algebraic coefficient
  closure and embedding: `S : RealSheaves.Setup`. This retains all fields of
  `d-real-setup`. The standard classical etale coefficient interface uses
  `Setup.{u,u+1}` with `Scheme.{u}` and stalk modules in universe `u+1`, exactly
  the recorded `EtaleLisseWeilSheaf` interface.
* Smooth geometrically connected separated finite-type nonempty curve of pure
  dimension one: `[hC : Fact (S.IsCurve C₀)]`, together with its structure map
  `[C₀.Over (Spec (.of S.k₀))]`. No additional geometric regularity is assumed.
  Noetherianity, geometric separatedness and prime invertibility are derived
  from these hypotheses using the existing finite-field base-change interfaces.
* Geometric curve: `S.geometricCurve C₀`. Geometric Galois Frobenius is the
  inverse-q-power `S.weilFrobenius C₀ hC.out`, on this very chosen base change.
* Geometric generic point: the algebraically closed field κ, its morphism `t`,
  and `hgeneric : IsGenericPoint (t (IsLocalRing.closedPoint κ)) Set.univ`.
* Weil group and its fundamental action: `d : Monodromy.DegreeDatum W` and
  `D : EtaleWeilDegreeData ... t W d` are precisely the recorded presentation
  interface: an identification of the geometric fundamental group with the
  degree kernel and a Frobenius path satisfying the conjugation law.
  `curveQuotientWeilRep` is just `Scheme.etaleFundamentalRep` for these data,
  never an independently assumed action. The degree extension is the Weil group
  presentation of the recorded interface.
* Classical lisse Weil sheaf: each value of `J` lies in
  `curveQuotientWeilSheaf`, an abbreviation for `EtaleLisseWeilSheaf`, the
  `IsoAlgebra` of the actual etale adic Frobenius pullback. The ambient H is
  `J.obj (Fin.last r)`; naming H by the final term loses no given filtration.
* Given finite filtration: `r : ℕ`, the ordered diagram
  `J : Fin (r+1) ⥤ curveQuotientWeilSheaf S C₀`, `hzero`, and `hmono`.
  Functoriality supplies all compatible composites to the final term, and
  `hmono` makes the adjacent arrows subsheaf inclusions.
* Prescribed quotients: `T : Fin r → ...`, the actual sheaf arrows
  `q j : J.obj j.succ ⟶ T j`, and `hexact`. The latter renders their short
  exact sequences by injectivity, `Function.Exact`, and surjectivity on every
  geometric adic stalk, the conservative exact fibre criterion for these
  classical lisse sheaves. It assumes no representation quotient comparison.
* Each quotient nonzero: `hnonzero j : ¬ IsZero (T j)`.
* Geometric irreducibility: `hirr` says every subrepresentation of the actual
  `Scheme.etaleGeometricRep ... (T j).carrier t` is bottom or top.
  The nonzero condition is supplied separately by `hnonzero`, as in the node.
* Finite dimension of V: the first conclusion is `FiniteDimensional` of the
  actual stalk of the final term, rather than an added hypothesis.
* The given filtration gives a composition series: `s` uses the dependency's
  `Representation.CompositionSeries` and `hlen : s.length = r` retains the
  original length. Each `e i` identifies the original term's stalk with the
  stable subspace `s.series i`. The first equation identifies its ambient
  inclusion with the actual stalk map of `J.map (homOfLE (Fin.le_last ...))`.
  Thus this is exactly the given chain, not some separately chosen series.
* Canonical successive quotient identifications with the prescribed action:
  `a : (s.factor j).Equiv (curveQuotientWeilRep ... (T ...))` is an equivariant
  linear isomorphism. Its defining equation is
  `a (Submodule.Quotient.mk (e j.succ v)) = curveQuotientStalkMap ... (q ...) v`.
  This pins it to `[v] ↦ q_j(v)` and therefore fixes the canonical map.
* Each quotient is irreducible and a constituent: the last pair of conclusions
  uses `Representation.IsIrreducible` and `Representation.IsConstituent`
  for the actual prescribed Weil representation. The factor is the canonical
  `Representation.CompositionSeries.factor`, with repetitions retained.
* `r=0` is allowed: `Fin r` is empty, `J` has one zero final term, `s` has length
  zero, and all quotient conditions are vacuous. No semisimplicity or splitting
  binder occurs anywhere.

Dependency declarations read and used:

* `Sheaf.Paper.RealSheavesSetup`: `RealSheaves.Setup`, `Setup.IsCurve`,
  `Setup.geometricCurve`, characteristic/prime fields.
* `Sheaf.Paper.RealWeilSheaves`: `Setup.weilFieldDatum`, `Setup.weilFrobenius`.
* `Sheaf.Paper.LisseIntegralSmallCoefficients`: publicly reexports the original
  `Sheaf.Paper.LisseAdicSheaves` integral, rational and algebraic lisse category
  and its actual fibre; that algebraic category is used by the recorded
  `EtaleLisseWeilSheaf` interface. No small-coefficient integral surrogate is
  substituted for it.
* `Sheaf.Paper.EtaleWeilFundamentalRepresentation`: `EtaleLisseWeilSheaf`,
  `EtaleWeilDegreeData`, `etaleGeometricRep`, `etaleFundamentalRep`,
  `etaleAlgebraicFiberMap`. Full signatures and normalization docstrings read.
* `WeilConjectures.RepresentationTheory.CompositionSeries`:
  `Representation.CompositionSeries`, `.length`, `.factor`.
* `WeilConjectures.EtaleCohomology.Purity.RealSheaves.LinearAlgebra`: the
  operations docstring explicitly identifies `Representation.IsConstituent`
  and `Representation.IsIrreducible` as the ordinary shared operations.
  Their definitions are read in
  `WeilConjectures.Mathlib.RepresentationTheory.Irreducible` and Mathlib.
* `Sheaf.Paper.EtaleWeilSheafEquivalence` is a proof import of the recorded
  `prop-wf-weil-sheaf-representation-equivalence`, with actual stalk normalization
  and finite-limit/colimit preservation in both directions.
* Existing base-change helpers are `WeilConjectures.zlClassicalNoetherian`,
  `zlClassicalSeparated` from `Sheaf.Paper.NormalizedClassicalWeilRealization`,
  and `sfWeilPrimeInvertible` from its public imports. Their proofs/data are
  reused, not restated as postponed helper theorems.

Edge checks: empty quotient index set (`r=0`), the zero sheaf, a rank-one sheaf,
a nonsplit unipotent rank-two extension with rank-one factors, and a quotient
with an invariant proper subspace. In the last case `hirr` fails, as required.
A filtration with a repeated nonzero term has zero successive quotient and
fails `hnonzero`; it cannot falsely yield a strict composition series.
Neither arithmetic irreducibility nor finite dimension is assumed as a shortcut.

Source checked: `literature/blueprint/latest/blueprint/sec-deligne-laumon-general/
sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md`, paragraph 2, and the
item's complete three-step expanded proof. There is no statement correction or
disputed mathematical assertion.

Searches (the prescribed msearch wrapper logs the service results):

* LeanFinder: “An exact fibre functor sends a filtration of lisse Weil sheaves
  with geometrically irreducible quotients to a composition series”: generic
  Jordan–Holder `CompositionSeries` and finite-length facts, no exact match.
* Loogle: `Representation.CompositionSeries`: no Mathlib identifier (it is the
  existing project declaration, which is reused).
* LeanSearch: “geometrically irreducible quotients of lisse Weil sheaf filtration
  give composition series”: generic composition-series and finite-length hits,
  none stating this sheaf filtration and its canonical quotient maps.
* msearch grep: `CompositionSeries|geometric.*irreducible`, Mathlib
  `RepresentationTheory`: no hits for the full assertion.
* `rg` of Mathlib/RepresentationTheory, the live `lean/WeilConjectures` and
  `lean/Sheaf`: found the shared representation series and constituent notions,
  exact etale realization, and the caller
  `Sheaf/DeligneLaumon/TwoPointCurveConstituentPurity.lean`; no declaration of
  this full assertion. Searching the exact item ID upstream found no declaration.
* Filtration searches found `ZlClassicalFiltration` in
  `ClassicalWeilFiltrationHeartTransport`, whose all-geometric-fibre exactness
  convention agrees with the explicit binders here. No new filtration notion is
  defined in this delivery.

## Second reading by Q19

I reread the complete node and the completed module clause by clause. The
fundamental action is the repaired classical etale action, not the similarly
named upstream pro-etale action. The series is attached to the given inclusions
through the ambient-stalk equation. The factor isomorphism is attached to the
given q_j through its quotient-generator equation, rather than only a bare
existence of an isomorphism. Both endpoints and the zero-length case are present.
No statement correction, dependency repair or new node was needed. This is a
self-rereading: the dispatcher's explicit prohibition on starting other agents
supersedes the standing independent second-worker instruction. The maintainer's
independent review remains the delivery review.
