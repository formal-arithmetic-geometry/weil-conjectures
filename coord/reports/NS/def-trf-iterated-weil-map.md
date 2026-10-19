## Worker report

The delivery defines `WeilConjectures.TraceFormulaCoefficientConventions.iteratedWeilIsomorphism`
and `iteratedWeilSchemeFrobenius` in `Sheaf.Paper.IteratedWeilMap`.
The current source was read in full at
`literature/blueprint/main-20261015/blueprint/sec-trace-formula/sk-d-weil/def-trf-iterated-weil-map.md`
(order 2639). Its two displays agree with the node; the older node's cocycle sentence is
only a pointer to the separate cocycle lemma, and no cocycle theorem is asserted here.
No statement correction or new definition node is needed.

Clause-by-clause translation:

* The finite-field datum, coefficient prime distinct from the characteristic, fixed
  finite extension, positive coefficient level, separated finite-type model and its
  geometric base change are precisely the fields of
  `T : TraceFormulaCoefficientConventions.{u}`. No new hypotheses are imposed.
* `(K, phi) in D^b_ctf,W(X,A)` is `K : T.strictWeilComplex`, using the dependency's
  existing category of pairs. Its carrier is `K.obj.carrier`; its invertible structure
  is exactly `T.strictWeilFrobenius K`. Boundedness, constructibility and finite Tor
  amplitude are inherited from the existing carrier property, not redefined.
* Positive integer m is `(m : ℕ) (hm : 1 ≤ m)`. In particular m=1 is included.
* `Lg_gamma^{m*} K` is the object of the canonical `proEtaleConstantRingDerivedPullback` along the m-th power of
  `End.of (T.datum.geometricGaloisFrobenius T.X₀)`. These are powers of the actual
  scheme map, not powers of an abstract endofunctor substituted for those domains.
* `phi^[m]` is an `Iso` to `K.obj.carrier`. The recursion starts with the recorded
  structure isomorphism at exponent one. At the successor, `pow_succ` changes the
  domain to pullback along `g ≫ g^(n+1)`, the canonical pullback-composition map
  identifies it with `Lg^* L(g^(n+1))^* K`, and `mapIso` of the previous iterate
  followed by phi gives exactly phi o Lg^*phi o ... o L(g^(m-1))^*phi.
  `iteratedWeilIsomorphism` reindexes this positive recursion using m-1.
* `kappa^(m)` is exactly `(T.selectedSchemeGaloisComparison T.X₀ m hm).app
  K.obj.carrier`, from the dependency's landed module. Its source and target are
  the canonical constant-ring pullbacks at `T.coefficientRing`. The selected family
  carries the original theorem's factorization, normalization and multiplicativity
  clauses. The original phi is transported by the existing presentation comparison.
* `u_m = phi^[m] o kappa^(m)_K` is `iteratedWeilSchemeFrobenius`. In Lean composition
  order it is exactly the component of kappa followed by
  `iteratedWeilIsomorphism`. Its source is exactly canonical constant-ring pullback along
  `T.datum.schemeFrobeniusIterate T.X₀ m`, and its target is K. Both displayed maps
  are isomorphisms by construction.

Dependencies read and used:

* `Sheaf.Paper.TraceFormulaStrictWeilComplex`: `strictWeilComplex`,
  `strictWeilFrobeniusPullback`, `strictWeilFrobenius`, and the inherited conventions.
* `Sheaf.SixFunctors.SchemeFrobenius`: `geometricGaloisFrobenius` and
  `schemeFrobeniusIterate`, publicly imported by the recorded modules.
* `Sheaf.SixFunctors.SelectedSchemeGaloisComparison`: the recorded
  `FiniteFieldDatum.canonicalSchemeGaloisComparison` and its specialization
  `TraceFormulaCoefficientConventions.selectedSchemeGaloisComparison T T.X₀ m hm`.
  The public import retains `FiniteFieldDatum.schemeGaloisComparison` and its
  normalization and multiplicativity clauses. The coefficient annihilator is
  supplied by this existing specialization, without a new hypothesis.
* `Sheaf.Paper.IntegralFinitePullbackComposition`: the recorded composition
  dependency publicly exposes `proEtaleConstantRingPullbackComposition`, with its
  canonical termwise K-flat normalization; the recursion uses its inverse.
* `Sheaf.TraceFormula.PointTransportComposition`: the existing
  `WeilConjectures.pointPowerPullbackModel l E n f`. The helper
  `iteratedWeilPullbackModel` only specializes it to T's positive level after
  destructing the bundled level. It constructs no second comparison. The existing
  model uses the unit-normalized intrinsic and tensor pullback comparisons.

Edge cases checked before writing: m=1 gives phi and phi o kappa; m=2 gives
phi o Lg^*phi. On a point a Frobenius matrix M gives M^m. Zero complexes and empty
schemes need no nonzero or nonempty assumptions. The positive-level coefficient
convention is retained, including ramified extensions and levels not divisible by a
ramification index. No new relation between site object and morphism universes is
introduced. The recursion never needs a choice of a zero-exponent coefficient map.

Searches performed with the prescribed msearch wrapper and direct source reads:

* LeanFinder: `iterate a Weil structure isomorphism and compose with scheme Galois
  Frobenius pullback comparison`, and `canonical comparison between iterates of
  scheme Frobenius and geometric Galois Frobenius derived pullback`. Eight hits in
  each case concern ring Frobenius iterates, with no exact statement match.
* LeanSearch: `iterate Frobenius Weil isomorphism on derived sheaves`. Eight hits
  concern ring Frobenius iteration, no exact match.
* Loogle: `CategoryTheory.Functor.mapIso, CategoryTheory.Iso.trans`. Twelve hits
  concern existing generic isomorphism operations, which are reused.
* msearch grep: `coeffIterate|iteratedWeil|weilIterate|schemeGaloisComparison`, and
  `sfIntrinsicPullback|schemeGaloisCanonical|iteratedWeilIsomorphism` in CategoryTheory:
  no Mathlib match.
* Direct rg in Mathlib, upstream WeilConjectures, and lean/Sheaf found the existing
  upstream `ProEtale.TraceFormula.FrobeniusStructure.coeffIterate` in
  `SixFunctors/ProEtale/TraceFormula/Frobenius.lean` (full signature and recursion read).
  It uses the older fixed-scalar derived category and an arbitrary scheme Frobenius
  coefficient morphism, and supplies no scheme/Galois kappa. It does not state this
  node. `IsoAlgebra.strIterate` likewise iterates a functor, without the required
  scheme-power domains or kappa. Direct grep for this node id in upstream returned
  no matches. Direct name searches found no conflicting declarations.
* Direct searches for pullback presentation comparisons located the existing
  `pointPowerPullbackModel` in `Sheaf.TraceFormula.PointTransportComposition`,
  lines 165–180. Its full signature and body were read and are reused. Searches for
  `selectedSchemeGaloisComparison` found the dependency module and its existing
  consumer `Sheaf.SixFunctors.GraphFrobeniusOpenExchange`. Both use the same κ.

There is no STATEMENT-DISPUTED flag. This delivery adds no postponed theorem;
every definition has actual data.

## Returned-delivery repair

The saved packet was inspected and its prescribed initial dry run passed as
`f2ed814d1d`; that mechanical check did not remove the mathematical duplication
identified by the maintainer at immutable head `62c4288c8a89`.

H13/H4 repaired: removed `SchemeGaloisCanonicalComparison.lean` and the sandbox copy
of `prop-trf-scheme-galois-comparison.json`. Thus the landed Q16 dependency record
is left unchanged. `IteratedWeilMap.lean` imports
`Sheaf.SixFunctors.SelectedSchemeGaloisComparison` and uses exactly
`(T.selectedSchemeGaloisComparison T.X₀ m hm).app K.obj.carrier` followed by the
iterated Weil isomorphism. No new cancellation theorem or nested selection of tau
is supplied.

The minor duplication is also repaired: `iteratedWeilPullbackModel` now specializes
`pointPowerPullbackModel`, instead of rebuilding its two comparison factors. The
extra `def-weil-inverse-image-pullback-comparison` entry has been removed from the
sandbox item's stmt_deps, restoring the current base list. The actual dependency
records are not edited. No new nodes, dependency modules or statement corrections
are delivered. The main definition signature is unchanged and verbatim in lean.statement.

## Second reading by NS

The self-reading opened the current node, the current main-20261015 source, the
repaired module, the full landed selected comparison and the existing pullback
model. No other agent was started, as the dispatcher brief forbids it; the
maintainer supplies independent review. T still supplies precisely the finite-field,
coefficient and model hypotheses; K is the recorded strict Weil pair with carrier
`K.obj.carrier`; m and hm cover exactly positive exponents. The recursion uses powers
of the actual scheme map and the canonical composition, with
phi_[n+2] = phi composed with Lg*phi_[n+1]. At m=1 it gives the original structure
isomorphism in constant-ring coordinates. The second displayed map uses the very
same κ family as `GraphFrobeniusOpenExchange`, with source LΦ^{m*}K and target K.
The cocycle remains a forward pointer, rather than a theorem introduced here.
The two mismatches found were duplicate κ and duplicate presentation comparison;
both were replaced by the existing declarations. The bundled-level wrapper is
only specialization of the latter. The zero complex, empty scheme and m=1 cases
are still admitted. No hypotheses, conclusions, universes or statement text changed.

Validation: prescribed scompile.py compiled the repaired module without diagnostics,
30.6 s in the sandbox and 30.5 s at its library path. Its reused helper overlay
compiled cleanly in 4.2 s. The single-file 60 s limit was unchanged. The self-check
confirmed only the item's lean field differs from the current base, the primary
signature is verbatim, no Lean line exceeds 100 characters, and the reused helper
node has no dependency path back to this item.
