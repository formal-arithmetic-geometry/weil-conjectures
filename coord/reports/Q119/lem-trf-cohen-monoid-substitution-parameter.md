## Worker report

The module `Sheaf.RingTheory.CohenMonoidSubstitutionParameter` states
`CohenMonoidSubstitution.cohen_monoid_substitution_parameter`. Its sole postponed
proof is `by sorry`. The nine helpers are explicit abbreviations or canonical
maps/ideals belonging to this statement; none contains postponed data or proofs.
The accepted Q48 stage-1 split is preserved. The inherited unchanged-node refusal
was a stage-1 issue: the current queue assigns stage 2 and the base has no `lean`.
There was no retained Lean module or report in this sandbox on resumption, and no
repair note was present for the item.

Clause-by-clause rendering:

- The Cohen ring with uniformizer the prime integer `p` is `hV : IsCohenRing p V`.
  This predicate includes primality, domain, DVR, the maximal-ideal equality and
  completeness. No extra local, domain or Noetherian hypothesis on `V` is added.
  The field `k=V/pV` is not independent data in the conclusion: its quotient occurs
  in the proof, and reduction modulo `p` is the quotient by `Ideal.span {p}`.
- A finite free abelian group is `K` with `AddCommGroup`, `Module.Free ℤ K` and
  `Module.Finite ℤ K`. The trivial group is allowed. `S` and `T` are additive
  commutative monoids with the recorded `IsFineSaturatedMonoid (Multiplicative _)`
  predicate. `hsharpS` and `hsharpT` say every invertible element is zero.
- The homomorphism is `f : S →+ K × T`. Its coordinates are `(f s).1` and
  `(f s).2`; `hβ` is precisely nonvanishing of the second coordinate on `s ≠ 0`.
- `n : ℕ` indexes the old variables by `Fin n`; it is explicitly declared in the
  variable context, along with `V`, `K`, their structures and all universes.
  `set_option autoImplicit false` forbids accidental auto-bound names.
- `E` is the existing `ToricMonoid.PolynomialRing V K n`, literally the
  `MvPolynomial` ring over `AddMonoidAlgebra`. `P` is prime; `hp` and `ht` say
  that it contains `p` and each old variable. `Local P` is `Localization.AtPrime P`,
  and `Complete P` is its completion at its actual maximal ideal.
- `I` with `hI` names exactly `(p,[s] : s ≠ 0,t)` in `V[S][t]`. Thus the source
  is precisely `AdicCompletion I (ToricMonoid.PolynomialRing V S n)`, with no
  additional ideal choice. The existing `ToricMonoid.chartIdeal` gives `([s],t)`.
- Localness of `D` is an existential conclusion. Then `J` with its displayed
  equality names exactly `(m_D,[v] : v ≠ 0)`; the target completion is `D[[T]]`.
  Quantifying over an ideal equal to this formula only names the specified ideal.
- The existential `ψ` is a ring homomorphism and is continuous for the explicit
  inverse-limit topologies. Its formula on `C(single s c)` is exactly
  `c[δ(s)][β(s)]`, with `coefficientMap` and `latticeMonomial` using the canonical
  map `E → E_* → D`. Its formula on `X i` sends it to `oldParameter P i` in `D`.
  Taking `s=0` in the first formula gives the prescribed coefficient extension.
- The existential augmentation `ε` is continuous and sends every completed
  monomial `single t d` to `d` when `t=0` and to zero otherwise. This specifies
  the coefficient identity and kills all nonzero `T`-monomials.
- The universal `θ` and its hypothesis are exactly `θ-p ∈ ([s] : s ≠ 0,t)H_S`,
  using the map of the existing chart ideal under the completion map.
  `ψ θ` is `η`, and `ε (ψ θ)` is `bar η`; separate aliases are unnecessary.
- `ε (ψ θ) - p ∈ completeParameters P` is the congruence modulo `(t)D`.
  The following two clauses are membership in `m_D` and nonmembership in `m_D²`.
- `Stratum P` is literally `E_* /(t)`, with `localParameters` obtained by mapping
  the variables' ideal under localization. Its regular-local structure is a
  conclusion, followed by regularity of `Stratum P /(p)`, nonzeroness of `p`,
  membership in the maximal ideal and nonmembership in its square.
- `e` is `D/(t)D ≃+* completion(E')`. The equation on every `a : E_*` identifies
  it with the canonical quotient-completion comparison, rather than an unrelated
  ring isomorphism. Localness of `completion(E')` is also a conclusion. The next
  two clauses retain the nonzero cotangent class of `p` there, as membership in
  its maximal ideal but not its square.
- The final two clauses say the image of `bar η` in `D/(t)D` is literally `p`,
  and its image through `e` is `p` in `completion(E')`. Together with the preceding
  square-nonmembership clause they express the retained nonzero cotangent class.

Dependency declarations read and reused:

- `WeilConjectures.RingTheory.CohenRing`: `IsCohenRing`, including its full DVR and
  completeness definition (def-weil-pbc-cohen-ring).
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup` and its public source
  `Sheaf.AlgebraicGeometry.LogRegularPair`: `AlgebraicGeometry.IsFineSaturatedMonoid`.
  Only the fs monoid clause of def-trf-fs-log-blowup is used, not a log scheme.
- `Mathlib.RingTheory.AdicCompletion.Basic` / `.Algebra`: `AdicCompletion`,
  `AdicCompletion.of`, `AdicCompletion.evalₐ` and its ring/algebra structures.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime` and
  its local-ring structure (def-weil-pbc-localization-at-prime).
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing`, the exact ring
  clause of def-weil-regular-scheme's mathlib_match. Its recorded scheme module
  `Sheaf.AlgebraicGeometry.IsRegularScheme` is also imported; no specialization
  or replacement predicate is defined.
- Added the already-landed statement dependency `def-trf-complete-toric-model`:
  `Sheaf.RingTheory.CompleteToricModel`, `ToricMonoid.PolynomialRing` and
  `ToricMonoid.chartIdeal`. These reuse the existing monoid polynomial and chart
  ideal constructions. No new definition node or dependency repair is needed.
- Non-public proof imports record every stated proof dependency:
  `WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete`,
  `WeilConjectures.RingTheory.RegularLocalLocalization`,
  `Mathlib.RingTheory.RegularLocalRing.Polynomial`,
  `WeilConjectures.RingTheory.LocalizationOfRegularRing`,
  `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`,
  `WeilConjectures.RingTheory.LocalCompletionQuotient`,
  `Mathlib.RingTheory.AdicCompletion.LocalRing`, and
  `Mathlib.RingTheory.AdicCompletion.Completeness`.

Edge cases checked before and during writing: `n=0` gives an empty variable ideal;
trivial `K`, `S` and `T` are allowed. For trivial `T`, the nonvanishing condition
forces `S` trivial, exactly as in the source statement. There is no finite or
nonempty assumption on the underlying monoid types. For `n≥1`, `θ=p-t_1` satisfies
the hypothesis and its augmentation is `p-t_1`, whose image modulo `(t)` is `p`;
no equality modulo the maximal ideal squared has been substituted for that
congruence. The primes `(p)` and `(p,z-1)` in the one-Laurent-variable example are
both permitted. All four object universes are independent, and completion uses
Mathlib's genuine compatible-sequence definition. No statement dispute found.

Searches (no exact existing declaration):

- `msearch.py ... leanfinder` queried “A substituted formal monoid relation over a
  Cohen ring congruent to p modulo monomials and old parameters has nonzero
  cotangent class”: eight hits on smooth cotangent presentations; none states this.
- `msearch.py ... leanfinder` queried “Cohen ring Laurent polynomial ring completion
  substitution formal monoid nonzero regular parameter”: eight Laurent-series
  completion and rational-function hits, not this assertion.
- `msearch.py ... loogle "AdicCompletion, AddMonoidAlgebra"`: zero hits.
- `msearch.py ... grep 'Cohen.*monoid|cohen.*substitution|substitution.*parameter'
  RingTheory`: zero Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for completed monoids,
  substitution, Cohen parameters, and the item id: found the existing complete
  toric model, formal monoid implicit elimination, formal monoid ring dimension,
  and general Cohen/power-series presentations; none has this substitution and
  parameter conclusion. The new namespace and theorem name have no hits in
  Mathlib, `lean/WeilConjectures` or `lean/Sheaf`.
- Read ILO VI 1.6(ii) directly using `pdftotext` on PDF page 76 (printed p. 70):
  the relation is congruent to `p` modulo nonzero monomials AND old variables.
  The current blueprint ancestor locality statement/proof was also read; it now
  concerns contracting correspondences, so this is the separately recorded
  auxiliary local-algebra verification, as the accepted node already says.

Validation: server `scompile.py` compiled the module in sandbox and library
contexts successfully after supplying classical decidability for augmentation.
All declaration data are real constructions. The final delivery checks below
validate the final header and node record as well.

## Second reading by Q119

A separate rereading in this dispatched session compared the node and the complete
Lean file, including all helper bodies. No other agent was started, as instructed;
the maintainer supplies the independent delivery review. The old-parameter clause
was checked especially against `θ=p-t_1`: it is a congruence modulo `(t)`, and the
statement retains the final nonzero cotangent class after quotienting `(t)`. The
monomial formula fixes coefficients at `s=0`, the variable formula gives precisely
the old parameters, and augmentation is normalized on every coefficient monomial.
The comparison `e` has the canonical formula on localized elements. The regularity
of both `E'` and `E'/p`, `p≠0`, both maximal-ideal square exclusions, and the image
of `bar η` in the quotient and completed stratum are all present. Local and regular
structures occur in conclusions, not hypotheses. Classical decidability was added
for the literal `if t=0`; no mathematical clause changed. The extra dependency is
an already-landed definition for precisely the monoid polynomial/chart notation.
