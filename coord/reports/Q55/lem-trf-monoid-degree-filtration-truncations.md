## Worker report

The module `Sheaf.RingTheory.MonoidDegreeFiltrationTruncations` states
`AddMonoidAlgebra.monoid_degree_filtration_truncations`, with its proof `sorry`.
No definitions, dependency repairs, new nodes, or statement corrections are needed.
The original node is unchanged except for `lean`.

Source read: ILO, Travaux de Gabber, Exposé VI, §1.6(i)–(ii), printed p. 70
(PDF p. 76, extracted with pdftotext). It gives completed monoid models, not this
auxiliary algebra theorem. The node explicitly attributes its filtration and
truncation argument to the agents. Its six proof steps are all reproduced in
the declaration docstring. The combined-ideal coefficient criterion is imported
as a proof dependency, not attributed to ILO.

Hypotheses and objects, matched against the node:

- `r : ℕ` represents every nonnegative integer, including zero. The exponent
  type `Fin r →₀ ℕ` is Mathlib's canonical exponent type for r variables; since
  `Fin r` is finite it is canonically equivalent to the node's `ℕ^r`.
- `Q : AddSubmonoid (Fin r →₀ ℕ)` is exactly the additive submonoid of exponents.
  `s : ℕ`, `q : Fin s → Q`, `h_nonzero`, and
  `h_generates : AddSubmonoid.closure (Set.range q) = ⊤` express the chosen finite
  list of nonzero additive generators. This condition implies finite generation;
  a separate finite-generation hypothesis would be redundant. There is no
  saturation, freeness, normality, or nontriviality assumption.
- `L : Type u`, `[CommRing L]`, and `a : Ideal L` give the arbitrary commutative
  coefficient ring and its ideal. No Noetherianity or completeness is assumed.
- `AddMonoidAlgebra L Q` is B, with its standard finite support and convolution
  multiplication. `MvPowerSeries (Fin r) L` is A, using the dependency declaration.
- `j` is an `L`-algebra homomorphism. Its defining equation is
  `j f = f.coeff.sum (fun e c ↦ MvPowerSeries.monomial (e : Fin r →₀ ℕ) c)`:
  exactly the finite sum sending `c z^e` to `c X^e`. The existential binder
  together with this equation specifies the canonical map completely; it does
  not assume an arbitrary map or arbitrary choice of embedding.
- `J` is specified by equality with `Ideal.map (algebraMap L B) a` joined with
  the span of the nonzero monomials `single e 1`. `I` is specified by equality
  with the analogous extended coefficient ideal joined with the span of the
  variables `MvPowerSeries.X`.
- `D = max 1 (Finset.univ.sup (fun i ↦ (q i : Fin r →₀ ℕ).degree))` is exactly
  the maximum of 1 and the degrees of the chosen list. `Finsupp.degree` is the
  sum of all coordinates. For the empty list the supremum is zero, so D is 1.
  The defining equations for J, I and D simply introduce the node's objects;
  they impose no additional hypotheses or alternative choices.

Conclusions, clause by clause:

- `Function.Injective j`, together with j's `→ₐ[L]` type, gives the injective
  L-algebra homomorphism assertion.
- For every `n : ℕ`, `J ^ n ≤ Ideal.comap j.toRingHom (I ^ n)` is `J^n ⊆ E_n`,
  and `Ideal.comap j.toRingHom (I ^ (D * n)) ≤ J ^ n` is `E_(Dn) ⊆ J^n`.
  Thus E is the actual inverse image, not an unrelated filtration.
- `∀ e, e ∉ Q → MvPowerSeries.coeff e F = 0` is precisely the support hypothesis.
- The equation for `b n` is a finite sum over
  `(Finsupp.finite_of_degree_lt (D * n)).toFinset`; a term is `single ⟨e,h⟩`
  with coefficient `coeff e F` when `e ∈ Q`, and zero otherwise. This is
  precisely the sum over `q ∈ Q` with `|q| < Dn`, and establishes finiteness
  using the existing finite-degree theorem. There is no infinite sum or
  unsupported finiteness assumption.
- For every `m n` with `n ≤ m`, the conjuncts are
  `b m - b n ∈ J ^ n` and `F - j (b n) ∈ I ^ (D * n)`. This includes all n,
  since m may equal n.
- `∃ x : AdicCompletion J B, ∀ n, AdicCompletion.evalₐ J n x =
  Ideal.Quotient.mk (J ^ n) (b n)` asserts that these precise residues form an
  inverse-limit element, with every component fixed. Mathlib's completion is
  the subtype of compatible quotient sequences. `evalₐ` expresses the ring
  quotient version of its module quotient components.
- `∀ e n, e.degree < D * n → coeff e (j (b n)) = coeff e F` is the final exact
  coefficient assertion, including exponents outside Q. Its strict inequality
  is the node's `Dn > |e|`.

Dependency declarations read and used:

- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries` (line 86), its
  `monomial` (132), `coeff` (137), and `X`. These are the exact recorded
  declaration and associated operations for `def-weil-pbc-multivariate-power-series`.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion` (line 171),
  defined as compatible sequences modulo `I^n • ⊤`; the ring case identifies
  this submodule with `I^n`. `Mathlib.RingTheory.AdicCompletion.Algebra`:
  `AdicCompletion.evalₐ` (132), its canonical projection to `B ⧸ J^n`.
  These use the exact completion recorded on `def-weil-pbc-adic-completion`.
- `WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients`:
  `power_series_mem_combined_ideal_pow_iff`, read with its full signature and
  docstring. It is the proof-only import for the node's steps 3 and 5.
- `Mathlib.Algebra.MonoidAlgebra.Basic`: `AddMonoidAlgebra`, `single`, and its
  coefficient finite support; these supply the monoid algebra already in Mathlib.
- `Mathlib.Data.Finsupp.Weight`: `Finsupp.degree` and `finite_of_degree_lt`
  (line 260), for exact total degree and the finite truncation index set.

Edge cases checked: n=0 gives empty truncation, ideal zeroth powers equal top,
and a zero quotient at completion level zero; m=n gives zero difference.
For Q={0} the list may be empty, D=1, B=L, and for n>0 the truncation retains
only the constant. For r=0 the exponent type has only zero and the variables
ideal vanishes. A nonempty list may repeat generators. There is no assumption
that L is nonzero, that a is proper or finitely generated, or that Q spans the
ambient lattice. The zero ring, a=0, a=top and proper submonoids are all included.
No node fault or disputed assertion was found.

Searches actually run on 2026-10-24:

- msearch.py leanfinder: "A finitely generated submonoid of natural exponent
  vectors embeds in formal power series and degree truncations are compatible
  with powers of the coefficient plus augmentation ideal". Returned
  `MvPowerSeries.trunc'_trunc'_pow`, `PowerSeries.trunc_trunc_pow`, and related
  truncation/expansion declarations; no filtration comparison for Q.
- msearch.py loogle: `AddMonoidAlgebra, MvPowerSeries`. Zero hits.
- msearch.py leansearch: "Degree filtration comparison for a finitely generated
  submonoid algebra in multivariate formal power series with compatible
  supported truncations". Returned grading, `truncFun`, `truncFun'`,
  `Ideal.Filtration.submodule`, and support-degree results. None states the item.
- msearch.py grep: `monoid.*(filtration|truncation)|AddMonoidAlgebra.*MvPowerSeries|cofinal.*degree`.
  Zero hits. Direct rg of both `lean/WeilConjectures` and `lean/Sheaf` with this
  expression likewise found no exact result; direct node-id grep in
  `lean/WeilConjectures` found none.
- Direct rg by the proposed declaration name in Mathlib, `lean/WeilConjectures`,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collision.
  Broader monoid searches found `MonoidCompletionCoefficients` and
  `FinitePatternFactorization`, which concern complete local coefficient rings
  and positive abstract monoids, not this arbitrary-ring filtration statement.
  Read `MonoidCompletionCoefficients` to check this difference. Also read
  Mathlib's `AddMonoidAlgebra.lift`, polynomial `monomialOneHom` and the polynomial
  inclusion in power series: these are ingredients, not the theorem.

Validation: scompile.py compiled the sandbox and actual module cleanly
(1.7 s and 1.4 s respectively), using the published server library.

## Second reading by Q55

A second clause-by-clause pass by the dispatcher worker, with the original JSON
and final module open, checked all binders and the defining equations. The
independent review is the maintainer's delivery review, as specified in this
assignment; no separate agent was started. In particular the pass checked that
finite generation is encoded by the chosen generating list, the cutoff is Dn
rather than n, the second containment has exponent Dn on I, the difference uses
m≥n, the tail has exponent Dn, and the limit component uses J^n rather than
J^(Dn). It also checked the support condition and eventual coefficient equality
outside Q, empty lists and all zero cases. No mismatch was found and no
statement change was made. The equality-characterized existential witnesses
specify every map, ideal, bound and truncation by the node's actual formula.

Delivery dry run: `deliver2.py --no-push` returned OK, with preflight and
per-file compilation passing. Only the module, item node and report were staged.
