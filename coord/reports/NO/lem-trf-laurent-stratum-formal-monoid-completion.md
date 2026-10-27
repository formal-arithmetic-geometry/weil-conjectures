## Worker report

Stage 2, group NO, 2026-10-23. The module
`Sheaf.RingTheory.LaurentStratumFormalMonoidCompletion` states
`AddMonoidAlgebra.LaurentStratum.completion`, with one `sorry` and the full eight-step
proof plan in its docstring. Its three abbreviations have literal Mathlib data:
`CoefficientRing = MvPolynomial (Fin n) (AddMonoidAlgebra L K)`,
`LocalCoefficients = Localization.AtPrime p`, and
`CompletedCoefficients = AdicCompletion (maximalIdeal (Localization.AtPrime p)) _`.
These merely name the three composite expressions in this node; no independent notion,
new definition node, dependency repair, or statement correction is needed.

The current node has no Lean record and is a stage-2 queue item. The old BLOCKED ending
concerned an unchanged stage-1 delivery. The current standing stage-2 brief, section 0,
explicitly permits this stage handoff. The accepted stage-1 split is preserved: only
`lean` changes in the node copy. There is no released repair note for this item.

Source read: ILO, Travaux de Gabber, VI 1.6, printed p. 70 (PDF p. 76), using the local
PDF. It gives the field and Cohen formal monoid models and sharp fs condition. As the
node's `proof_origin` says, this particular Laurent-stratum comparison is an
agent-supplied algebraic construction attached to those models, not a quotation of ILO.
The Lean statement follows that node and its accepted proof, without attributing its
additional quotient calculations to ILO.

Hypothesis and clause correspondence:

- A field or Cohen coefficient ring: `(L : Type u) [CommRing L] [IsLocalRing L]` and
  `hL : IsField L ∨ ∃ p₀ : ℕ, IsCohenRing p₀ L`. Both allowed kinds are local rings;
  displaying the local structure makes the specified `maximalIdeal L` available and
  imposes no restriction on either kind. The Cohen predicate already includes
  primality, the DVR condition, the specified maximal ideal and completeness.
- Finite free abelian group: `(K : Type v) [AddCommGroup K] [Module.Free ℤ K]
  [Module.Finite ℤ K]`. No basis or positive rank is assumed.
- Sharp fine saturated additive monoid: `(T : Type w) [AddCommMonoid T]`,
  `hfs : AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative T)`, and
  `hsharp : ∀ t : T, IsUnit (Multiplicative.ofAdd t) → t = 0`. The multiplicative
  type synonym lets the existing fs predicate express the additive notion exactly.
  There is no assumption that this sharp monoid is free.
- Nonnegative number of variables: `(n : ℕ)`; `Fin n` indexes precisely those variables.
- `E = L[K][t_1,...,t_n]`: `CoefficientRing L K n` above, with actual finite-support
  additive monoid rings. The product law in `AddMonoidAlgebra` is `[u][v]=[u+v]`.
- The prime `p` and its containment: `(p : Ideal (CoefficientRing L K n)) [p.IsPrime]`
  and `hp`, the inequality from the supremum of the image of `maximalIdeal L` and
  the span of all polynomial variables into `p`. It is not restricted to a maximal
  ideal or to the augmentation prime of the Laurent variables.
- `E_*` and `D`: `LocalCoefficients p` and `CompletedCoefficients p` above.
  `U` is the literal `AddMonoidAlgebra (CoefficientRing L K n) T`.
- The ideal `r`: parameter `r` with `hr` equal to the image of `p` plus the ideal
  spanned by `single t 1` for all `t ≠ 0`. Universal quantification over an ideal
  satisfying this equality is just naming the displayed ideal, not an arbitrary
  extra prime. The conclusion first supplies `∃ _ : r.IsPrime`, so primeness of
  this constructed ideal is a conclusion. `Z` is then `Localization.AtPrime r`.
- Nonzero complete regular Noetherian local `D`: `∃ _ : IsRegularLocalRing D`,
  `Nontrivial D`, and `IsAdicComplete (maximalIdeal D) D`. The regular-local class
  extends both `IsNoetherianRing` and `IsLocalRing`, so neither clause is omitted.
- The residue field: `∃ k : (D ⧸ maximalIdeal D) ≃+* FractionRing (E ⧸ p)`.
  The equation for each `e₀ : E` specifies that this isomorphism is the one induced
  by the coefficient map, not an unrelated abstract ring isomorphism.
- The ideals `b` and `a`: universally quantified ideals with equalities to the
  respective coefficient maximal ideal plus the span of all nonzero `single t 1`.
  Thus these ideal parameters are fixed by the node's formulas. `H` throughout
  is the literal `AdicCompletion a (AddMonoidAlgebra D T)`, which is Mathlib's
  compatible-family inverse limit of all the displayed quotients.
- The canonical map `E_*[T] → Z`: existential `f`, with its value fixed on every
  `single t (image e₀)` for `e₀ : E`. This determines the map on the coefficient
  localization (inverses have unique images) and all monomials.
- All positive finite quotient isomorphisms: `q j hj : (E_*[T] ⧸ b^j) ≃+*
  (Z ⧸ maximalIdeal Z^j)` and `s j hj : (E_*[T] ⧸ b^j) ≃+* (D[T] ⧸ a^j)`.
  The node's first displayed arrow is `q.symm`. The two equations on every
  quotient representative make these exactly the maps induced by `f` and
  coefficient completion (`AddMonoidAlgebra.mapRingHom T`), respectively.
- Compatibility for all positive levels: two equations for every `i ≤ j`, with
  the actual `Ideal.Quotient.factorPow` reduction maps, express commuting squares
  for both `q` and `s`.
- The completed comparison: `∃ e : AdicCompletion (maximalIdeal Z) Z ≃+* H`, with
  the evaluation equation for every positive `j` and every completed element.
  The level map is explicitly `s j hj ∘ (q j hj).symm`.
- Continuity in both directions: two `Continuous` clauses, one for `e`, one for
  `e.symm`, under the adic topologies of the defining ideals extended into the
  two completions. This specifies the formal-adic topologies explicitly, without
  relying on any ambient topology instance.
- Coefficients and monomials: the equation on each `single t e₀` says that `e`
  sends its image from `U` through `Z` and completion to `single t (image e₀)`
  in the completion of `D[T]`. Taking `t=0` gives every coefficient of `E`;
  taking `e₀=1` gives every monomial `[t]`.
- The augmentation quotient: a ring homomorphism `ε : H →+* D` kills every
  nonzero monomial and is the identity on coefficients, by the displayed
  conditional formula on each `single t d`. Classical decidability is supplied
  directly to that conditional; no decidability hypothesis is added to `T`.
  The ideal in `g : (H ⧸ span {images of single t 1 | t ≠ 0}) ≃+* D` is precisely
  `([v] : v ≠ 0)H`. Its equation on all `x : H` says it is induced by `ε`, and
  `g.symm d = quotient (of (single 0 d))` specifies its coefficient inverse.

Dependency declarations read and used:

- `WeilConjectures.RingTheory.CohenRing`: `IsCohenRing`.
- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`: its public import exposes
  `AlgebraicGeometry.IsFineSaturatedMonoid`, whose complete definition and docstring
  were read in `Sheaf.AlgebraicGeometry.LogRegularPair`. The fs-log-blowup node's
  main declaration `IsSaturatedLogBlowup` was also read; this item uses its monoid
  clause, not the geometric blowup construction.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`, with its
  coefficient algebra map and local-ring structure.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`,
  `IsAdicComplete`, `AdicCompletion.of`, and `AdicCompletion.evalₐ`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme` and the ring clause of that node in
  `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing` (which extends
  `IsNoetherianRing`, defined in `Mathlib.RingTheory.Noetherian.Defs`). This item
  concerns rings, not a new predicate for schemes.

The module also imports each currently stated proof dependency, using its recorded
upstream module or Mathlib match: `PowerSeriesFieldCohenRegularComplete`,
`RegularLocalLocalization`, `LocalizationOfRegularRing`, `CompletionRegularLocal`,
`AdicCompletionNoetherian`, Mathlib's `RegularLocalRing.Polynomial`,
`AdicCompletion.LocalRing`, `AdicCompletion.Completeness`, `RingTheory.FiniteType`,
`Localization.Submodule`, `Sheaf.TraceFormula.SharpFsOrthantEmbedding`, and
`Sheaf.NumberTheory.Padics.AdicInverseLimitIso`. The proof-only nodes
`lem-trf-positive-monoid-adic-filtration` and `lem-trf-formal-monoid-residue-domain`
currently have neither a Lean record nor a Mathlib match; they supply no symbol
needed to type this statement and therefore no import can yet be added for them.
Their intended uses are preserved in proof-plan steps 6 and 8.

Edge cases checked before finalizing:

- `T = {0}`: no nonzero-monomial generators, `a=m_D D[T]`, `b=m_E* E_*[T]`,
  and augmentation is coefficient identity. All quantifiers remain meaningful;
  no nonempty set of nonzero monomials or positive monoid rank is assumed.
- `K=0` and `n=0`, separately and together: the group ring and polynomial ring
  permit these cases. The zero group is a finite free integer module. In the
  field case with both zero, `p=0`, `E_*=D=L`, and this is ordinary formal monoid
  completion. With `T=0` as well all isomorphisms are coefficient identities.
- Cohen coefficients with `K=0=n`: the same statement is the usual completion
  over the complete DVR; it does not force residue characteristic zero.
- A nonmaximal Laurent prime is allowed, e.g. `L` a field, `K=ℤ`, `n=0`, `p=0`:
  `D=Frac(L[K])` and the residue-field target is that fraction field. No closed
  point or algebraically closed residue field is assumed.
- Singular fs monoids are allowed, e.g. the saturated cone `a≥0, 0≤b≤2a` in
  `ℤ²`; the statement does not inadvertently restrict to free monoids.
- `j=1` gives the residue quotients. `j=0` is deliberately outside the positive
  quotient family, exactly as in the node. AdicCompletion still includes its
  automatically zero level, as in Mathlib's definition.
- Universes `u v w` are explicitly declared and independent; every ring
  construction lives in their appropriate maximum. `autoImplicit` is false.

Searches for existing statements (raw summaries are retained in `searches.jsonl`):

- `msearch.py leansearch`, query "completion of localized sharp monoid algebra over
  a completed Laurent coefficient ring": eight results, including
  `LaurentSeries.LaurentSeriesAlgEquiv`, `Algebra.Extension.localization`, and
  `AdicCompletion.instAlgebra`. None compares the stated arbitrary coefficient
  prime, sharp monoid, and all positive quotient levels.
- `msearch.py leanfinder`, query "completion of a sharp fine saturated monoid
  algebra at a Laurent stratum prime is the monoid completion over the completed
  coefficient localization": eight LaurentSeries completion/localization results;
  all concern one-variable valued Laurent series, not this statement.
- `msearch.py loogle`, query `AdicCompletion, AddMonoidAlgebra`: zero results.
- `msearch.py grep`, query
  `LaurentStratum|laurentStratum|formal_monoid.*completion|monoid.*completion`,
  subdirectory `RingTheory`: one unrelated Dedekind-domain valuation result.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf`, queries `LaurentStratum` and
  `monoid.*completion|completion.*monoid`: no existing Laurent-stratum theorem.
  Related monoid-completion coefficient, support-projection and formal-ring-dimension
  statements do not assert the finite quotient or localized Laurent comparison.
- Exact node-id search in both Lean roots and `dag/lean_names_upstream.json`: no hits.
  DAG inspection also found `lem-sfb-laurent-monoid-completion`; its larger setup
  with an additional completed monoid direction differs from this node, and it
  currently supplies no recorded declaration for this statement.

No node fault or statement dispute was found. The compiler's initial undecidable
`t=0` error was repaired by explicitly using classical decidability; a long line
warning was repaired by wrapping the line. No theorem was proved in this delivery.

## Second reading by NO

A separate second pass in the same worker session compared the node and file clause
by clause; no other agent was started, as the dispatch brief prohibits that. The
maintainer's independent review remains the external second reader.

The second pass verified that `∃ _ : IsRegularLocalRing D` supplies Noetherianity,
that primeness of `r` is a conclusion, and that `r`, `b`, `a` are fixed by equalities.
It checked the first quotient equivalence's reversed orientation, both commuting
reduction squares, the evaluation equation tying the completed map to those same
quotient maps, both adic continuities, and the formulas fixing coefficients,
monomials and the augmentation quotient's inverse. It confirmed that all three
zero-parameter cases remain present. The only repairs were the explicit classical
decision for the augmentation formula, explicit types on the remaining element
binders, the standard module header, and line wrapping. The TeX statement and every
stage-1 field are unchanged.
