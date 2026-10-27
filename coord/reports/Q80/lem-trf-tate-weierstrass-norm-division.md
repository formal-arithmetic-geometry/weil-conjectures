## Worker report

`Sheaf.RingTheory.TateWeierstrassNormDivision` states
`RestrictedSeries.tate_weierstrass_norm_division`, with its sole theorem proof
`sorry`. Two concrete interface helpers extract the distinguished-variable
coefficients (`weierstrassCoefficient`) and include polynomials over the existing
restricted-series ring into the ambient formal-series ring
(`weierstrassPolynomialExpansion`). Both use Mathlib's canonical constructions,
without data chosen from an existence theorem or postponed obligations.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- `(F : Type u) [NontriviallyNormedField F] [CompleteSpace F]` is exactly a
  complete field with a nontrivial real-valued multiplicative absolute value.
  `[IsUltrametricDist F]` adds precisely the nonarchimedean inequality. No
  discrete valuation, characteristic, or dense value group hypothesis appears.
- `s d : ℕ` includes both zero cases. A and D are exactly
  `MvPowerSeries.IsRestricted.subring (R := F) (fun _ : Fin s ↦ (1 : ℝ))`
  and the same expression at `s + 1`. Mathlib's defining cofinite convergence
  means exactly that the sets of coefficients with norm at least epsilon are
  finite. All Gauss norms are `MvPowerSeries.gaussNorm (norm : F → ℝ)` at
  radius one, so are the required suprema of coefficient norms.
- X is indexed by zero and the Y variables by successor indices.
  `MvPowerSeries.finSuccEquiv F s` canonically regroups by X. Its coefficient
  formula says `coeff x (PowerSeries.coeff k (finSuccEquiv F s p)) =
  coeff (x.cons k) p`. Thus `weierstrassCoefficient g.val i` is exactly a_i,
  represented in the ambient formal-series ring. Its restrictedness follows
  from g being restricted; no independently chosen coefficients are assumed.
- `hd` says a_d = 1; `hlower` bounds every coefficient for i < d. `hupper`
  takes the supremum over exactly `{i : ℕ // d < i}` and requires it to be
  strictly less than one. This is the uniform tail bound in the node, rather
  than just a pointwise strict inequality for each coefficient.
- The first conjunct quantifies over every h in D and supplies q in D and
  `r : Polynomial A`. `r.degree < (d : WithBot ℕ)` includes the correct degree
  of zero. The equality is `h.val = q.val * g.val +
  weierstrassPolynomialExpansion r`. The parent formal-series subring
  inclusion is injective, and the polynomial inclusion is canonical, so this
  is exactly the equality in D, not an equality after evaluation or quotient.
- The two inequalities bound the norms of q and r by the norm of h. The
  expanded polynomial's Gauss norm equals the maximum coefficient Gauss norm
  on A[X], since expansion only includes and reindexes its coefficients.
- Competitors `q'` and `r'` satisfy only the degree bound and division equality,
  and must equal q and r. No norm bounds are assumed on competitors: uniqueness
  is among all decompositions. `d = 0 → r = 0` explicitly records the final
  division edge-case clause.
- The second conjunct supplies `w : Polynomial A` and `unit : Dˣ`.
  `w.Monic ∧ w.natDegree = d` gives monicity and degree exactly d, because
  monicity implies w is nonzero. Every lower coefficient is bounded by one.
  `g.val = unit.val.val * weierstrassPolynomialExpansion w` is the specified
  factorization. The last two inequalities bound the unit and its actual
  multiplicative inverse by one. `d = 0 → w = 1` is explicit.

Dependency declarations read and used:

- `def-weil-polynomial-ring`: `Polynomial` in
  `Mathlib.Algebra.Polynomial.Basic`, lines 69–78, full docstring and structure;
  `Polynomial.degree`, `natDegree`, and `Monic` in
  `Mathlib.Algebra.Polynomial.Degree.Defs`, lines 45–61. The latter module is
  publicly imported and imports Basic. `Polynomial.map` and the canonical
  polynomial-to-power-series coercion give coefficient inclusion.
- Added the already landed `def-trf-restricted-series-presentation` to
  `stmt_deps` and publicly imported its module
  `Sheaf.RingTheory.RestrictedSeriesPresentation`. I read the full definitions
  and docstrings of `RestrictedSeries.constants`,
  `IsTopologicallyFinitelyPresented`, `IsAffinoidQuotient`, and
  `HasBoundedTopologicallyGeneratedImage`. Here the used notion is its
  specified Mathlib restricted-series subring, not its presentation predicates.
  No dependency repair or new node is needed.
- Read `MvPowerSeries.IsRestricted`, `IsRestricted.subring`, and `gaussNorm`
  in Mathlib Restricted.lean and GaussNorm.lean. Read `finSuccEquiv` and its
  coefficient formula in Equiv.lean, lines 159–181. These supply the existing
  ring, norm, and regrouping, rather than private copies.
- The proof dependency `lem-trf-restricted-series-gauss-completion` has no Lean
  record in the current read clone, hence no proof-only module to import.
  Its entire statement and seven-step proof were read. The assigned theorem's
  docstring carries all seven steps of its own node's proof: polynomial
  division, completion, contraction, uniqueness, preparation, and edge cases.

Edge cases checked mathematically before writing: if d = 0, the lower range
is empty, `degree r < 0` forces r = 0, and preparation has w = 1. For s = 0
there is still X and A is canonically F. For h = 0 the norm bounds force
q = r = 0. A zero upper tail satisfies `hupper` (the supremum is zero), and
the correction terminates immediately. A zero divisor g is excluded by hd,
not an extra assumption. Arbitrary characteristic, nondiscrete values, and
arbitrary universe u remain allowed. The supremum index is nonempty for every
d. Uniqueness requires no bounds on competing decompositions.

The source book remains explicitly WANTED in the node: its descriptive source
citation does not claim a verified theorem number. The proof is honestly the
DAG's agent reconstruction. I read the latest blueprint local-term lemma;
this analytic node is historical supporting material, and no current unit
statement or route changes.

Searches actually run with the prescribed `msearch.py` wrapper:

- LeanFinder: `Weierstrass division and preparation for restricted Tate series
  with Gauss norm bounds` — eight hits headed by
  `PowerSeries.IsWeierstrassDivision`, `IsWeierstrassDivisionAt`,
  `weierstrassDiv`, `exists_isWeierstrassDivision`. These concern formal adic
  series over local rings, not analytic restricted-series division with bounds.
- Loogle: `"weierstrassDiv"` — twelve hits for the same formal adic interfaces;
  no exact match.
- Mathlib grep: `Weierstrass|weierstrass|gaussNorm`, subdirectory
  `RingTheory/MvPowerSeries` — five hits, all GaussNorm.lean, no division.
- LeanSearch: `Tate algebra Weierstrass preparation division with Gauss norm
  bounds` — eight hits, formal `PowerSeries.weierstrassDiv` and related
  statements plus `PowerSeries.le_gaussNorm`; no exact match.
- `rg` in `lean/WeilConjectures` for
  `weierstrass|Weierstrass|gaussNorm|IsRestricted.subring` and the exact node
  ID — no matches. The initial broader `Tate|tate|Gauss|gauss|Restricted` search
  was inspected; its matches concern unrelated algebraic topics and prose.
- `rg` in `lean/Sheaf` found the existing restricted-series presentation and
  affinoid comparison, but no division statement. Exact new declaration names
  were searched in both library roots and `dag/lean_names_upstream.json`,
  with no matches.

No correction, disputed statement, new node, or dependency module. The node
copy changes only `lean` and adds the existing definition node to `stmt_deps`.
Universes are explicit and auto-implicits disabled. The prescribed scompile.py
compiled the module cleanly against the live library (library compile 9.3 s).

## Second reading by Q80

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
