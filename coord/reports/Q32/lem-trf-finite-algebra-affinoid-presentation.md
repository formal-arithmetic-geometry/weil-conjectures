## Worker report

The single module `Sheaf.RingTheory.FiniteAlgebraAffinoidPresentation` states
`RestrictedSeries.finite_algebra_affinoid_presentation`, with `sorry` as its only proof.
The node is unchanged except for its `lean` record. No new definitions or nodes,
dependency repairs, or statement corrections are needed.

Source read: Brian Conrad, *Several approaches to non-archimedean geometry*,
https://math.stanford.edu/~conrad/papers/aws.pdf, Theorem 1.2.6(3), PDF p.6, and the
quotient-norm discussion on PDF pp.5–6 and Exercise 1.2.4. The theorem gives affinoidness
of every module-finite algebra; the preceding construction equips any Tate quotient
with its complete homogeneous nonarchimedean quotient norm. This agrees with the node.

Hypotheses and conclusion, clause by clause:

- The complete field with a nontrivial real-valued multiplicative nonarchimedean absolute
  value is `(K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]`. `NontriviallyNormedField.non_trivial` asks for a norm greater than
  one, equivalent over a field to the absolute value being nontrivial (invert a small
  nonzero element when necessary). Its inherited `Field` is the dependency's definition.
- The nonzero commutative K-algebra A is `(A : Type v) [CommRing A] [Nontrivial A]
  [Algebra K A]`. The hypothesis `hA` existentially quantifies `r : ℕ` and a ring map
  from `MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ))` to A,
  with `Function.Surjective α` and `α.comp (constants K r) = algebraMap K A`.
  Thus the input is an algebraic Tate quotient presentation; it does not presume a
  norm, completeness, continuity, or a finitely generated kernel on A.
- The nonzero commutative unital A-algebra B is `(B : Type w) [CommRing B]
  [Nontrivial B] [Algebra A B]`. Finite generation as an A-module is precisely
  `[Module.Finite A B]`. The K-algebra structure is `[Algebra K B]
  [IsScalarTower K A B]`; `IsScalarTower.algebraMap_eq` identifies it with the composite
  K → A → B, rather than imposing an independent scalar action.
- The asserted norm is `∃ N : RingNorm B`. This Mathlib structure contains positivity,
  separation at zero, invariance under negation, the triangle inequality, and
  submultiplicativity for the given ring operations on B. The normed commutative ring
  `{ N.toNormedRing, ‹CommRing B› with }` uses exactly those original operations.
  In particular there is no existential replacement of the algebraic structure.
- `@IsAffinoidQuotient K _ _ B { N.toNormedRing, ‹CommRing B› with }
  (algebraMap K B)` uses the dependency's actual predicate. Unfolding it gives
  completeness in the N-metric and `∃ (m : ℕ) (q : K⟨Y₁,…,Yₘ⟩ →+* B)`, with
  surjectivity, compatibility with `constants K m` and the fixed K-structure, and
  `∀ b, N b = sInf {r : ℝ | ∃ f, q f = b ∧ r = gaussNorm norm 1 f.val}`.
  This is the required infimum over the full fibre of the very same q. The Gauss norm
  at polyradius one is the supremum of the coefficient norms. Surjectivity makes
  each fibre nonempty; Gauss norms are nonnegative, so no empty-infimum convention
  changes the meaning. The metric is `N (x - y)` up to the usual negation symmetry.
- `IsNonarchimedean (N : B → ℝ)` explicitly adds `N (b+b') ≤ max (N b) (N b')`.
- `∀ (c : K) (b : B), N (c • b) = ‖c‖ * N b` is the exact scalar equality, for the
  given composite action. It includes zero scalars and the zero element.
- No injectivity of A → B, reducedness of A or B, or separability hypothesis occurs.
  The affinoid conclusion is precisely the recorded dependency predicate, not a new
  substitute or a mere existence of an unspecified Banach algebra isomorphism.

Dependency declarations read and used:

- `Field`, `Mathlib.Algebra.Field.Defs`, source line 180: field definition, inherited by
  `NontriviallyNormedField` (whose full signature was read in
  `Mathlib.Analysis.Normed.Field.Basic`, lines 153–169).
- `RestrictedSeries.constants` and `RestrictedSeries.IsAffinoidQuotient`,
  `Sheaf.RingTheory.RestrictedSeriesPresentation`, source lines 31–61. Read the whole
  module, including the recorded main declaration `IsTopologicallyFinitelyPresented`;
  that adic notion is not the affinoid clause used by this item.
- `Module.Finite`, `Mathlib.RingTheory.Finiteness.Defs`, source lines 116–120.
- Mathlib's `MvPowerSeries.IsRestricted.subring` and `MvPowerSeries.gaussNorm`, read in
  `Mathlib.RingTheory.MvPowerSeries.Restricted` and `.GaussNorm`. At radius one their
  definitions are exactly coefficient decay in the cofinite filter and the coefficient
  supremum. `RingNorm` and `RingNorm.toNormedRing` were read in
  `Mathlib.Analysis.Normed.Unbundled.RingSeminorm`.

Already stated proof dependencies are imported without `public`:
`Mathlib.RingTheory.IntegralClosure.Algebra.Basic` for `Algebra.IsIntegral.of_finite`,
`Mathlib.RingTheory.Ideal.Quotient.Operations` for quotient algebra operations, and
`Mathlib.Analysis.Normed.Group.Quotient` for `Ideal.Quotient.normedCommRing`,
`Ideal.Quotient.normedAlgebra`, `Submodule.Quotient.completeSpace`, and
`quotient_norm_mk_eq`. Their signatures and surrounding source were read. The polynomial
ring and its evaluation are already publicly imported by the statement dependency.
The proof-only nodes `lem-trf-restricted-series-gauss-completion`,
`lem-trf-tate-separated-monic-quotient`, and `lem-trf-tate-ideal-best-approximation`
have no recorded Lean declaration; no speculative import or restatement is added.
The theorem docstring preserves all five proof steps, including these node references.

Edge cases checked before writing: r = 0 and m = 0 are allowed by natural-number
binders, with `Fin 0` giving the constant restricted-series ring. The statement has no
positive-rank assumption on the finite module. It allows nilpotents, repeated roots,
noninjective A → B (for example quotient algebras), arbitrary characteristic, arbitrary
nontrivial value groups, and algebraically nonclosed K. A = 0 and B = 0 are excluded
exactly as the node says. Universes u, v, w are independent and explicitly bound;
no small test-object quantifier or implicit universe restriction is introduced.

Searches actually run with `msearch.py Q32 lem-trf-finite-algebra-affinoid-presentation`:

- LeanFinder: `A module finite algebra over a strict affinoid algebra admits a surjective
  Tate algebra presentation with a complete quotient Gauss norm` returned eight hits,
  including `Module.Finite.exists_free_surjective`, ordinary finite presentations, and
  adic-completion surjections. None gives the Tate/quotient-norm statement.
- Loogle: `"Module.Finite", "NormedAlgebra"` returned zero hits.
- LeanSearch: `A module finite commutative algebra over an affinoid algebra is an
  affinoid algebra` returned eight hits, including `Module.Finite.finiteType`,
  `RingHom.Finite`, and the integral/finite-type criterion. None is the analytic claim.
- Mathlib grep: `TateAlgebra|affinoid|restricted.*series` in `RingTheory` returned ten
  hits in the restricted-series files, providing the existing ring, not this theorem.
- `rg` over project `lean/WeilConjectures` and `lean/Sheaf` for
  `affinoid|IsAffinoidQuotient|finite_algebra_affinoid` found the existing presentation
  predicate and other affinoid inputs, but no theorem stating this item. The nearby
  `AffinoidPolynomialClosedPointComparison` was read; it concerns completed local
  rings of polynomial quotients and does not assert finite-algebra affinoidness.
- A direct grep for the item id under `lean/WeilConjectures` returned no match; the
  upstream-name index search returned no match. The withdrawn CompactObject example
  and its current upstream node binding were also read as requested.

Validation: `scompile.py Q32 lem-trf-finite-algebra-affinoid-presentation` compiled the
single file on the server in both sandbox and library mode, with no errors or warnings
(15.3 and 11.3 seconds respectively). Both automatic-implicit options are disabled.
No definition data or helper proof is postponed, and the sole `sorry` belongs to the
matching theorem node. No STATEMENT-DISPUTED issue was found.

## Second reading by Q32

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
