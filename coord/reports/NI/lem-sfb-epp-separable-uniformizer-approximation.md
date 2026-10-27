## Worker report

The module `Sheaf.RingTheory.SeparableUniformizerApproximation` states
`IsDiscreteValuationRing.exists_separable_uniformizer_approximation` with one
`sorry` proof. It introduces no definitions. The node is unchanged except for
its `lean` attachment. The statement was checked against Stacks Project,
More on Algebra, Tag 09EW, `lemma-make-degree-q-extension`, and the use of its
second approximation in Tag 09EY, `lemma-purely-inseparable-case`.

Hypotheses and clauses, in order:

- Prime p: `(p : ℕ) (hp : p.Prime)`.
- Complete discrete valuation ring R of characteristic p: `(R : Type u)` with
  `[CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharP R p]` and
  `[IsAdicComplete (IsLocalRing.maximalIdeal R) R]`.
- Fraction field F of R: `(F : Type v) [Field F] [Algebra R F]
  [IsFractionRing R F]`. The ring and fraction field have independent universes.
- Uniformizer t: `(t : R)` and
  `(ht : IsLocalRing.maximalIdeal R = Ideal.span {t})`, exactly the node's
  definition of a uniformizer.
- Every integer n > 1: `(n : ℕ) (hn : 1 < n)`. All such integers are positive,
  so indexing by their natural-number values preserves exactly the range.
- There exists a finite separable extension F'/F: the existential field `L : Type v`
  has `Field L`, `Algebra F L`, `Module.Finite F L` and `Algebra.IsSeparable F L`.
  The accompanying `Algebra R L` and `IsScalarTower R F L` specify the composite
  R-algebra structure, with no restriction on the extension. A finite extension
  of F can be realized in the universe of F (for example as a polynomial quotient).
- Degree p: `Module.finrank F L = p`.
- Its integral closure R' of R is a complete DVR: R' is literally Mathlib's
  `integralClosure R L`, not an arbitrary ring with chosen comparison maps.
  The existential instance `hS : IsDiscreteValuationRing (integralClosure R L)`
  supplies its DVR structure; `IsAdicComplete` is taken at its maximal ideal,
  explicitly using `hS.toIsLocalRing`.
- There exist a uniformizer s and an element a in R': `∃ s a : integralClosure R L`,
  with its maximal ideal equal to `Ideal.span {s}`.
- Approximation t = s^p + s^(np)a:
  `algebraMap R (integralClosure R L) t = s ^ p + s ^ (n * p) * a`.
- The residue map R/(t) → R'/(s) is an isomorphism: the existential ring
  equivalence `e : R ⧸ Ideal.span {t} ≃+* (integralClosure R L) ⧸ Ideal.span {s}`
  satisfies, for every x in R,
  `e (Ideal.Quotient.mk (Ideal.span {t}) x) =
  Ideal.Quotient.mk (Ideal.span {s}) (algebraMap R (integralClosure R L) x)`.
  Surjectivity of the quotient projection makes this the induced map uniquely;
  the clause cannot be satisfied by an unrelated abstract residue isomorphism.
- Extended ideal equality (t)R' = (s)^p:
  `Ideal.map (algebraMap R (integralClosure R L)) (Ideal.span {t}) =
  (Ideal.span {s}) ^ p`.

Dependency declarations read in full with their docstrings and used directly:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing` from
  `Mathlib.RingTheory.DiscreteValuationRing.Basic`. Its recorded `mathlib_match`
  is usable without a `lean` attachment. The signature at line 58 extends local
  PID and excludes fields; `irreducible_iff_uniformizer` at line 93 confirms
  the generator formulation used here.
- `def-weil-pbc-adically-complete-ring`: `IsAdicComplete`,
  `AdicCompletion`, `AdicCompletion.of` from
  `Mathlib.RingTheory.AdicCompletion.Basic`. The first is the completeness
  predicate used here; `AdicCompletion.of_bijective_iff` identifies it with the
  node's bijective canonical completion map, including separatedness.
- `def-pc-field-extension`: `Algebra` from `Mathlib.Algebra.Algebra.Defs`, with
  `Field` instances and `algebraMap` for the field inclusion.
- `def-weil-pbc-separable-algebraic-extension`: `Algebra.IsSeparable` from
  `Mathlib.FieldTheory.Separable`. Its definition uses separable minimal
  polynomials for all elements and includes algebraicity.
- `def-weil-pbc-integral-closure`: `integralClosure` from
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, whose actual carrier is
  `{r | IsIntegral R r}`.

Additional public imports supply `IsFractionRing` and `Module.finrank` from
`Mathlib.RingTheory.Localization.FractionRing` and
`Mathlib.LinearAlgebra.Dimension.Finrank`. The proof dependency
`lem-sfb-epp-approximate-uniformizer-root` has no recorded Lean declaration or
Mathlib match in the node read for this delivery; its future proof import is
therefore absent. Its exact specialization and the sign rearrangement are in
the theorem docstring, following both steps of the node's accepted proof.
The other proof dependency is the already publicly imported DVR module.

Edge cases checked before writing:

- p = 0 and p = 1 are excluded precisely by primeness. Characteristic two is
  included: choosing a = -b' still gives the requested sign in that characteristic.
- n = 0 and n = 1 are excluded precisely by n > 1; n = 2 is included.
- Zero rings and fields are excluded by the node's DVR notion itself; t and s
  cannot be zero or units because their spans are nonzero maximal ideals.
- No perfection, finite residue field, residue separability hypothesis or chosen
  coefficient field is assumed. Infinite and imperfect residue fields are included.
- For R = F_p[[t]], the source's polynomial
  Y^p - t^(n+p-1)Y - t is Eisenstein and has nonzero derivative
  -t^(n+p-1), including p = 2. Its root is a uniformizer and the error term has
  order p(n+p-1)+1 >= np. This checks the sign, degree, small n, and exponent.
- The residue isomorphism explicitly agrees with the inclusion on every
  representative, and the final equality is an equality of ideals, not just
  a numerical ramification-index statement.

Searches for existing declarations (all queries completed):

- `msearch.py leanfinder`, query "A complete discrete valuation ring of
  characteristic p admits a separable totally ramified degree p extension with
  a uniformizer approximating the pth root of the original uniformizer": eight
  hits, including `PreTilt.untiltFun`, `Tilt`, `PreTilt`, and
  `Valuation.exists_pow_Uniformizer`; none asserts this finite-extension result.
- `msearch.py loogle`, query `IsDiscreteValuationRing, Algebra.IsSeparable`:
  zero hits.
- `msearch.py grep`, query
  `uniformizer.*approx|approx.*uniformizer|separable.*uniformizer`: zero hits.
- `msearch.py leansearch`, query "A complete discrete valuation ring admits a
  separable totally ramified degree p extension approximating the pth root of a
  uniformizer": eight hits concerning valuation uniformizers and DVR
  characterizations; none states the required approximation extension.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `uniformizer.*approx|approx.*uniformizer|separable.*uniformizer` and the item
  id found only unrelated geometric uses. Further searches for
  `exists.*[Uu]niformizer|[Ss]eparableUniformizer|separable_uniformizer|separable.*[Aa]pprox`
  found only unrelated chart and monic-approximation results.
- `rg` in Mathlib, both project Lean roots, and `dag/lean_names_upstream.json`
  for the chosen declaration name `separable_uniformizer_approximation` found
  no collision. No notion has been duplicated.

No statement correction, dependency repair, new node or disputed statement is
needed. All binders and universes are explicit and `autoImplicit` is disabled.
The prescribed `scompile.py` compiled both its sandbox and library module checks
cleanly (1.8 seconds each); no warnings or errors were printed.

## Second reading by NI

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
