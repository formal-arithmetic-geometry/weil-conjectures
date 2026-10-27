## Worker report

The module `Sheaf.RingTheory.CompleteToricLocalizedUnitDivisorLift` states
`ToricMonoid.complete_toric_localized_unit_divisor_lift`. Its sole theorem has
proof `sorry`; it introduces no definitions or additional assumptions. The natural-language
statement and accepted stage-1 proof are unchanged.

I read the item, each statement dependency's statement and Lean record (or Mathlib match),
the relevant signatures and docstrings, and the four proof dependency statements. I read
ILO, Exposé VI 1.1--1.6, PDF pages 75--76, printed pages 69--70, including the field and
Cohen models in 1.6. This is the node's agent-formulated divisor lemma, not a claim that
ILO states a converse recognition theorem. The current blueprint ancestry is
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md`.
Kato and Niziol's WANTED texts are not claimed as read.

Clause-by-clause correspondence:

- An additive commutative monoid is `(P : Type u) [AddCommMonoid P]`.
  `hfs : AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative P)` means finite
  generation, injectivity into the canonical group completion, and saturation there.
  The multiplicative tag changes notation only. `hsharp` says precisely that an
  invertible element of `P` is zero.
- The nonnegative integer number of parameter variables is `(n : ℕ)`.
- `(R : Type w) [CommRing R]` and `z : P → R` are the ring and its chart monomials.
  `hmodel : ToricMonoid.IsCompleteModel.{u, v, w} P n R z` is exactly the two alternatives
  in the statement. Its first disjunct existentially supplies a field `k : Type v`
  and a ring isomorphism from `B_k(P,n)` carrying every specified monomial to `z q`.
  Its second supplies a commutative local ring `C : Type v`, `IsCohenRing p C`,
  `θ - p ∈ completedChartIdeal C P n`, and an isomorphism from the quotient by `(θ)`
  carrying the quotient monomials to `z`. `IsCohenRing` includes primality of `p`, the
  domain/DVR condition, maximal ideal `(p)` and `(p)`-adic completeness. It does not
  assume the residue field perfect. `Complete` is the existing `AdicCompletion` of the
  polynomial monoid ring at the maximal-ideal-plus-chart ideal. All these are real
  published definitions, not new copies. Universes `u`, `v`, `w` are independent.
- `[IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]` render the assumed
  Noetherian normal domain, including `1 ≠ 0`. `hmonomial` is exactly nonvanishing of
  every chart monomial.
- The multiplicative set is `Submonoid.closure (Set.range z)`. The model condition
  makes `z 0 = 1` and `z (a + b) = z a * z b`, so its image already is a submonoid:
  this closure is precisely the stated `S = {z^a : a ∈ P}`, not a larger localization.
  The canonical `algebraMap R (Localization ...)` is the node's `ℓ`.
  Mathlib's localization uses the fraction relation with a witness denominator, so
  zero divisors have not been silently cancelled in the definition.
- `(f : R)` and `hf : IsUnit (algebraMap R (Localization ...) f)` express exactly the
  element and localized-unit hypothesis.
- The first conjunct `f ≠ 0` is the node's nonvanishing conclusion. The second is
  `∃ a₀ : P, ∀ q : Ring.WeilHeightOnePrime R, ...`. The existing height-one-prime type
  consists of nonzero prime ideals with no prime strictly between them and zero.
- `Ring.weilOrder q f = Ring.weilOrder q (z a₀)` is exactly the displayed pointwise
  normalized-valuation equality. The recorded divisor definition computes `weilOrder`
  by `Ring.ord (Localization.AtPrime q.1.asIdeal)`, namely the length of the quotient
  by the given element, converted to an integer. In a Noetherian normal domain the
  height-one localization is a DVR and, for a nonzero ring element, this length is
  finite and equals its normalized additive valuation (uniformizer value one).
  Nonzero `f` and `hmonomial` prevent the infinite-length-to-zero convention from
  changing this conclusion. Since both arguments belong to `R`, no fraction lift
  or separately chosen valuation is necessary. The node states the pointwise form
  or equivalently equality of principal divisors; the pointwise form is stated here.
  The fraction field is determined by `R`, so omitting a redundant binder for it
  removes no choice or hypothesis.

Dependency declarations reused:

- `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`, through its public import
  `Sheaf.AlgebraicGeometry.LogRegularPair`: `AlgebraicGeometry.IsFineSaturatedMonoid`,
  whose full definition was read at LogRegularPair.lean:138--146. No log scheme or
  blowup hypothesis is added to this purely algebraic statement.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, read at lines 167--173;
  used inside the published complete model.
- `WeilConjectures.RingTheory.CohenRing`: `IsCohenRing`, its full definition read;
  used inside the published complete model.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, lines 193--197.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  lines 69--74, together with `IsDomain`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`, lines
  55--58; used by `Ring.weilOrder`.
- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`,
  lines 56--60, through `IsCohenRing` and the interpretation of height-one orders.
- `Sheaf.RingTheory.WeilDivisorClassGroup`: `Ring.WeilHeightOnePrime`,
  `Ring.weilOrder`, with `Ring.ord` from `Mathlib.RingTheory.OrderOfVanishing.Basic`.
  I read their complete definitions and docstrings, including the class-group
  construction used by the proof dependency.
- `Sheaf.RingTheory.CompleteToricModel`: `ToricMonoid.IsCompleteModel`, `Complete`,
  `monomial`, `completionIdeal`, `completedChartIdeal`, reusing the constructions
  of `Sheaf.RingTheory.LogRegularSaturationNormality`. Added the already landed
  definition node `def-trf-complete-toric-model` to `stmt_deps` under brief §5's
  authorization to cite landed notions. Its record is not changed.

The stated proof dependencies are imported without `public`:
`Sheaf.RingTheory.CompleteToricFacetValuations`,
`Sheaf.RingTheory.CompleteToricBoundaryClassInjectivity`, and
`Sheaf.GroupTheory.SharpConeLatticeIntersection`.
Their theorem signatures and proof docstrings were read. The remaining proof dependency
`lem-trf-normal-domain-principal-divisor-kernel` has neither a Lean record nor a
Mathlib match, so has no module to import. It is used only by the future proof,
not to define the statement's objects. The five proof steps of the item are carried
in the theorem docstring, including every cited node and the degenerate cases.

Edge cases checked before writing:

- For `P = {0}`, the only monomial is `1`; the localization is `R`, so `hf` means
  that `f` is a unit. All its height-one orders are zero, as are those of `z 0`.
  The exponent `a₀ = 0` works. No positive-rank or nonempty-facet assumption appears.
- `n = 0` is allowed because `Fin 0` is the empty variable set. Neither the
  conclusion nor the model predicate requires a parameter.
- When also `P = {0}`, the field model is the field and the Cohen quotient is
  `C/(p)`, also a field. Its set of height-one primes is empty. The nonvanishing
  conjunct is still required; it has not been lost to a vacuous valuation equality.
- `f = 0` cannot satisfy `hf`: all denominators are nonzero, so localization is
  nontrivial. Domain and monomial-nonvanishing hypotheses explicitly remain.
- For `P = ℕ` or `ℕ²`, coordinate monomials give the expected nonnegative boundary
  orders. For the saturated singular cone `0 ≤ b ≤ 2a` in `ℤ²`, the primitive
  normals are `b` and `2a-b`. Their parity constraint is retained because `a₀`
  lies in `P`; the conclusion is not merely a rational lattice lift.
- The field characteristic is unrestricted, and the Cohen residue field is not
  restricted to perfect fields. The zero ring is excluded exactly by `IsDomain`.

Searches actually run:

1. `msearch.py ... leanfinder` with query
   `In a complete saturated sharp monoid algebra or Cohen parameter quotient, any element invertible after monomial localization has the same divisor as a monomial`:
   eight hits, including `IsLocalization.algebraMap_isUnit_iff`, the away-localization
   specialization, and `exists_reduced_fraction'`. These characterize divisibility
   by a denominator or describe a reduced fraction, not the required toric divisor lift.
2. `msearch.py ... loogle` with query `"MonoidAlgebra", "IsUnit"`: zero hits.
3. `msearch.py ... grep` with query
   `toric|facet|boundary.*divisor|divisor.*boundary` in `RingTheory`: eleven unrelated
   hits, mostly combinatorics imports; no matching theorem.
4. `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for toric/localized-unit/divisor
   patterns, then the narrower `completeToric|complete_toric|localized.*monomial|monomial.*localiz`
   in their RingTheory directories. Found the existing facet, boundary-class and
   face-strata modules, and the two existing equivalent complete-model predicates;
   no existing divisor-lift theorem. Reused the facet module's `ToricMonoid` model.
5. Literal node-id grep in `lean/WeilConjectures`, and declaration-name searches in
   `dag/lean_names_upstream.json` and both source roots: no attachment for this item.
   The affinely unrelated boundary-unit descent theorem does not concern complete
   toric models. DAG searches located the existing `def-trf-complete-toric-model`
   and `def-trf-complete-toric-local-model` definitions; no definition node was added.

There is no statement dispute or correction. The prescribed `scompile.py` compiled
both sandbox and library module modes cleanly (1.6 seconds each); no unexpected
warnings. `set_option autoImplicit false` checks that all variables and universes
are explicit.

## Second reading by Q24

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
