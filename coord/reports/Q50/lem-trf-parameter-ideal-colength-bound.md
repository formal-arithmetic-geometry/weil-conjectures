## Worker report

The module `Sheaf.RingTheory.ParameterIdealColengthBound` states
`IsLocalRing.parameterIdeal_colength_bound`, with its sole proof `sorry`.
No definition or auxiliary theorem is introduced. The natural-language statement,
proof and proof dependencies are unchanged. I read Stacks `algebra.tex`, Tag 00KQ,
`proposition-dimension`, specifically its parameter-monomial paragraph, and the
seven steps of the accepted node split. The theorem docstring records all seven
steps, including the separate nilpotent case and the length-additivity arguments.
No mathematical fault or disputed statement was found.

Hypothesis and conclusion correspondence:

- The arbitrary commutative nonzero Noetherian local ring is `R : Type u` with
  `[CommRing R] [IsNoetherianRing R] [IsLocalRing R]`. Mathlib's `IsLocalRing`
  extends `Nontrivial R`; no redundant nonzero hypothesis is needed. The universe
  `u` is explicit and unrestricted.
- The nonnegative number of parameters is `d : ℕ`; the ordered parameter family
  is `x : Fin d → R`. Its containment in the maximal ideal is
  `hx : ∀ j : Fin d, x j ∈ maximalIdeal R`.
- `J : Ideal R` together with `hJ : J = Ideal.span (Set.range x)` specifies exactly
  the generated ideal. This allows empty, repeated and zero parameters.
- The integer `a ≥ 1` is `a : ℕ` with `ha : 1 ≤ a`, and the power containment is
  `haJ : (maximalIdeal R) ^ a ≤ J`.
- `L : ℕ∞`, `hL : Module.length R (R ⧸ J) = L`, and `hLfin : L < ⊤` give exactly
  the stated finite colength, using the recorded definition of module length.
- The positive-generator assertions are guarded by `1 ≤ d →`. For each `i : ℕ`,
  the existential `e` is an equivalence between
  `Fin (Nat.choose (i + d - 1) (d - 1))` and the subtype of exponent families
  `f : Fin d → ℕ` satisfying `∑ j : Fin d, f j = i`. Thus every formal monomial
  occurs once, regardless of coincidences among its values in the ring.
- `b` lifts these monomials into `J ^ i`; its defining equality is
  `∀ k, (b k : R) = ∏ j : Fin d, x j ^ (e k).val j`.
  These existential lifts are only a way to write the actual elements of the
  subtype ideal; they add no independent mathematical condition.
- `q` is an `R`-linear map from the finite product of the indicated binomial
  number of copies of `R ⧸ J` to `Ideal.associatedGradedPiece J i`.
  A product over this finite index is the same module as its finite direct sum.
  The codomain is the existing quotient of `J^i` by the comap of `J^(i+1)`.
  `Function.Surjective q` is the requested surjectivity. For every coordinate `k`
  and every representative `r : R`, the component formula
  `q (Pi.single k (Ideal.Quotient.mk J r)) = r • Submodule.Quotient.mk (b k)`
  specifies multiplication by that coordinate's monomial. It constrains actual
  residue classes and actual quotient classes; no arbitrary surjection replaces
  the requested monomial map.
- `∀ n : ℕ, 1 ≤ n →` introduces all positive powers. The first two conjuncts
  assert `Module.length` less than `⊤` for `R/m^n` and `R/J^n`. The next two
  give respectively `length(R/m^n) ≤ length(R/J^n)` and
  `length(R/J^n) ≤ L * (Nat.choose (n + d - 1) d : ℕ∞)`.
- The zero-generator case is guarded by `d = 0 →`. It states `J = ⊥`,
  `(maximalIdeal R) ^ a = ⊥`, `Module.length R R < ⊤`,
  `Module.length R R = L`, and equality of `length(R/m^n)` with `L` for every
  `n : ℕ` satisfying `a ≤ n`. Thus all clauses of the node's zero case are present.

Dependencies read and used:

- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` from
  `Mathlib.RingTheory.Noetherian.Defs`, the abbreviation `IsNoetherian R R`,
  whose ideal interpretation is recorded in `isNoetherianRing_iff_ideal_fg`.
- `def-weil-pbc-module-length`: its Mathlib match `Module.length` from
  `Mathlib.RingTheory.Length`, valued in `ℕ∞` and defined from the Krull dimension
  of the submodule lattice. Finiteness is exactly length less than infinity.
- `lem-weil-pbc-length-additive-short-exact`: its Mathlib match
  `Module.length_eq_add_of_exact`, in the same imported Length module. I read its
  full signature: injective `f`, surjective `g`, and `Function.Exact f g` give
  length of the middle module equal to the sum of the two others. This is the
  proof dependency for the source/kernel sequences and the power filtration;
  no additional import is needed since Length is already a statement import.
- The already landed `def-weil-pbc-associated-graded-ring` is added to `stmt_deps`
  to use its recorded `Ideal.associatedGradedPiece` in
  `WeilConjectures.RingTheory.AssociatedGradedRing`. I read that abbreviation's
  signature and docstring: `(J ^ i) ⧸ Submodule.comap (J ^ i).subtype (J ^ (i+1))`.
  It is precisely the quotient needed here, and avoids creating a second notion.
  This is an existing-node addition under the stage-2 landed-node rule, not a new
  node or a statement correction. That node file itself is untouched.
- Remaining public imports give the local maximal ideal and `Nat.choose`.

Edge cases checked before writing:

- `d = 0`: the image of the empty parameter family is empty and its span is zero.
  The hypothesis forces `m^a = 0`; stabilization starts at `a`, not at every
  positive power. For example `R = k[t]/(t^a)` has `length(R/m^n) = min(n,a)`.
- `d = 1`: both the monomial count `choose(i,0)` and the cumulative count
  `choose(n,1)` have the expected values one and `n`.
- `i = 0`: the sole exponent tuple is zero, its monomial is one, `J^0 = R`, and
  the map has a single copy of `R/J` mapping to the zero-degree quotient.
- `n = 1`: the upper bound is `L * choose(d,d) = L`, so it is equality for `R/J`;
  the lower bound comes from the quotient map to `R/m`.
- Repeated parameters, zero parameters and zero divisors are retained. For a field
  with all parameters zero and positive `d`, the positive-degree targets vanish
  and the length bound still holds. Surjectivity never requires distinct or
  nonzero monomial values.
- Infinite residue fields, arbitrary characteristic, and nonreduced local rings
  are included; no cardinal finiteness or domain hypothesis is introduced.

Searches actually run:

- `msearch.py` LeanFinder query: "Binomial colength bound for powers of an ideal
  generated by d elements and degree i monomial surjection". Eight hits, including
  `Ideal.index_pow_le`, `Ideal.mul_add_mem_pow_succ_inj`, and
  `Ideal.span_pow_eq_map_homogeneousSubmodule`. The last describes generation by
  homogeneous polynomials, but none states this module-length theorem with its
  component formula, binomial bounds and zero-generator case.
- `msearch.py` Loogle query: `"length", "choose"`. Zero hits.
- `msearch.py` grep query: `length.*choose|choose.*length|length.*pow|pow.*length`
  in `RingTheory`. Four hits: Length line 271 (free-module length),
  Ramification line 155, and DVR Basic lines 555 and 557. The DVR computation
  specializes the ring and is not the requested general statement.
- `msearch.py` LeanSearch query: "Length of quotients by powers of finitely
  generated ideals bounded by binomial coefficients". Eight hits including
  `Ideal.index_pow_le`, `Ideal.finite_quotient_pow`, and
  `Ideal.Quotient.factorPow`. Cardinal finiteness/index are different from
  finite composition length, and none provides this statement.
- `rg` on the project and upstream sources for parameter ideals, monomial
  surjectivity, colength, `length.*choose`, and `choose.*length` found the
  downstream Hilbert--Samuel docstring and specialized related material, but
  no existing declaration of this result. Searching the exact node id in
  `lean/WeilConjectures` returned no hit. A name search for
  `parameterIdeal_colength_bound` in Mathlib, upstream and `Sheaf` found no clash.
- The search for `associatedGradedPiece` found the existing upstream abbreviation;
  its DAG record was located by the associated-graded-ring filename search.
  Thus no new helper definition or node is needed.

Validation: the prescribed `scompile.py Q50 lem-trf-parameter-ideal-colength-bound`
compiled this module in module mode, both its sandbox probe and its library-name
probe, cleanly with no errors or warnings. Every variable and universe is explicitly
bound, `autoImplicit` is false, all lines are at most 100 characters, and the only
postponed proof is the named theorem matching this node.

## Second reading by Q50

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
