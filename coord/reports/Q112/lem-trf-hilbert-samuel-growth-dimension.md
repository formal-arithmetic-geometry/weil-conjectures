## Worker report

The module `Sheaf.RingTheory.HilbertSamuelGrowthDimension` states
`IsLocalRing.exists_hilbertSamuel_polynomial` with one `sorry`, for precisely
`lem-trf-hilbert-samuel-growth-dimension`. No definitions, extra nodes, dependency
repairs, or statement changes are needed.

Source read: `literature/stacks-project/algebra.tex`,
`proposition-hilbert-function-polynomial` (00K8, lines 14148--14168), and
`proposition-dimension` (00KQ, lines 14520--14611). The former gives eventual
polynomiality for the cumulative length function, the latter its degree. The
node explicitly shifts the source exponent `n+1` to `n`; the Lean uses `n`.
The module docstring identifies both source places and the declaration docstring
carries all seven proof steps, including the explicit Artin--Rees length estimate
and prime-chain induction.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A commutative ring of any universe is `(R : Type u) [CommRing R]`, with `universe u`
  explicitly declared. `[IsNoetherianRing R]` is the recorded Noetherian predicate.
- A nonzero local ring is `[IsLocalRing R]`: its full definition in
  `Mathlib.RingTheory.LocalRing.Defs` extends `Nontrivial R`, so no extra nonzero
  hypothesis or characteristic assumption is needed. The specified maximal ideal
  is `IsLocalRing.maximalIdeal R`, the ideal of nonunits.
- The existential rational polynomial is `∃ Q : Polynomial ℚ`, and nonzero is
  `Q ≠ 0`. No particular polynomial is supplied as data by a definition.
- Strict positivity of its leading coefficient is `0 < Q.leadingCoeff` in `ℚ`.
- Its degree is `(Q.natDegree : WithBot ℕ∞) = ringKrullDim R`.
  The separate nonzero clause makes `natDegree` the polynomial's actual degree;
  the cast is the natural finite integer in the codomain of `ringKrullDim`.
  This clause also includes finiteness of the ring's dimension as a conclusion.
- The integer threshold at least one is `∃ N : ℕ, 1 ≤ N`.
  Every integer at least this positive threshold is a natural number, so the
  quantifier `∀ n : ℕ, N ≤ n →` gives exactly the requested integer range.
- `R ⧸ (maximalIdeal R) ^ n` is the quotient by the nth power of the actual
  maximal ideal, with its canonical `R`-module structure.
- Finite composition length is
  `Module.length R (R ⧸ (maximalIdeal R) ^ n) < ⊤`.
  By the recorded length node and `Module.length_ne_top_iff`, this is finite
  composition length in exactly the node's sense.
- Equality to the polynomial is
  `((Module.length R (R ⧸ (maximalIdeal R) ^ n)).toNat : ℚ) = Q.eval (n : ℚ)`.
  The preceding strict inequality rules out infinity, so `ENat.toNat` is precisely
  the finite integer length, faithfully embedded in the rationals. There is no
  equality asserted outside the requested eventual range.

Statement dependencies used, with their full signatures and docstrings read:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`, the abbreviation `IsNoetherian R R`; the same source's
  `isNoetherianRing_iff_ideal_fg` spells out finite generation of every ideal.
- `def-weil-pbc-module-length`: `Mathlib.RingTheory.Length`, `Module.length`.
  This is the Krull dimension of the submodule lattice, valued in `ℕ∞`.
  The source's `Module.length_ne_top_iff` identifies finite composition length.
- `def-weil-pbc-krull-dimension-ring`:
  `Mathlib.RingTheory.KrullDimension.Basic`, `ringKrullDim`, the Krull dimension
  of the prime spectrum ordered by inclusion, valued in `WithBot ℕ∞`.

The module publicly imports these recorded statement-dependency modules and the
Mathlib polynomial, rational, and maximal-ideal interfaces used by the signature.
The stated proof dependencies are imported without `public`:
`WeilConjectures.RingTheory.GradedAlgebra.Standard` for
`GradedAlgebra.IsStandard`, `Mathlib.RingTheory.Ideal.KrullsHeightTheorem` and
`Mathlib.RingTheory.LocalRing.Quotient` for the system-of-parameters interfaces,
and `Mathlib.RingTheory.Filtration` for `Ideal.exists_pow_inf_eq_pow_smul`.
Length additivity is already in the public `Length` module as
`Module.length_eq_add_of_exact`. These declarations' source signatures were read.
The proof dependency `lem-trf-standard-graded-hilbert-function` currently has
neither a Lean record nor a Mathlib match; it has no module to import. It is only
used in the future proof, and no missing notion is required to state this item.
Its eventual proof import is left to the maintainer when that node is stated.

Edge cases checked before writing:

- A field has maximal ideal zero, `Q = 1`, and dimension zero, with threshold one.
  Thus constants and dimension zero must be allowed, and are.
- For a nonreduced Artinian local ring the powers of the maximal ideal eventually
  vanish; the eventual polynomial is the positive constant `length_R R`.
- In a discrete valuation ring, the length is `n`, so `Q = X`, with exponent `n`.
  For a two-variable formal power series ring over a field the length is
  `n(n+1)/2`, checking the same exponent convention in dimension two.
- `n = 0` is outside the claimed range because `N ≥ 1`; there is no spurious
  demand that the positive constant field polynomial equal the zero quotient's
  length at zero.
- The zero ring is excluded by precisely the stated nonzero local hypothesis;
  positive and mixed characteristics are included. No domain, residue-field,
  completeness, equicharacteristic, or regularity hypothesis was added.
- Rings of arbitrary universe `u` are covered. A finite degree is concluded, not
  assumed separately. No polynomial-degree convention loses the degree-zero case.

Searches for an existing statement (all actually run with `msearch.py Q112
lem-trf-hilbert-samuel-growth-dimension`):

- LeanFinder: “For a nonzero Noetherian local ring the length of its quotient by
  the nth power of its maximal ideal is eventually a rational polynomial with
  positive leading coefficient and degree equal to Krull dimension”. Eight hits,
  all dimension/regular-element quotient inequalities or finite-length results;
  no eventual length polynomial theorem.
- LeanSearch: “Hilbert Samuel polynomial length quotient maximal ideal powers
  degree Krull dimension”. Eight hits, including `ringKrullDim`, quotient bounds,
  and `Polynomial.hilbertPoly`; no match to the claimed result.
- Loogle: `"Hilbert", "length"`. Zero hits.
- Mathlib grep under `RingTheory`:
  `HilbertSamuel|hilbert.*samuel|samuel.*hilbert|length.*polynomial|polynomial.*length`.
  Zero hits.
- Read `Mathlib/RingTheory/Polynomial/HilbertPoly.lean` lines 18--42 and the
  definition following them. `Polynomial.hilbertPoly` concerns coefficients of
  a rational formal series, and explicitly lists the Hilbert polynomial of a
  graded module as TODO. It is not this statement or a one-line specialization.
- Direct `rg` of `WeilConjectures/`, `lean/Sheaf/`, and
  `dag/lean_names_upstream.json` for Hilbert--Samuel/length-polynomial patterns
  and the item id found no existing declaration for this statement. The few
  word-order matches concerned unrelated cohomology or regular sequences.
- A direct name search for `exists_hilbertSamuel_polynomial` in Mathlib, upstream,
  and `lean/Sheaf` found no collision.

No statement dispute or node fault was found. The node copy changes only `lean`,
with the verbatim signature, branch `newtargets-dag`, and actual UTC date.

Validation: `scompile.py` compiled both its sandbox probe and the actual library
module successfully with no diagnostics (2.0 s and 7.2 s respectively). The first
compile identified a missing public polynomial-degree import; adding
`Mathlib.Algebra.Polynomial.Degree.Defs` fixed it without changing the signature.
A local packet check confirmed only the node's `lean` field changed, its signature
is verbatim, every module line is at most 100 characters, and the only postponed
proof is the named theorem's complete `sorry` proof.

## Second reading by Q112

Independent second reading verified the item node, Stacks source places 00K8 and 00KQ,
all three statement dependencies and their exact Lean declarations, and the delivered
module signature clause by clause. `[IsLocalRing R]` supplies nontriviality, the
natural-number threshold expresses the requested integer range with `N ≥ 1`, and
`Module.length < ⊤` plus `toNat` gives finite composition length. The polynomial
nonzero/positive-leading-coefficient and degree clauses match the node exactly,
including the degree-zero, field, Artinian, and arbitrary-universe cases. No extra
Noetherian, domain, characteristic, completeness, or regularity hypothesis occurs.
The source-based proof plan and docstrings were checked for all seven steps; the
unrecorded future proof dependency `lem-trf-standard-graded-hilbert-function` is
used only by the postponed proof and does not alter this statement. Searches found
no duplicate declaration, and no route-pivot machinery or pro-etale substitute is
present. The immutable module was independently compiled with `scompile.py` for
both sandbox and library passes (exit 0; no diagnostics beyond permitted `sorry`).
