## Worker report

The module `Sheaf.GroupTheory.PositiveMonoidLengthGrowth` states
`AddSubmonoid.positiveMonoid_length_growth`, with its entire proof `by sorry`.
The node is unchanged except for `lean`. There are no new nodes, dependency
repairs, statement corrections, or disputed clauses.

Source read: ILO, Travaux de Gabber, Exposé VI, §1.6(i)–(ii), printed p. 70
(PDF p. 76), using `pdftotext` on the provided PDF. That page supplies the formal
monoid models, not this counting theorem. The seven-step lattice-counting proof
is agent supplied as the node explicitly says; it is reproduced step by step
in the theorem docstring. I also read the current blueprint's
`sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md` and its proof:
the lattice argument is a subsidiary node, not the blueprint unit's statement.

Hypotheses and clauses, matched individually:

- Nonnegative integers `r,d`: `(r d : ℕ)`.
- A free integral lattice of rank `r`, with fixed lattice coordinates:
  `(G : Type u) [AddCommGroup G] (B : Module.Basis (Fin r) ℤ G)`.
  A basis of exactly this size expresses `G ≅ ℤ^r`, including rank zero;
  no separate freeness assumption is added, since the basis already supplies it.
- The additive submonoid and finite generation: `(P : AddSubmonoid G)` and
  `hfg : P.FG` using Mathlib's definition.
- Its generated subgroup is all of `G`:
  `hspan : AddSubgroup.closure (P : Set G) = ⊤`.
- The integral weight homomorphism and strict positivity away from zero:
  `(w : G →+ ℤ)` and `hpos : ∀ p : P, p ≠ 0 → 0 < w (p : G)`.
- The sequence on positive integers and its monotonicity:
  `(lam : ℕ+ → ℝ≥0)` and `hmono : Monotone lam`.
- Positive two-sided polynomial constants and positive threshold:
  `hgrowth` existentially quantifies `a b : ℝ≥0`, their strict positivity,
  and `k₀ : ℕ+`, followed by both inequalities for all `k ≥ k₀`.
  Positive constants in the nonnegative reals give exactly positive real
  constants, with no loss or additional condition.
- The finite attained largest decomposition length for every `p`:
  `∃ ν : P → ℕ` with `IsGreatest` of the lengths `l` admitting
  `f : Fin l → P`, all entries nonzero, and `∑ i, f i = p`.
  `ν 0 = 0` is explicit. This is a uniquely specified maximum, not an
  arbitrary function or a finite upper bound masquerading as the length.
- Finiteness of every positive length sublevel:
  `∀ n : ℕ+, Set.Finite {p : P | ν p < (n : ℕ)}`.
- The convolution is `∃ F : ℕ+ → ℝ≥0` with an equality for every `n` to
  `∑ᶠ p : {p : P // ν p < (n : ℕ)}, lam (((n : ℕ) - ν p.1).toPNat')`.
  The finite index set has just been asserted finite, so `finsum` is the
  ordinary finite sum, including zero summands. `ν p < n` makes the argument
  of `Nat.toPNat'` strictly positive, where that conversion preserves it.
  This equality completely determines `F`; no arbitrary map replaces the sum.
- Eventual two-sided growth of degree `d+r`: the existential positive
  `a' b' : ℝ≥0` and `n₀ : ℕ+` followed by the two estimates for `n ≥ n₀`.
- Rank zero: `r = 0 → P = ⊥ ∧ ∀ n : ℕ+, F n = lam n`.
  The bottom additive submonoid is precisely `{0}`.
- Positive rank and a choice of nonzero finite monoid generators:
  the `0 < r` implication first supplies such a family, then quantifies over
  every `s : ℕ`, `g : Fin s → P` with nonzero entries and ambient additive
  monoid closure of their range equal to `P`.
- Weight maximum `M`: universally quantify a natural `M` equal to
  `Finset.univ.sup (fun i ↦ (w (g i : G)).toNat)`.
  Nonzero generators have positive integer weights, and the family is
  nonempty in positive rank; hence this is exactly their integer maximum.
  For every `p`, `(w (p : G) : ℝ) / (M : ℝ) ≤ (ν p : ℝ)` and
  `(ν p : ℤ) ≤ w (p : G)` give the two stated inequalities.
- Any coordinate bound `C ≥ 1`: quantify `C : ℕ`, `1 ≤ C`, and
  `∀ i j, |B.repr (g i : G) j| ≤ (C : ℤ)`.
  Integers at least one correspond exactly to such naturals.
  `∀ n : ℕ+, Set.ncard {p : P | ν p < (n : ℕ)} ≤ (2*C*n+1)^r`
  gives the full cardinal bound, not merely finiteness or an asymptotic bound.
- Existence of `r` linearly independent generators:
  `∃ v : Fin r → Fin s, LinearIndependent ℤ (fun j ↦ (g (v j) : G))`.
  Integral independence of integer vectors is equivalent to rational
  independence by clearing denominators; it also forces distinct selections.
- Every such independent choice is covered by the following universal `v`.
  Its weight maximum `W` is specified as the supremum over the selected
  weights, again exactly the positive integer maximum.
- For every positive `n ≥ 2`, the coefficient box has type
  `Fin r → Fin ((n : ℕ) / (4*r*W) + 1)`. Its entries are precisely the
  integers from zero to the required floor. The map lands in `P` as
  `∑ j, (b j : ℕ) • g (v j)`.
  `Function.Injective` asserts injectivity, and the separately quantified
  inequality for every box tuple asserts the image's length is at most
  `(n : ℝ) / 4`, exactly as stated.
- The lower convolution estimate uses
  `(((n/(4*r*W)+1)^r : ℕ) : ℝ≥0) * lam ((n/2).toPNat') ≤ F n`.
  Natural division gives the two floors. Since `n ≥ 2`, the sequence index
  `n/2` is positive and `toPNat'` preserves it.
- The matching upper estimate `F n ≤ ((2*C*n+1)^r : ℕ) * lam n` is
  in the arbitrary-coordinate-bound clause, also for every `n ≥ 2`.
  Separating the lower estimate from `C` reflects that it does not depend
  on a coordinate bound; taking the two conjuncts yields the displayed pair.

Dependencies used:

- `def-weil-pbc-free-module`: the recorded module
  `Mathlib.LinearAlgebra.FreeModule.Basic`, declaration `Module.Free`.
  Its full signature and docstring were read at lines 42–44: freeness is
  existence of a `Module.Basis`. Here a supplied `Module.Basis (Fin r) ℤ G`
  carries the exact finite-rank information rather than merely arbitrary
  freeness. This uses the same basis notion, not a private definition.
- Proof dependency `lem-weil-span-independent-subfamily`: recorded Mathlib
  match `exists_linearIndependent'` in
  `Mathlib.LinearAlgebra.LinearIndependent.Lemmas`; full signature read.
- Proof dependency `lem-weil-dimension-span-independent-family`: recorded
  Mathlib match `finrank_span_eq_card` in
  `Mathlib.LinearAlgebra.Dimension.Constructions`; full signature read.
  These two modules are ordinary proof imports, not public statement imports.
- Other public imports provide the notions appearing in the signature:
  `Mathlib.GroupTheory.Finiteness` (`AddSubmonoid.FG`, subgroup closure),
  `Mathlib.Algebra.BigOperators.Finprod` (`finsum`),
  `Mathlib.Data.Set.Card` (`Set.ncard`),
  `Mathlib.Data.NNReal.Defs` (`NNReal`, its order and arithmetic), and
  `Mathlib.Data.PNat.Defs` (`PNat`, `Nat.toPNat'`).

Searches (all performed for this item):

- `msearch.py leanfinder`: “Polynomial growth of the convolution over a positive
  finitely generated additive lattice monoid using maximal decomposition length”.
  Eight hits: Akra–Bazzi growth, Hurwitz-kernel estimates and L-series bounds.
  None states the maximum-length monoid convolution estimates.
- `msearch.py loogle`: `AddSubmonoid, Finset.card`: zero hits.
- `msearch.py grep`: `(maximalLength|decompositionLength|length.*[Cc]onvolution|positiveMonoid)`:
  zero Mathlib hits.
- `msearch.py leansearch`: “Maximal additive decomposition length in a positive
  finitely generated submonoid and polynomial convolution growth”. Eight hits
  give free-monoid word length and finite-generation definitions/results,
  including `AddSubmonoid.FG`, but no maximum-length convolution theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for positive monoids,
  maximal/decomposition lengths and length convolution: the project has
  `Sheaf.RingTheory.PositiveMonoidConvolutionLength`, read in full. It gives
  attained maximum lengths and finite sets, plus convolution ring laws; it
  does not state polynomial growth or the generator/coordinate estimates.
  Its `ν` is existentially quantified, not an exported definition, so there
  is no existing maximum-length definition to import or duplicate here.
- Literal node-ID grep in `lean/WeilConjectures`: no match.
- Declaration-name search in both project roots, Mathlib and
  `dag/lean_names_upstream.json`: no existing
  `positiveMonoid_length_growth` declaration.

Edge cases checked against the statement and proof:

- `r = 0`: the basis is empty, `G` is zero and `P = ⊥`; the length of zero
  is zero, every positive sublevel is the singleton and `F n = lam n`.
  No positive-rank maximum or division is used in this branch.
- `d = 0`: both growth exponents and constants remain meaningful, since
  positive integers to the zeroth power are one.
- `p = 0`: the empty `Fin 0` decomposition is present; strict positivity
  prohibits every nonempty decomposition of zero.
- `n = 1`: finiteness and cardinality apply; the `n/2` sequence input is
  used only under `n ≥ 2`, so there is no illicit sequence value at zero.
- `n = 2`: the lower box may contain only its zero tuple, and `n/2 = 1`
  is a valid sequence input.
- Empty/repeated generator lists: empty lists are allowed by the syntax,
  but cannot generate the nonzero lattice in the positive-rank branch.
  Repeated generators are allowed; an independent selected family cannot
  repeat a vector. No extra distinctness/minimality assumption is imposed.
- Non-saturated positive monoids and generators with negative coordinates
  are allowed: only strict positive weight is assumed, and the coordinate
  estimate uses absolute values. There is no normality/saturation assumption.

Validation: the prescribed `scompile.py` compiled both the sandbox and actual
module name without errors or warnings. The only postponed declaration is the
named theorem above. All variables and the object universe are explicit.

## Second reading by Q41

I reopened the node and the final signature for a separate clause-by-clause
self-check. The dispatcher expressly prohibits starting another agent; this
section does not claim an independent worker review. The maintainer performs
the independent review of the delivery.

The main potential mismatches checked were: replacing the maximum by an
arbitrary bounded length (avoided by `IsGreatest`); evaluating `lam` at zero
(avoided by the strict sublevel and `n ≥ 2`); losing rank zero (explicit
`P = ⊥` and equality of sequences); and proving only eventual growth while
omitting the refined generator estimates (all present). I limited the upper
convolution inequality to `n ≥ 2`, matching the displayed pair's range, while
retaining the cardinality estimate at every positive `n`. The separate lower
and upper conjuncts apply simultaneously for every choice of generators,
independent subfamily and coordinate bound. No mathematical correction to the
node was needed. Only the compiler-facing sequence identifier and NNReal scope
needed repair during compilation; no hypothesis or conclusion changed.
