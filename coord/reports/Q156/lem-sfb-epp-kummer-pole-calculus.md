## Worker report

The module `Sheaf.RingTheory.KummerPoleCalculus` states
`IsDiscreteValuationRing.kummer_pole_calculus`, with one `sorry` and no new definitions.
The node's statement and dependency lists are unchanged. No correction or disputed
statement is needed. Read sources: Stacks `more-algebra.tex`, `lemma-prepare`
(Tag 09F2, lines 34977–35014), and `lemma-lowering-the-level` (Tag 09F5,
especially equations `first-congruence` and `second-congruence`, lines 35165–35212).
The source's printed `pi^(-n) P(z)` typo is already corrected in the supplied node;
the delivery uses its explicit sufficient bound on `ord c`.

The valuation is Mathlib's canonical normalized maximal-ideal valuation. Write
`ord x = -WithZero.log (v x)` for nonzero x. Its multiplicative value is
`v x = WithZero.exp (-ord x)`, so `ord x ≥ m` is expressed by
`v x ≤ WithZero.exp (-m)`. At zero the multiplicative value is zero, below every
positive exponential threshold; this encodes `ord 0 = +∞` without using the
finite-valued `WithZero.log 0`. No independent valuation hypothesis is imposed.
The equality binders `hw`, `hv`, `he` introduce exactly the node's defined objects,
with no file-local notation, let binders, chosen constructions, or helper notions.

Hypothesis and clause correspondence:

- A DVR R: `[CommRing R] [IsDomain R] [IsDiscreteValuationRing R]`.
- Fraction field F: `[Field F] [Algebra R F] [IsFractionRing R F]`.
- Characteristic zero of F: `[CharZero F]`.
- Prime residue characteristic p: `(p : ℕ) (hp : p.Prime)` and
  `[CharP (IsLocalRing.ResidueField R) p]`.
- Exact order p of ζ: `(ζ : R) (hζ : IsPrimitiveRoot ζ p)`; read its definition
  `pow_eq_one` and `dvd_of_pow_eq_one`, not merely a p-th root condition.
- w = 1 - ζ: `(w : R) (hw : w = 1 - ζ)`.
- Normalized valuation: `(v : Valuation F ℤᵐ⁰)` with
  `hv : v = (maximalIdeal R).valuation F`. This is the same valuation used by the
  recorded `dvr_valuation_ring_characterization`, with a uniformizer of value
  `WithZero.exp (-1)` and hence additive value one.
- e = ord w and e > 0: the integer equality `he` and first conclusion `0 < e`.
  In particular the conclusion also ensures w is nonzero; no such assumption was added.
- The quotient polynomial in R[T]: `∃ P : Polynomial R` whose image under the
  injective `algebraMap R F` is exactly `C ((w^p)⁻¹) * ((1 + C w * X)^p - 1)`.
  This asserts integrality of the specified polynomial, without selecting arbitrary data.
- Monicity: `P.Monic`.
- Shape and all coefficient congruences: `∃ a : ℕ → R`, with
  `∀ i, 1 ≤ i → i < p → a i ∈ Ideal.span {w}` and the exact equality
  `P = X^p - X + ∑ i ∈ Finset.Ico 1 p, C (a i) * X^i`.
  Values of the coefficient family outside that range impose no condition.
- ord(p) = (p-1)e: `v (p : F) = WithZero.exp (-((p : ℤ) - 1) * e)`.
- The polynomial identity: equality in `MvPolynomial (Fin 2) R`, substituting
  `X 0 + X 1 + C w * X 0 * X 1` using `P.eval₂ MvPolynomial.C`, with the
  exact right side `P(X 0) + P(X 1) + C (w^p) * P(X 0) * P(X 1)`.
  It is a polynomial identity over R, not just an equality at F-valued points.
- Every integer 0 ≤ n < pe: `∀ n : ℤ, 0 ≤ n → n < (p : ℤ) * e → ...`.
- Every c with ord(c) ≥ -n/p: `∀ c : F, v c ^ p ≤ WithZero.exp n → ...`.
  As p is positive, this is exactly p*ord(c) ≥ -n, including c = 0.
  No integer division or truncation of the rational bound occurs.
- ord(P(c)) ≥ -n: `v (P.eval₂ (algebraMap R F) c) ≤ WithZero.exp n`.
- ord(P(c) - (c^p-c)) ≥ e-n: the next conjunct has threshold
  `WithZero.exp (n - e)` and precisely that difference as its argument.
- ord(wc) > 0: `v (algebraMap R F w * c) < 1`.
- All x,y with ord(x),ord(y) ≥ -n: independent quantifiers over x,y and two
  `v ... ≤ WithZero.exp n` premises. The conclusion has argument `w^p * x * y`
  and threshold `WithZero.exp (2*n - (p : ℤ)*e)`, exactly ord ≥ pe-2n.
  This clause is independent of the existence or bound of c.
- Any field extension E/F: `∀ (E : Type t) [Field E] [Algebra F E]` with an
  independent universe t; no finite, algebraic, separable, or degree restriction.
- Any z and c with 1+wc nonzero: `(z : E) (c : F)` and the explicit F-valued
  nonzero premise. This last clause is outside the n/c pole-bound quantifiers,
  as in the node's final proof step, and covers all c with this premise.
- F(z+c+wzc) = F(z): equality of `IntermediateField.adjoin F` of the two singleton
  sets; each F and R coefficient is embedded by the specified algebra maps.

Dependencies used, with their signatures and docstrings read:

- `def-sc-discrete-valuation-ring`: `IsDiscreteValuationRing`,
  `Mathlib.RingTheory.DiscreteValuationRing.Basic` (imported publicly through
  `Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing`). Its class is
  precisely a local PID domain with nonzero maximal ideal; the same module's
  `irreducible_iff_uniformizer` supplies the uniformizer convention.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`, publicly
  imported and used for both R→F and F→E.
- `def-weil-polynomial-ring`: `Polynomial`, `Mathlib.Algebra.Polynomial.Basic`,
  publicly imported; the same finitely supported coefficient polynomial type is used.
- Proof-only imports: `WeilConjectures.Mathlib.Algebra.CharP.Lemmas`
  (`iterateFrobeniusOfPrime`, the recorded `def-weil-ring-frobenius` interface);
  `Mathlib.Data.Nat.Choose.Sum` (`add_pow`, recorded binomial expansion);
  `Sheaf.RingTheory.DVRValuationRingCharacterization`
  (`IsDiscreteValuationRing.dvr_valuation_ring_characterization`).
- Other proof dependencies are Mathlib leaves already available from the valuation
  import: `AddValuation.map_mul`, `map_pow`, `map_add_of_distinct_val`, and
  `IsDiscreteValuationRing.exists_lift_of_le_one`. The complete seven-step proof
  is copied in mathematical form into the theorem docstring.

Edge cases checked before writing: p = 2 has ζ = -1 and P(T) = T²+T, whose error
coefficient relative to T²-T is 2 = w; the range `Ico 1 2` includes that coefficient.
At n = 0 the c bound means integral c and the error has order ≥ e. Zero c, zero
x or y, P(c) = 0, and a zero error all satisfy the multiplicative bounds. The
strict upper endpoint n < pe is retained and is what gives ord(wc)>0. Negative
integers n are explicitly excluded, and 2n-pe may have either sign in the group
exponential. The final equality allows z = 0 and E = F. The forbidden affine
collapse 1+wc = 0 is excluded exactly by its given hypothesis. No completeness,
Henselian property, perfect residue field, chosen uniformizer, or algebraicity
hypothesis has been introduced. The universes of R,F,E are independently explicit.

Searches actually run using the authorized msearch wrapper (see searches.jsonl):

- LeanFinder: `Kummer polynomial ((1+(1-zeta)*T)^p-1)/(1-zeta)^p integral
  coefficients valuation estimates in a discrete valuation ring`: 8 hits, including
  Eisenstein cyclotomic translates, `Polynomial.int_coeff_of_cyclotomic'`, and
  generic polynomial valuation lemmas; none states these coefficient and pole clauses.
- Loogle: `IsPrimitiveRoot, Polynomial`: 12 hits, including primitive-root polynomial
  factorizations and cyclotomic results; no exact match.
- LeanSearch: `Kummer polynomial mixed characteristic discrete valuation ring
  primitive root of unity pole bounds`: 8 hits about cyclotomic minimal polynomials
  and primitive roots; no exact match.
- Mathlib grep: `kummer|Kummer|addValuation|additiveValuation` under
  `RingTheory/DiscreteValuationRing`: 5 hits, all concerning `addVal R` on the
  ring itself. The fraction-field valuation used here already exists as
  `(maximalIdeal R).valuation F`.
- Local rg of `lean/Sheaf/RingTheory`, `lean/Sheaf/FieldTheory`,
  `lean/WeilConjectures/RingTheory`, `lean/WeilConjectures/FieldTheory`, and
  `lean/WeilConjectures/Mathlib/RingTheory` found other Kummer and normalized
  valuation material, but no statement of this calculus. Searching the item id
  in `lean/WeilConjectures` returned no occurrence. Searching the proposed declaration
  and “Kummer pole” in both library trees and `dag/lean_names_upstream.json`
  returned no existing declaration. Read the recorded characterization module and
  the Mathlib primitive-root, field-adjoin, polynomial, and valuation declarations.

Validation: scompile.py compiled both the sandbox and final library-module form
cleanly (3.7 and 2.7 seconds). The initial parser diagnostic for `ℤᵐ⁰` was repaired
by opening Mathlib's existing `WithZero` scope. No diagnostic probes remain.

## Second reading by Q156

Independent clause-by-clause reading of the delivered statement against the node, its
three stmt_dep records and Stacks `more-algebra.tex` (`lemma-prepare`, Tag 09F2;
`lemma-lowering-the-level`, Tag 09F5, equations `first-congruence` and
`second-congruence`). It was supplied by the maintainer's second reader; the delivery's
own section said it was a second pass by the same worker.

Write `ord x = -WithZero.log (v x)`. For nonzero x, `v x = WithZero.exp (-ord x)`, and
`v 0 = 0` lies below every `WithZero.exp m`. So `v x ≤ exp(-m)` is exactly `ord x ≥ m`
(true for x = 0), and `v x < 1` is exactly `ord x > 0`.

1. R a DVR [def-sc-discrete-valuation-ring]: `[CommRing R] [IsDomain R]
   [IsDiscreteValuationRing R]`, the recorded Mathlib class. Correct.
2. F its fraction field [def-pc-field-extension]: `[Field F] [Algebra R F]
   [IsFractionRing R F]`. Correct.
3. char F = 0 and residue characteristic a prime p: `[CharZero F]`, `hp : p.Prime`,
   `[CharP (IsLocalRing.ResidueField R) p]`. Correct, nothing stronger: no completeness,
   Henselian, perfect-residue or finiteness assumption.
4. ζ ∈ R of multiplicative order p: `hζ : IsPrimitiveRoot ζ p`, which means exact
   order p. Correct.
5. w = 1 - ζ: `hw`. Correct.
6. v the valuation normalized on a uniformizer, v(0) = +∞:
   `hv : v = (maximalIdeal R).valuation F`. This is the HeightOneSpectrum adic valuation
   of `IsDiscreteValuationRing.maximalIdeal`. It is the same convention as the landed
   `dvr_valuation_ring_characterization`, which gives `-log v(t) = 1` for a generator t
   of the maximal ideal. Correct.
7. e = v(w) > 0: `he : e = -WithZero.log (v (algebraMap R F w))` and the conjunct
   `0 < e`. Correct. (If w = 0 this would give e = 0, so the conjunct also asserts w ≠ 0,
   which the hypotheses force.)
8. P = ((1+wT)^p - 1)/w^p lies in R[T] [def-weil-polynomial-ring]: `∃ P : Polynomial R`
   with `P.map (algebraMap R F) = C ((w^p)⁻¹) * ((1 + C w * X)^p - 1)`. Because R → F is
   injective, P is the node's polynomial and nothing is chosen. Correct.
9. Monic, and P = T^p - T + Σ_{1≤i<p} a_i T^i with a_i ∈ wR: `P.Monic` and
   `∃ a : ℕ → R` with `a i ∈ Ideal.span {w}` for `1 ≤ i < p` and the exact equality over
   `Finset.Ico 1 p`. Correct. For p = 2: P = T² + T, a_1 = 2 = w.
10. v(p) = (p-1)e: `v (p : F) = WithZero.exp (-((p : ℤ) - 1) * e)`, which parses as
    `exp((-(p-1))·e)`, i.e. ord p = (p-1)e. Correct.
11. P(X+Y+wXY) = P(X) + P(Y) + w^p P(X)P(Y): an equality in `MvPolynomial (Fin 2) R`
    via `P.eval₂ MvPolynomial.C`, with exactly these terms. This is the source's identity
    in A[z_1,z_2]. Correct.
12. ∀ integers 0 ≤ n < pe: `∀ n : ℤ, 0 ≤ n → n < (p : ℤ) * e →`. Correct.
13. c ∈ F with v(c) ≥ -n/p: `v c ^ p ≤ WithZero.exp n`, i.e. -p·ord c ≤ n. This is exact
    for a rational bound and includes c = 0. Correct.
14. v(P(c)) ≥ -n: `≤ exp n`. v(P(c) - (c^p - c)) ≥ e - n: `≤ exp (n - e)`.
    v(wc) > 0: `v (w * c) < 1`. Correct; these are the first congruence with the
    π^n P(c) correction recorded in the node's source field.
15. x, y with v(x), v(y) ≥ -n give v(w^p x y) ≥ pe - 2n: independent `∀ x y` under the
    same n, with `≤ exp (2n - pe)`. This is the second congruence. Correct.
16. Any field extension E/F, z ∈ E, 1 + wc ≠ 0 ⇒ F(z + c + wzc) = F(z):
    `∀ (E : Type t) [Field E] [Algebra F E] (z : E) (c : F)`, the nonzero premise in F,
    and an equality of `IntermediateField.adjoin F` on singletons. It holds for every c
    with this premise, as in the node's final proof step, and has no algebraicity or size
    restriction. Correct.

Edge cases checked: p = 2 (ζ = -1, w = 2, a_1 = 2 ∈ wR, covered by `Ico 1 2`); n = 0
(integral c, error order ≥ e); c = 0, x = 0 or y = 0 (v = 0 below every threshold);
2n - pe of either sign; the strict bound n < pe, which is needed for ord(wc) > 0
(n = pe, c = -1/w gives 1 + wc = 0); z = 0 and E = F. R, F and E have independent
universes u, v and t.

Mathematics checked: (1-ζ)^p ≡ 0 in the residue field gives e > 0; pU = (-1)^p w^{p-1}
with U ∈ 1+wR gives ord p = (p-1)e and u = p/w^{p-1} ≡ -1 mod w (Wilson), so
a_1 = u + 1 ∈ wR; the identity comes from 1 + wS = (1+wX)(1+wY); the pole estimate is
e + i·ord c ≥ e - in/p ≥ e - n for 1 ≤ i < p.

Records: the item differs from the base only in `lean`. The record has every key and its
`statement` is verbatim the file's signature. stmt_deps are unchanged and all three
recorded declarations are used. The plain imports are the recorded lean modules of
proof_deps def-weil-ring-frobenius, lem-pur-commutative-ring-binomial-expansion and
lem-sc-dvr-valuation-ring-characterization, as brief-stage2 §3 asks. No line is over
100 characters. The module docstring and the theorem docstring give the source place,
`(blueprint: …)` and the seven proof steps. There is one `sorry` and no definition.

Searches: the declaration name, "Kummer pole", 09F2/09F5 and `lemma-prepare` in
side-live `lean/` and slopmaster2 `WeilConjectures/` returned no existing statement of
this calculus.

No mismatch was found. Only this section was replaced.
