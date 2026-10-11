## Worker report

The module `Sheaf.RingTheory.IntegralIdempotentAnnihilatingPolynomial` states
`Polynomial.exists_monic_aeval_eq_zero_map_eq_of_isIdempotentElem_quotient` with a
`sorry` proof. No definition or additional node is needed. The item's `stmt_deps`
is empty; there are no recorded dependency declarations to import.

The source is [Stacks Tag 09XG](https://stacks.math.columbia.edu/tag/09XG),
More on Algebra, lemma-helper-integral. The local literature file is absent on
this machine, so I read the complete statement and proof on the official Stacks
page. It agrees with the node, including d ≥ 1. No statement correction or
STATEMENT-DISPUTED issue was found.

Hypothesis and conclusion correspondence:

- Commutative rings A and B: `{A : Type u} {B : Type v} [CommRing A] [CommRing B]`,
  with both universes explicitly declared.
- The ring map A → B: `[Algebra A B]`, whose map is `algebraMap A B`.
  A map of commutative rings induces this algebra structure; no injectivity,
  nontriviality, finiteness, or additional constraint on the map is assumed.
- B integral over A: `[Algebra.IsIntegral A B]`, meaning every element of B is
  integral over A, exactly as the node requires.
- Ideal I and element b: `(I : Ideal A) (b : B)`.
- The image of b in B/IB is idempotent: the binder `hb` uses
  `IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap A B)) b)`.
  `Ideal.map` is the extended ideal IB; `Ideal.Quotient.mk` is its quotient map;
  `IsIdempotentElem` means the image multiplied by itself equals itself.
- There exist an integer d ≥ 1 and polynomial f in A[x]:
  `∃ (d : ℕ) (f : A[X]), 1 ≤ d ∧ ...`. Positive natural numbers parametrize
  exactly the positive integer exponents in the statement.
- f is monic: `f.Monic`.
- f(b) = 0 in B: `aeval b f = 0`, using the specified algebra map.
- Reduction of f modulo I equals x^d(x-1)^d:
  `f.map (Ideal.Quotient.mk I) = (X : (A ⧸ I)[X]) ^ d * (X - 1) ^ d`.
  This is equality of polynomials over A/I, not just equality of evaluations.

Definitions read in Mathlib: `Algebra.IsIntegral` in
`Mathlib.RingTheory.IntegralClosure.Algebra.Defs`, `IsIdempotentElem` in
`Mathlib.Algebra.Group.Idempotent`, and `Ideal.Quotient.mk` in
`Mathlib.RingTheory.Ideal.Quotient.Defs`. Read the full signature and source of
`Polynomial.exists_monic_aeval_eq_zero_forall_mem_of_mem_map` in
`Mathlib.RingTheory.IntegralClosure.Algebra.Ideal` (Tag 00H5): it is the
proof ingredient named by the node, not the current statement. The module's
proof docstring reproduces all three DAG proof steps, including the degree-zero
case, and names that proof dependency.

Edge cases checked mathematically before writing:

- B the zero ring: f = X(X-1) and d = 1 satisfy all conclusions for any A.
- A the zero ring: any A-algebra B is also the zero ring; the zero polynomial is
  monic in this ring under Mathlib's definition (leading coefficient = 1 = 0).
- I = top: the quotient is the zero ring and the reduction equality is automatic;
  integrality gives an annihilator, so the statement imposes no improper ideal
  hypothesis. The positive exponent remains permitted independently of degree.
- I = bottom: b is already idempotent; f = X(X-1), d = 1 works.
- b = 0 or b = 1: the same polynomial works. No characteristic is excluded.
- No finite-degree equality is added: in a zero coefficient ring it would be
  inappropriate to require natDegree f = 2d.

Searches for existing declarations:

- `msearch.py ... leansearch "integral algebra element idempotent modulo ideal
  monic annihilating polynomial congruent X^d times (X-1)^d"`: unavailable
  (Internal Server Error); recorded as unavailable without a search verdict.
- `msearch.py ... leanfinder "integral algebra element idempotent modulo extended
  ideal monic annihilating polynomial congruent to X^d (X-1)^d"`: eight hits,
  including the three integral-over-ideal annihilator lemmas, a power-basis
  congruence, an invertible-element annihilator, a characteristic-polynomial
  lemma, and two integrality lemmas. None states the requested reduction formula.
- `msearch.py ... loogle "Polynomial.Monic, Polynomial.map, IsIdempotentElem"`:
  zero hits.
- `msearch.py ... grep "09XG|annihilating.*idempotent|idempotent.*polynomial"`:
  zero hits in Mathlib.
- `rg` over the source `WeilConjectures/`, the project's `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `integral.*idempotent|idempotent.*polynomial|09XG`
  and the item id: only unrelated Artin-Schreier interpolation and a proof
  docstring about idempotent lifting; no declaration for this statement.
- `grep -rn` of the item id in source `WeilConjectures/`: no matches.
- `rg` of `exists_monic.*idempotent|exists_monic.*map.*pow` in the source,
  `lean/Sheaf`, and upstream name index: no matches. The selected declaration
  name is therefore new.

Validation: single-file server compilation and `deliver2.py --no-push` are run
before handoff; the second reader supplies the independent second-reading section.

## Second reading by G1

I independently read the item node and its Lean module, the empty `stmt_deps`,
the proof-dependency node `lem-weil-pbc-integral-extended-ideal-element-monic`,
and its actual Mathlib declaration in IntegralClosure/Algebra/Ideal.lean.
I read the official Stacks [09XG](https://stacks.math.columbia.edu/tag/09XG)
statement and proof, then downloaded the upstream `more-algebra.tex` into
`scratchpad/more-algebra.tex` and read lines 1959–1975 and the Lifting section
preamble. No local literature checkout is present. The preamble adds no standing
Noetherian, domain, characteristic, finiteness, or proper-ideal assumption.

Independent object/hypothesis/conclusion checklist, in node order:

1. Commutative ring A: `{A : Type u} [CommRing A]`. Exact; arbitrary universe.
2. Ideal I of A: `(I : Ideal A)`. Exact; no properness assumption.
3. Ring map A → B of commutative rings: `{B : Type v} [CommRing B]
   [Algebra A B]`, with map `algebraMap A B`. Exact: every such ring homomorphism
   induces an algebra structure via `RingHom.toAlgebra`; no injectivity or
   nontriviality is imposed. Universes u and v are independent and explicitly bound.
4. B integral over A: `[Algebra.IsIntegral A B]`. Exact: its field is
   `∀ x : B, IsIntegral A x`; `algebraMap_isIntegral_iff` identifies it with
   integrality of the specified ring map. No finite-module assumption.
5. Element b of B: `(b : B)`. Exact, unconstrained except for the next hypothesis.
6. Its image in B/IB is idempotent: `hb : IsIdempotentElem
   (Ideal.Quotient.mk (I.map (algebraMap A B)) b)`. Exact: `Ideal.map` is
   the ideal spanned by the image of I (not just the set image), Quotient.mk is
   the quotient ring map, and IsIdempotentElem means multiplication by itself
   equals itself. I read all three definitions in Mathlib.
7. Exist positive integer d and polynomial f in A[x]: `∃ (d : ℕ) (f : A[X]),
   1 ≤ d ∧ ...`. Exact: positive naturals and positive integers parameterize
   the same polynomial powers. The existential order does not constrain either
   witness; both follow all hypotheses.
8. f monic: `f.Monic`. Exact: leading coefficient equals one, also for zero rings.
9. f annihilates b in B: `aeval b f = 0`. Exact evaluation via algebraMap A B;
   I read Polynomial.aeval in Algebra/Polynomial/AlgebraMap.lean.
10. Polynomial reduction modulo I is X^d(X−1)^d:
    `f.map (Ideal.Quotient.mk I) = (X : (A ⧸ I)[X]) ^ d * (X - 1) ^ d`.
    Exact equality in the polynomial ring over A/I, not just equality of values.
    Polynomial.map maps coefficients via the quotient ring homomorphism.

Edge cases: A or B may be zero rings; if A is zero then its algebra B is zero.
The polynomial X(X−1) with d = 1 works whenever B is zero, and the zero
polynomial is monic when A is zero. I = top is allowed and makes coefficient
reduction automatic; I = bottom makes b already idempotent, so X(X−1) works.
The same choice handles b = 0 and b = 1. All characteristics are covered, including
2 where subtraction still has the required meaning. d = 0 is excluded exactly
as in the source, while the proof docstring handles a degree-zero intermediate
annihilator. No natDegree = 2d condition incorrectly excludes zero rings.
Empty indexing sets and schemes are not objects of this lemma.

Independent searches used different wording from the worker:

- LeanFinder: "An integral ring extension and an element idempotent in the
  quotient admit a monic relation reducing to a power of T times a power of T
  minus one". Eight hits: the three integral-over-ideal annihilator lemmas,
  weak Eisenstein lemmas and other integrality statements. No hit gives the
  prescribed reduction polynomial. I opened the actual 00H5 declaration;
  it concerns an element already in IB and only lower coefficients in I.
- Loogle: `Polynomial.Monic, Ideal.Quotient.mk, Polynomial.map`. Two hits:
  Polynomial.generalizedEisenstein and AlgebraicClosure.Monics.map_eq_prod;
  neither states this lemma.
- msearch grep: `IsIdempotentElem.*aeval|aeval.*IsIdempotentElem|09XG|helper-integral`.
  Zero hits. Direct rg in Mathlib, source WeilConjectures, project lean/Sheaf,
  and dag/lean_names_upstream.json for `09XG|helper-integral|idempotent.*(annihilat|monic)|
  ((annihilat|monic).*idempotent)` also found no hits.
- The worker's three-kind search record includes the unavailable LeanSearch
  service; it is correctly recorded as unavailable rather than a negative result.

No new definition node, dependency module, or statement correction is present
or needed. Standard Mathlib notions suffice, with no private or hollow definition.
The sole theorem has a sorry proof, as stage 2 requires. Its source-bearing
module and declaration docstrings cover all three proof steps, including the
00H5 dependency and the degree-zero repair. Namespace, explicit universes,
imports, declaration name, and 100-character line convention are correct.
The node's lean.statement is verbatim the file signature up to `:=`.

Mismatches found: none. I changed no Lean or node content and appended only
this independent review. The prescribed single-file server compilation succeeded
in 1.3 seconds with exit code 0 and no warnings. An initial compile invocation
used a relative path from the read-only repository and failed to find the sandbox
file; rerunning with its absolute sandbox path resolved that invocation error.
