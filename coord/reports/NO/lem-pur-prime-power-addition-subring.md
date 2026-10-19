## Worker report

The module `Sheaf.RingTheory.PrimePowerAdditionSubring` states
`Subring.exists_prime_pow_add_mem`, with `sorry` as its entire proof. No definition,
extra node, dependency module, or statement correction is needed.

Hypothesis and conclusion correspondence:

- A commutative ring C: `{C : Type u} [CommRing C]`, for an explicitly bound arbitrary universe u.
- A unital subring A of C: `(A : Subring C)`. Mathlib's structure extends
  `Subsemiring C` and `AddSubgroup C`, hence contains 1 and is closed under addition,
  multiplication, and additive inverses, exactly as the node requires.
- A prime integer p: `{p : ℕ} (hp : p.Prime)`. Here prime means a positive prime number,
  as in Stacks Tag 0545; this is the canonical natural-number encoding of that integer.
- Elements x,y of C: `{x y : C}`.
- Positive integers n,m: `{n m : ℕ} (hn : 0 < n) (hm : 0 < m)`.
  Positive integers and positive naturals are the same exponent range.
- The four membership hypotheses, in node order: `hx : x ^ (p ^ n) ∈ A`,
  `hpx : (p : C) ^ n * x ∈ A`, `hy : y ^ (p ^ m) ∈ A`, and
  `hpy : (p : C) ^ m * y ∈ A`.
- Existence of one positive integer a: `∃ a : ℕ, 0 < a ∧ ...`.
- Both required memberships for that same a:
  `(x + y) ^ (p ^ a) ∈ A ∧ (p : C) ^ a * (x + y) ∈ A`.
- The integer-multiple convention is rendered by natural casts and multiplication in C.
  For the nonnegative integers p^n, p^m, and p^a, this equals casting through ℤ by the
  canonical ℤ-algebra structure, sending k to k times 1. The canonical cast preserves
  powers; no arbitrary or extra algebra structure is assumed.

Dependencies read and used:

- `def-weil-pbc-algebra-hom-quotient` is a Mathlib leaf, not a missing Lean record.
  Its recorded declarations were read in `Mathlib.Algebra.Algebra.Hom` (`AlgHom`),
  `Mathlib.RingTheory.Ideal.Quotient.Operations` (`Ideal.Quotient.algebra`,
  `Ideal.Quotient.mkₐ`), and `Mathlib.RingTheory.Ideal.Operations`
  (`IdemCommSemiring (Ideal R)`). This item uses only the ambient commutative ring and
  its canonical integer casts; quotient algebras, general algebra homomorphisms,
  and ideal products do not occur, so their modules are not imported unnecessarily.
- `Mathlib.Algebra.Ring.Subring.Defs`, `Subring`: existing definition used directly.
- `Mathlib.Data.Nat.Prime.Defs`, `Nat.Prime`: existing primality predicate used directly.
- Proof-only import `Mathlib.Data.Nat.Choose.Sum`, `add_pow`, is the recorded match of
  `lem-pur-commutative-ring-binomial-expansion`; its full signature and docstring were read.
- Proof-only import `Mathlib.RingTheory.WittVector.Frobenius`,
  `WittVector.map_frobeniusPoly.key₁`, is the recorded match of
  `lem-pur-prime-power-binomial-divisibility`; its signature and enclosing prime `Fact`
  context were read. A future proof supplies the Fact from hp and sets j=k-1.

Source checked: `literature/stacks-project/algebra.tex`, label
`lemma-help-with-powers` (Tag 0545). Its polynomial subring identity evaluates in any
commutative ring and hence gives this arbitrary-subring formulation. The docstring
carries all four node proof steps: explicit a and bound B, binomial expansion and
remainders, coefficient divisibility including both nonzero-remainder cases, and
reassembly into a finite sum of products of the four given subring elements.

Edge cases checked before writing: the zero ring is included (no Nontrivial or domain
assumption); all characteristics including p and mixed characteristic are included;
A may be the bottom or top subring; x or y may be zero, and x+y may vanish.
The smallest allowed prime is 2 and the smallest n,m are 1. At p=2,n=m=1 the proposed
proof exponent is a=6, B=2, and both a-n+1 and a-m+1 are 6, so the required bound holds.
The cases n=0,m=0 are deliberately excluded by the node, while the existential a is
strictly positive. Endpoints of the binomial sum have both remainders zero; no
valuation at zero is needed. No cancellation, torsion-freeness, or characteristic
assumption enters the statement.

Searches made (2026-10-15):

- msearch leanfinder: `Subring containing prime power powers and prime power multiples
  of two elements contains a prime power and prime power multiple of their sum`:
  eight hits, including `exists_add_pow_prime_pow_eq`,
  `Commute.exists_add_pow_prime_pow_eq`, the ZMod identities,
  `Ideal.add_pow_add_pred_mem_of_pow_mem`, and `Ring.perfectionSubring`.
  No exact match: the sum identities leave an uncontrolled ambient-ring error factor;
  ideal membership and characteristic-p perfection do not state this subring result.
- msearch loogle: `"exists_add_pow_prime_pow_eq"`: the two commuting/commutative
  versions above, neither giving the required subring memberships.
- msearch grep: `Subring.*pow|pow.*Subring|exists_add_pow_prime`: 25 hits;
  subring power closure and characteristic-p identities, no matching theorem.
- msearch leansearch: `Subring containing prime power powers and multiples of x and y
  contains prime power powers and multiples of x+y`: unavailable, Internal Server Error.
- Direct rg over upstream `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json`:
  `prime_power.*(add|subring)|primePower.*(add|subring)|exists_add_pow_prime|help.with.powers`:
  only an unrelated ProjGradedModuleStalkMap reference to primePowers, no match.
- Required upstream grep for `lem-pur-prime-power-addition-subring`: no hits.
- Collision search `exists_pow_add_mem|exists_prime_pow_add_mem` over Mathlib,
  upstream WeilConjectures and project lean/Sheaf: no hits.

No statement dispute or node fault found. Server compilation and delivery dry-run
validation are recorded below once complete. The independent second reading is left
to the dispatcher-designated second reader.

Validation: scompile.py compiled the delivered module cleanly on the server in 1.0 s,
with nice 19, two threads, and a 60 s per-file limit. deliver2.py --no-push printed
`OK (dry run)`: compilation and preflight passed except for the independent second
reading, which the second reader supplies. Nothing was pushed.

## Second reading by NO

Independently read the sandbox node and module together with Stacks Algebra,
Tag 0545 (`lemma-help-with-powers`, algebra.tex lines 10813–10852), its application
in `lemma-p-ring-map`, and the chapter conventions (rings are commutative with 1;
the zero ring is allowed). The node is precisely the evaluation of the polynomial
subring identity in an arbitrary commutative ring. Conversely, applying the node
to the generated subring of the polynomial ring recovers that identity. Positivity
of a agrees with the explicit source choice, although the source's opening sentence
only says integer a. No additional hypothesis is inherited from preceding lemmas.

Object, hypothesis, and conclusion checklist, in node order:

- Prime integer p: `{p : ℕ} (hp : p.Prime)`; PASS. Read `Nat.Prime` in
  `Mathlib.Data.Nat.Prime.Defs`: the positive-prime convention is exactly the source's.
- Commutative ring C: `{C : Type u} [CommRing C]`; PASS. The explicitly declared
  universe u is arbitrary, and no domain, field, Nontrivial, or characteristic
  instance is present.
- Unital subring A of C: `(A : Subring C)`; PASS. Read the structure in
  `Mathlib.Algebra.Ring.Subring.Defs`: it extends `Subsemiring C` and `AddSubgroup C`,
  sharing ambient 0 and 1 and giving exactly the stated closure properties.
- Elements x and y of C: `{x y : C}`; PASS. Both are arbitrary ambient elements,
  not assumed to lie in A.
- Positive integer exponents n,m: `{n m : ℕ} (hn : 0 < n) (hm : 0 < m)`; PASS.
  This encodes precisely the positive integer range, with separate bounds and no
  equality or ordering assumed between n and m.
- Membership of x raised to p^n: `(hx : x ^ (p ^ n) ∈ A)`; PASS.
- Membership of p^n times x: `(hpx : (p : C) ^ n * x ∈ A)`; PASS.
- Membership of y raised to p^m: `(hy : y ^ (p ^ m) ∈ A)`; PASS.
- Membership of p^m times y: `(hpy : (p : C) ^ m * y ∈ A)`; PASS.
- Existence of a positive integer a: `∃ a : ℕ, 0 < a ∧ ...`; PASS. It follows
  all the objects and hypotheses; no uniform exponent is demanded prematurely.
- Power membership for the sum: `(x + y) ^ (p ^ a) ∈ A`; PASS.
- Multiple membership for the same sum and the same a:
  `(p : C) ^ a * (x + y) ∈ A`; PASS. The two clauses are conjoined under one witness.
- Canonical integer-multiple convention: natural casts into C and multiplication;
  PASS. Casting the nonnegative integer p through ℤ gives the same element, and
  casting commutes with powers. No choice of algebra structure is introduced.

Dependencies: opened `def-weil-pbc-algebra-hom-quotient` and its recorded Mathlib
signatures (`AlgHom`, `Ideal.Quotient.algebra`, `Ideal.Quotient.mkₐ`, and the ideal
semiring instance). They provide the ordinary commutative-ring conventions; the
item needs no quotient, ideal operation, or algebra-hom object, so no replacement
notion or dependency module is needed. Opened both proof-dependency nodes and
read `add_pow` in `Mathlib.Data.Nat.Choose.Sum` and
`WittVector.map_frobeniusPoly.key₁` in `Mathlib.RingTheory.WittVector.Frobenius`,
including its `[Fact p.Prime]` context. The first applies to the underlying
commutative semiring; the second uses n=a and j=k-1 for positive k≤p^a.
Both proof-only imports are present without `public`.

Edge cases: the zero ring, arbitrary characteristic (including characteristic p,
zero and mixed characteristic), bottom and top subrings, zero x or y, and x+y=0
are all included. The prime restriction excludes 0 and 1 exactly as the source.
The cases n=0 and m=0 are outside the node, and a=0 is excluded by the conclusion.
There is no index-type or scheme parameter, so empty index sets and empty schemes
add no cases here. In the proof's finite binomial sum, endpoint indices have both
remainders zero; no valuation at zero is used. Arbitrary u includes all ring sizes.

Independent duplicate searches (2026-10-15), using different wording:

- msearch leanfinder: `Subring stable under adjoining elements whose p-power and
  p-multiple already lie in the subring, closure under sum`: eight hits, including
  `Subalgebra.perfectClosure`, `Ring.perfectionSubring`, `Subring.pow_mem` and
  closure induction/list descriptions; no exact theorem.
- msearch loogle: `"Subring", "pow", "add"`: zero hits.
- msearch grep: `pow.*add.*mem|add.*pow.*mem|perfectClosure`: 25 hits, including
  relative perfect closures; no arbitrary-characteristic subring theorem.
- Direct rg on Mathlib, upstream WeilConjectures, project lean/Sheaf and upstream
  names for `exists_prime_pow_add_mem|primePowerAddition|help_with_powers|
  prime_power_addition`: no duplicate. A broader concept/id search in the project
  and upstream found only unrelated projective-spectrum power membership.
- Read the actual nearby candidates: `Subalgebra.perfectClosure` requires
  `[ExpChar A p]` and concerns powers in an algebra-map range;
  `Ring.perfectionSubring` is an alias of `Perfection.subring`, a characteristic-p
  subring of sequences. Neither states this node. Read
  `exists_add_pow_prime_pow_eq`: its ambient error factor r is uncontrolled by A,
  so it does not imply the desired membership by direct specialization.

No mismatch found; no Lean, signature, or node correction was necessary. There are
no new definition nodes, dependency modules, or statement_change to review.
The sole theorem has exactly `by sorry`; there is no definition, hidden local
notation, private substitute, or proved auxiliary theorem. Both docstrings cite
the source and blueprint id. The theorem docstring follows all four node proof
steps: explicit a and B; binomial expansion and remainders; both nonzero-remainder
cases and endpoints; reassembly by subring closure. The arithmetic bounds are
valid, and the argument uses no cancellation in C. All variables and the universe
are bound; the JSON lean.statement was checked verbatim against the signature,
and all Lean lines satisfy the 100-character limit.

Validation: independently compiled the sole delivered module with scompile.py on
the server: clean, 1.0 s, nice 19, two threads, 60-second per-file limit. Only the
report was changed by this second reading.
