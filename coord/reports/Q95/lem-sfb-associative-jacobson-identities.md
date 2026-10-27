## Worker report

The module `Sheaf.Algebra.Lie.AssociativeJacobsonIdentities` states
`Algebra.associative_jacobson_identities`, with its proof `sorry`, and constructs
`Algebra.jacobsonCorrectionTerm` with real data. The latter is the coefficient
construction explicitly included in this node, not an independent missing notion.
Both declarations are recorded in `lean.declarations`. No new node or dependency
module is needed. No mathematical statement, dependency, or accepted proof split
is changed; the item gains only its `lean` field.

Source read: Milne, Algebraic Groups (2017), Section 10k, the definition preceding
Proposition 10.38 and Proposition 10.38(a),(b), printed pp. 204–206 (PDF pages
216–218). The accepted node uses the coefficient normalization of the correction
terms. I retain that exact normalization and the six-step coefficient proof in
the theorem docstring, rather than replacing it with a new word convention.

Hypotheses and clauses, individually:

- The field is `F : Type u` with `[Field F]`. Prime positive characteristic is
  `(p : ℕ) [Fact p.Prime] [CharP F p]`; primality includes `p > 0`.
- The associative unital algebra is `A : Type v` with `[Ring A] [Algebra F A]`.
  `Ring` includes associativity and a unit but no commutativity. `Algebra` gives
  the central scalar action. Universes `u` and `v` are independent and explicit.
  There is no finite-dimensionality or nontriviality requirement on `A`.
- The elements are the explicit binders `(a b : A)`.
- The commutator endomorphism `ad(a)` is expressed directly as
  `LinearMap.mulLeft F a - LinearMap.mulRight F a`. At input `c` it is exactly
  `a*c-c*a`. This uses existing Mathlib constructions, not a replacement Lie
  structure or an independently defined adjoint.
- For `z=ta+b`, `Polynomial.X * Polynomial.C a + Polynomial.C b` is the actual
  polynomial `z`. `Polynomial A` supports noncommutative coefficients and
  its indeterminate is central (`Polynomial.X_mul`, Basic.lean:501).
- `Nat.iterate (fun q : Polynomial A ↦ z*q-q*z) (p-1) (Polynomial.C a)`
  is precisely `ad(ta+b)^(p-1)(a)`; iteration of this endomorphism as a function
  is its composition power. The function is not an arbitrary adjoint witness.
- `Algebra.jacobsonCorrectionTerm F p a b i` is the coefficient at `i-1`
  multiplied by the scalar inverse `(i : F)⁻¹`. For `1 ≤ i < p`, that scalar
  is invertible, so it is exactly the element defined by `i*s_i = coefficient`.
  The total definition outside this range imposes no additional claim.
- The first conjunct is equality of the two actual `F`-linear endomorphisms:
  `(LinearMap.mulLeft F a - LinearMap.mulRight F a)^p` and
  `LinearMap.mulLeft F (a^p) - LinearMap.mulRight F (a^p)`.
- The second conjunct is `(a+b)^p = a^p+b^p+sum s_i`, with the index set
  `Finset.Ico 1 p`, exactly the integers `1,...,p-1`. Both clauses hold for
  every `a,b`, rather than assuming the elements commute.

Dependency declarations read and used:

- `def-weil-field` is a Mathlib leaf with match `Field`; read its entire
  docstring and class signature at Mathlib/Algebra/Field/Defs.lean:167–181.
  `Mathlib.Algebra.Field.Defs` is publicly imported.
- The proof dependency `lem-sfb-commuting-binomial-expansion` is a Mathlib leaf
  matching `Commute.add_pow`, Mathlib/Data/Nat/Choose/Sum.lean:34–35; read
  lines 25–40. Its module is imported privately for the postponed proof.
- Read `LinearMap.mulLeft` and `LinearMap.mulRight` with their docstrings and
  full signatures in Mathlib/Algebra/Module/LinearMap/Defs.lean:1016–1055.
  They need no commutativity assumption on the algebra. Read `CharP` at
  Mathlib/Algebra/CharP/Defs.lean:41–57, `Algebra` at
  Mathlib/Algebra/Algebra/Defs.lean:95–99, `Polynomial.C` and `Polynomial.X`
  at Mathlib/Algebra/Polynomial/Basic.lean:430–481, and `Nat.iterate` at
  Mathlib/Logic/Function/Iterate.lean:40–46.

Edge cases checked before writing:

- At `p=2`, the coefficient polynomial is `[b,a]`; the one correction term
  is `ba-ab=ab+ba`, exactly the mixed part of the square in characteristic two.
  Thus the orientation of the adjoint and the coefficient index are correct.
- At `p=3`, the constant coefficient is `b²a+bab+ab²`, and the coefficient
  at `t` is twice `a²b+aba+ba²`. Division by the indicated index gives
  exactly the six mixed words in the cube. This checks the scalar normalization.
- If `A` is commutative, the first commutator iteration is zero and `p-1 ≥ 1`,
  so every correction term in the sum vanishes, as expected.
- The zero algebra is allowed: there is deliberately no `[CharP A p]`, which
  would exclude it (its characteristic is one). Characteristic is imposed on
  the nonzero field only. All formulas in the zero algebra are equalities of
  zero elements/maps. No faithful action is required.
- Arbitrary infinite-dimensional algebras, finite base fields, and elements
  equal to zero are included. No coefficient argument uses evaluation to
  detect polynomial equality. The cases `p=0,1` are exactly excluded by the
  node's prime-characteristic hypothesis.

Searches actually run through `msearch.py` for this item:

- LeanFinder: `Jacobson identities for arbitrary associative algebras of
  characteristic p, adjoint pth power and sum pth power with iterated
  commutator coefficient correction terms`. Eight hits: commuting-element
  power formulas, `LieAlgebra.ad_pow_lie`, and the Jacobson–Noether theorem;
  none states the arbitrary noncommuting sum formula.
- Loogle: `LieAlgebra.ad, "pow"`. Four hits including `LieAlgebra.ad_pow_lie`,
  `LieModule.toEnd_pow_lie`, `LieSubalgebra.coe_ad_pow`, and
  `JacobsonNoether.exist_pow_eq_zero_of_le`. The first three concern iteration
  and the Leibniz formula, not this characteristic-p identity; the fourth
  concerns a division ring with extra algebraicity/separability assumptions.
  Read OfAssociative.lean:305–325 and JacobsonNoether.lean:1–70.
- LeanSearch: `In an associative algebra of prime characteristic the pth power
  of ad a equals ad of a to p and the Jacobson formula expresses pth power of
  a sum via iterated commutators`. Eight hits, including `add_pow_char`,
  `add_pow_char_of_commute`, `LieAlgebra.ad_pow_lie`, and derivation structures.
  The sum formulas impose commutativity or commuting arguments; read
  CharP/Lemmas.lean:150–190 to check the hypotheses. No exact match.
- Mathlib grep: `jacobson|Jacobson|ad_pow|restrictedLie` in `Algebra/Lie`.
  Five hits, all `ad_pow_lie` or `coe_ad_pow` and their uses. No match.
- Loogle: `"mulLeft", "mulRight"`. Twelve hits about equality of left and
  right multiplication or order properties; none gives the two identities.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for Jacobson,
  restricted-Lie and adjoint-power keywords found unrelated Jacobson-radical,
  topology and Jacobson–Noether material only. The required node-id search
  in `lean/WeilConjectures` found no result. The proposed full declaration
  names were also searched in Mathlib, both project trees and
  `dag/lean_names_upstream.json`, with no match.

The current node has no repair note and no Lean attachment; `coord/queue.tsv`
marks it stage 2. The inherited failure was an unchanged stage-1 node after Q17's
accepted split, not a defect in this stage-2 assignment. No STATEMENT-DISPUTED
or statement correction is needed.

Validation: use the prescribed server single-file compiler and delivery dry run;
no local Lean build or source mutation was used. Initial compilation diagnosed
an incorrect `Function.iterate` name and a privately imported interval constant;
repaired these to `Nat.iterate` and an explicit public finite-interval import.

Final validation passed: `scompile.py` compiled both the isolated sandbox and
library module without errors or unexpected warnings. `deliver2.py --no-push`
reported OK: the delivery passes the server preflight and compiles. A structural
check confirms the node delta is only `lean`, the recorded signature is verbatim,
every Lean line has at most 100 characters, and there is exactly one `sorry`.

## Second reading by Q95

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
