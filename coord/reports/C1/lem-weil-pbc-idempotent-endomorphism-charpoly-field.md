## Worker report

The module `Sheaf.LinearAlgebra.IdempotentEndomorphismCharpolyField` states
`LinearMap.charpoly_toMatrix_of_idempotent`, with exactly one `sorry` and no definitions.
It states the characteristic-polynomial formula and the divisibility in an arbitrary basis.
The original node is unchanged except for its `lean` field; no new or dependency modules
are needed, and no statement correction or dispute was found.

Hypotheses and clauses, individually:

- A field k: `{k : Type u} [Field k]`, with an explicit arbitrary universe `u`.
- n ≥ 0: `(n : ℕ)` includes every nonnegative integer, including zero.
- V = k^{⊕n}: `(Fin n → k)` is the finite coordinate vector space, canonically the
  direct sum of n copies of k. For a finite index set every function has finite support.
- p is k-linear V → V: `(p : (Fin n → k) →ₗ[k] (Fin n → k))`.
- p ∘ p = p: `(hp : p.comp p = p)`.
- r = dim_k Im(p): `let r := Module.finrank k (LinearMap.range p)` in the conclusion.
- Computed in any basis: `(b : Module.Basis (Fin n) k (Fin n → k))` is universally
  quantified, not a fixed preferred basis. Such bases exist for all n, so this introduces
  no restriction on p or k.
- det(T-p) = (T-1)^r T^{n-r}: the first conjunct is
  `(LinearMap.toMatrix b b p).charpoly = (Polynomial.X - 1) ^ r * Polynomial.X ^ (n - r)`.
  Matrix.charpoly is precisely the determinant of T times the identity minus that matrix.
- Divides T^n(T-1)^n in k[T]: the second conjunct uses polynomial divisibility `∣`
  with `(Polynomial.X : Polynomial k) ^ n * (Polynomial.X - 1) ^ n`.

Dependencies read and used:

- `def-weil-pbc-charpoly-free-module`: the recorded `Matrix.charpoly` from
  `Mathlib.LinearAlgebra.Matrix.Charpoly.Basic`, applied to the matrix obtained by
  `LinearMap.toMatrix` in basis b. The definition and characteristic-matrix definition
  were read in full.
- `lem-weil-pbc-charpoly-free-module-properties`: its Mathlib match includes
  `LinearMap.charpoly_toMatrix` from `Mathlib.LinearAlgebra.Charpoly.ToMatrix`, whose
  full signature identifies each basis matrix characteristic polynomial with p.charpoly.
  This module is imported; the arbitrary-basis presentation uses the recorded matrix
  notion and states the formula for every basis directly. The other clauses' recorded
  declarations (`LinearEquiv.charpoly_conj`, `Matrix.charpoly_monic`,
  `Matrix.charpoly_natDegree_eq_dim`, `Module.Basis.baseChange`,
  `LinearMap.charpoly_baseChange`) were also inspected, but those clauses are not needed
  to formulate this node.

Edge cases checked mathematically before writing: n = 0 gives r = 0 and polynomial 1,
which divides 1; p = 0 gives r = 0 and X^n; p = identity gives r = n and (X-1)^n.
Intermediate projections give the product with both exponents nonnegative, as r ≤ n
by rank-nullity. Positive characteristic, including characteristic two, causes no
exception: zero and one are distinct in every field. No nonzero-dimension hypothesis,
characteristic restriction, or extra finite-dimensionality hypothesis was introduced.

The source file literature/stacks-project/more-algebra.tex is absent on this machine.
The source proof was read instead at https://stacks.math.columbia.edu/tag/07M5,
Lemma 15.9.11: the fibre characteristic polynomial has the stated powers, and it
annihilates X^n(X-1)^n in the quotient. This confirms the node's formula and divisibility.
The declaration docstring includes all four natural-language proof steps with their
DAG references: decomposition and rank-nullity, adapted basis and direct sum,
identity/zero characteristic polynomials, then exponent comparison for divisibility.

Searches for an existing statement (2026-10-11), run through msearch.py:

- LeanSearch: "characteristic polynomial of an idempotent linear endomorphism over a field";
  service unavailable (Internal Server Error), recorded in searches.jsonl.
- LeanFinder: "characteristic polynomial of an idempotent linear map is (X-1)^rank times
  X^(dimension-rank)"; eight hits, including LinearMap.charpoly_one and generalized
  eigenspace dimension results, none the full idempotent formula and divisibility.
- Loogle: "IsIdempotentElem, LinearMap.charpoly"; zero hits.
- Mathlib grep: "charpoly.*(idempot|proj)|(idempot|proj).*charpoly" in LinearAlgebra;
  zero hits.
- Source repository and lean/Sheaf rg for characteristic-polynomial/idempotent or
  projection combinations: zero hits; the node id search in WeilConjectures also had
  zero hits. Exact declaration-name searches in Mathlib, WeilConjectures, lean/Sheaf,
  and dag/lean_names_upstream.json found no collision.

Validation: scompile.py compiled the module on the server in 1.5 seconds, exit code 0,
with no warnings. The delivery dry run is the final mechanical check; the second
reader supplies the independent reading and delivery.

## Second reading by C1

Independent second reading on 2026-10-11. I opened the sandbox node and Lean module,
both statement-dependency nodes, and their Mathlib declarations. No mathematical
mismatch was found, so the module and node record are preserved.

The node's objects, hypotheses and conclusion clauses, matched individually:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Arbitrary field k | `{k : Type u} [Field k]`, `universe u` | Exact; no characteristic restriction. |
| Nonnegative integer n | `(n : ℕ)` | Exact, including zero. |
| V = direct sum of n copies of k | `Fin n → k` | Exact finite coordinate space; finite support is automatic. |
| k-linear endomorphism p of V | `(p : (Fin n → k) →ₗ[k] (Fin n → k))` | Exact domain, codomain and scalar field. |
| p composed with p equals p | `(hp : p.comp p = p)` | Exact equality of linear maps, with no added condition. |
| r is the dimension of the image | `let r := Module.finrank k (LinearMap.range p)` | Exact; range is the image subspace, finite dimensional automatically. |
| Computation in any basis | `(b : Module.Basis (Fin n) k (Fin n → k))` | Universally quantified after p and hp; the standard basis exists for every n. |
| Characteristic polynomial det(T-p) | `(LinearMap.toMatrix b b p).charpoly` | Uses the dependency's recorded notion, with the correct matrix convention. |
| Formula (T-1)^r T^(n-r) | First conjunct, `(Polynomial.X - 1) ^ r * Polynomial.X ^ (n - r)` | Exact polynomial equality in k[T]. |
| Divisibility by T^n(T-1)^n | Second conjunct, `∣ (Polynomial.X : Polynomial k) ^ n * (Polynomial.X - 1) ^ n` | Exact divisibility and factor order. |

Dependency signatures and definitions: `Matrix.charpoly` in Matrix/Charpoly/Basic.lean:134
is `(charmatrix M).det`; `charmatrix` at line 50 is `scalar n X - C.mapMatrix M`.
`LinearMap.toMatrix` in Matrix/ToLin.lean:584 and its application rule at line 621
use entry `b.repr (p (b j)) i`, so these are the specified columns, not a different
endomorphism notion. For the other dependency, Charpoly/ToMatrix.lean:43 states
`(toMatrix b b f).charpoly = f.charpoly` with an arbitrary finite basis b.
Its required finite/free instances are available for the coordinate space, not new
hypotheses. I also opened `LinearEquiv.charpoly_conj`, `Matrix.charpoly_monic`,
`Matrix.charpoly_natDegree_eq_dim`, `Module.Basis.baseChange` and
`LinearMap.charpoly_baseChange`; the dependency's other clauses are not needed to
type this item. No missing notion, new node or dependency module is needed.

Source checked independently: the repository has no Stacks .tex checkout. I fetched
https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex
into this item's scratchpad and read lines 2019–2064, including the entire statement
and proof of `lemma-lift-projective-module` (Tag 07M5), also checked at
https://stacks.math.columbia.edu/tag/07M5. Lines 2038–2041 give the fibre projector's
characteristic polynomial and the vanishing of the indicated product in its quotient.
The ambient hypotheses are a ring A, an ideal I and a finite projective A/I-module;
after passage to the residue field the projector acts on the stated finite coordinate
space. They introduce no additional hypothesis on this field-linear lemma. The product
vanishes in k[T]/(f) precisely because f divides it. The worker report's phrase
“it annihilates X^n(X-1)^n in the quotient” should be read as this product vanishing
in the quotient, rather than a separate annihilator assertion.

Edge cases: n = 0 has the empty basis, the unique endomorphism, r = 0 and both
polynomials equal 1; the statement includes it. For p = 0 the range has rank zero
and the formula is X^n; for p = identity r = n and it is (X-1)^n. Natural subtraction
is appropriate because r ≤ n. All field characteristics, including two, are covered.
The arbitrary universe u permits every field universe; V is this explicitly specified
coordinate space in the same universe, so no arbitrary-module universe is excluded.
There are no scheme or independent index-set binders in this item; the relevant
empty index set is Fin 0. The conclusion's local r binds both conjuncts.

Independent searches, with different phrasing, recorded by msearch.py:

- LeanFinder: “characteristic polynomial of a linear projection onto its range and
  complementary nullspace”; eight hits, including `LinearMap.charpoly_one`,
  `LinearMap.charpoly_eq_X_pow_iff`, generalized eigenspace dimension results and
  idempotent conjugation/range lemmas, none the full formula and divisibility.
- Loogle: `"charpoly", "idempotent"`; zero hits.
- LeanSearch: “determinant of T minus a projection equals powers determined by image
  dimension”; service unavailable (Internal Server Error), not a negative-search verdict.
- `rg` over all Mathlib, WeilConjectures, project lean/Sheaf and
  dag/lean_names_upstream.json for `charpoly.*(idempot|projection)`, the reversed
  combination and the proposed declaration name: no hits. Read the related
  `charpoly_one`, `charpoly_zero` and `charpoly_prodMap`; none duplicates this statement.

Conventions: one theorem with `by sorry`, no definitions and no proved auxiliaries.
The single import supplies the matrix characteristic polynomial and basis comparison.
Both docstrings name the source and blueprint id. The theorem docstring covers all
four node proof steps and their dependencies. The namespace, topic path, copyright,
line widths and explicitly bound variable/universe are correct. No statement correction
or dispute is required. The JSON `lean.statement` equals the file signature verbatim.

Changes: appended this independent reading, including the precise interpretation of
the source's quotient vanishing; no changes to correct Lean or node content.
Validation: scompile.py compiled the delivered module in 1.4 seconds, exit code 0,
with no warnings. The delivery dry run and push follow this reading.
