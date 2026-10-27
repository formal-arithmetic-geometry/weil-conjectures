## Worker report

The module `Sheaf.LinearAlgebra.SemilinearRestrictedSymmetricBasis` states
`SymmetricAlgebra.exists_basis_semilinear_restricted_quotient`, with its sole proof `sorry`.
The node's statement, dependency lists and proof are unchanged; only `lean` is attached.
No helper definition, new node, dependency repair or statement correction is required.
The quotient and induced map are direct applications of Mathlib, rather than second definitions.

Hypothesis and clause correspondence:

- A field k: `{k : Type u} [Field k]`.
- Prime characteristic p > 0: `(p : ℕ) [Fact p.Prime] [CharP k p]`.
  Primality includes positivity and p ≥ 2; no characteristic-zero case is introduced.
- Any k-vector space V: `{V : Type v} [AddCommGroup V] [Module k V]`.
- T additive: `(T : V →+ V)`, whose bundled laws include additivity and zero preservation.
- T(cv) = c^p T(v): `hT : ∀ (c : k) (x : V), T (c • x) = c ^ p • T x`.
- The canonical linear inclusion into Sym: `SymmetricAlgebra.ι k V`.
- The specified commutative quotient B(V,T):
  `(SymmetricAlgebra k V) ⧸ Ideal.span
  (Set.range fun x : V => (ι k V x) ^ p - ι k V (T x))`.
  These are all the relations, indexed by all vectors, not just the chosen basis.
- j is the induced linear map: `(Ideal.Quotient.mkₐ k ...).toLinearMap.comp (ι k V)`.
  It is a canonical composite, not an arbitrary map or an additional assumption.
- Every basis with arbitrary index set: `{I : Type w} (b : Module.Basis I k V)`.
  The scalar, module and index universes are explicitly bound and independent.
- Exponents with finite support and coordinates in {0,...,p-1}:
  `{a : I →₀ ℕ // ∀ i : I, a i < p}`. Naturals supply the lower bound automatically.
- These specified monomials form a basis: the first conjunct asserts existence of a
  `Module.Basis` with precisely that index type and the quotient as its carrier, with
  `∀ a, c a = a.val.prod (fun i n => (Ideal.Quotient.mkₐ k ... (ι k V (b i))) ^ n)`.
  Thus this is a statement about the exact monomial family, not just freeness or dimension.
- Empty product equals 1: `Finsupp.prod` is by definition the product over the finite support,
  so the zero finitely supported exponent has the empty product, equal to 1. No extra
  tautological conclusion is added.
- In particular j is injective: the second conjunct is `Function.Injective` of the
  exact composite defining j above.
- The absence of finite dimensionality, finite T-generation and perfectness is preserved:
  there are no such binders, no finiteness instance, no invariant-subspace assumption,
  and no surjectivity assumption on Frobenius or T.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field` in `Mathlib.Algebra.Field.Defs`, obtained through the
  public algebra imports. Its full structure is a commutative ring with division.
- `lem-weil-pbc-symmetric-algebra-universal-property`:
  `SymmetricAlgebra`, `SymmetricAlgebra.ι`, `SymmetricAlgebra.lift` and
  `SymmetricAlgebra.algHom_ext` in `Mathlib.LinearAlgebra.SymmetricAlgebra.Basic`.
  The signature uses the first two directly. Read the full definitions and universal property.
- `def-weil-pbc-algebra-hom-quotient`: `AlgHom` from `Mathlib.Algebra.Algebra.Hom`,
  `Ideal.Quotient.algebra`, `Ideal.Quotient.mkₐ`, its surjectivity and kernel theorems
  from `Mathlib.RingTheory.Ideal.Quotient.Operations`. The quotient algebra and map in the
  statement are exactly these constructions.
- Proof-only `lem-sfb-symmetric-algebra-monomial-basis`: `Module.Basis.symmetricAlgebra`
  in `Mathlib.LinearAlgebra.SymmetricAlgebra.Basis`, imported without `public`.
- Proof-only `lem-sfb-commuting-binomial-expansion`: `Commute.add_pow` in
  `Mathlib.Data.Nat.Choose.Sum`, imported without `public`.
- `Module.Basis` in `Mathlib.LinearAlgebra.Basis.Defs` and `Finsupp.prod` in
  `Mathlib.Algebra.BigOperators.Finsupp.Basic` provide the exact basis and finite product.

Source check: read Milne's local PDF, Definition 10.39 and Theorem 10.40 with its proof
and Corollary 10.41, printed pp.206–207 (PDF pp.218–219), and Lemma 14.43, printed p.294
(PDF p.306). Zero bracket makes the restricted operation exactly an additive p-semilinear
map. Commutativity removes any need for an order in the product. Theorem 10.40 has an
arbitrary index set; its basis also gives injectivity without finite dimensionality.
Also read the current blueprint unit and its direct-image proof in `literature/blueprint/latest/`.
The declaration docstring carries all six node proof steps, including the ideal-generator
calculation, finite triangular argument, quotient-basis argument and injectivity.

Edge cases checked mathematically before writing:

- I empty / V zero: the exponent type has one element, the only relation is zero,
  the quotient is k and the basis vector is 1; the linear map from V is injective.
- p = 2: degrees still drop by at least one and the unit exponents remain allowed.
- T = 0: the statement gives the standard truncated polynomial monomials.
- Rank one with T(e) = λe: the quotient is k[X]/(X^p - λX), including λ = 0.
- Nonperfect k = F_p(t): no pth roots of coefficients are required.
- Infinite basis I = ℕ with semilinear shift T(e_i) = e_(i+1): no finite invariant
  subspace is assumed. Every relation and monomial still has finite support.
- T = identity over F_p: this also fits; the polynomial relations have nonzero linear terms.

Searches (2026-10-24):

- `msearch.py ... leanfinder` query: "The quotient of the symmetric algebra by v power p
  minus a Frobenius semilinear map has a basis of monomials with exponents less than p".
  Eight hits, including `Module.Basis.symmetricAlgebra`, its repr lemma,
  `mapPowExpCharPowOfIsSeparable`, `SymmetricAlgebra.instModuleFree`,
  `IsSymmetricAlgebra.mvPolynomial` and `Module.Basis.tensorAlgebra`.
  None states a basis of the restricted quotient.
- `msearch.py ... loogle` query: `"SymmetricAlgebra", "basis"`.
  Two hits: `Module.Basis.symmetricAlgebra` and its repr lemma; both are unrestricted.
- `msearch.py ... grep` query:
  `restrictedSymmetric|RestrictedLie|restrictedEnvelop|PBW|Poincare.Birkhoff`.
  One hit, an alternative-construction comment in `Mathlib/Algebra/Lie/Free.lean`.
- `msearch.py ... leansearch` query:
  "Symmetric algebra quotient by p power minus a semilinear operation".
  Eight hits including `LinearMap.frobenius`, `SymmetricPower`, `SymmetricAlgebra`,
  `LinearMap.iterateFrobenius`, `SymmetricAlgebra.lift` and divided-power quotients;
  none gives the required quotient basis.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` for
  `restrictedSymmetric|restricted[Ss]ymmetric|semilinear.*[Bb]asis` and the item id:
  no corresponding declaration; one unrelated quadratic-criterion comment.
  Follow-up declaration-name search for `exists_basis_restrictedQuotient` and restricted
  ideal/map names found no matching algebra construction.
- `rg -l` in `dag/nodes` for restricted symmetric algebra mentions found this item and
  its consumers, including primitive Frobenius duality and the coalgebra-kernel primitive
  lemma, but no separate definition or theorem with the same statement.

Validation: prescribed `scompile.py NH lem-sfb-semilinear-restricted-symmetric-basis`
compiled both sandbox and library-module modes successfully, with no errors or warnings.
No global build or direct repository mutation was run. No statement dispute or node fault found.

## Second reading by NH

The dispatcher worker reread the node and finished file after compilation. This is a second
pass by the same worker; the independent review is the maintainer's, as specified in the brief.
The universal hypotheses, exact all-vector relation ideal, bounded finitely supported
exponent type, pointwise monomial identification and canonical-map injectivity match the
clauses above. In particular, the existential basis is constrained at every index, so it
cannot accidentally assert a basis unrelated to the monomials. The empty exponent has
product 1 by the existing `Finsupp.prod` definition. The arbitrary-index and imperfect-field
cases are retained, and no equality between universes is imposed. No mismatch or revision
was needed in this second pass.
