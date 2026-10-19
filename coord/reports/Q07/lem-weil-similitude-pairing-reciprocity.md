## Worker report

The module `Sheaf.LinearAlgebra.SimilitudePairingReciprocity` states
`LinearMap.similitude_pairing_reciprocity`, with one `sorry` and no new definitions.
The item node changes only in `lean`. There is no statement correction and no disputed
statement. No dependency repair or new node is needed.

Source read: current blueprint `main-20261015`,
`sec-zeta-weil/sk-prop-reciprocity/prop-duality-reciprocity.md` and its
`prop-duality-reciprocity.proof.md`, especially steps 1–2 (the paired dual action,
reciprocal eigenvalues, equal dimensions, and determinant product). The node states the
abstract linear algebra used there. Its recorded source also points to Milne II §27,
proof of Theorem 27.12, p. 158. The module docstring records that source and the
declaration docstring carries all eleven DAG proof steps, including the determinant
calculation over K[T], extension of coefficients, and multiplicity bookkeeping.
There is no maintenance repair note for this item.

Hypotheses, individually:

- `K : Type u` and `[Field K]` give the arbitrary field.
- `V : Type v`, `[AddCommGroup V]`, `[Module K V]` and the corresponding binders
  for `W : Type w` give the two vector spaces. Their universes are independent.
- `[FiniteDimensional K V]` and `[FiniteDimensional K W]` give exactly finite
  generation over the field, using the dependency's Mathlib abbreviation.
- `p : V →ₗ[K] W →ₗ[K] K` is the bilinear pairing. `[p.IsPerfPair]` has the two
  fields `bijective_left` and `bijective_right`, exactly the two induced bijections
  to the duals required by the node. The actual definition was read in
  `Mathlib.LinearAlgebra.PerfectPairing.Basic`.
- `F : Module.End K V` and `G : Module.End K W` are the linear endomorphisms.
- `c : K` with `hc : c ≠ 0` expresses the nonzero scalar c in K× without an
  extra choice of a unit representative. The two presentations are equivalent in a field.
- `hFG : ∀ (v : V) (w : W), p (F v) (G w) = c * p v w` is the exact similitude
  identity, with no symmetry, alternating-form, diagonalizability, or characteristic
  hypothesis.

Conclusions, clause by clause:

1. `Module.finrank K W = Module.finrank K V` gives equality of the dimensions.
   Every occurrence of the node's n is expanded to `Module.finrank K V`, so no
   auxiliary n or hidden let binder is required.
2. `Function.Bijective F ∧ Function.Bijective G` expresses invertibility of the
   linear endomorphisms. The next equality is
   `LinearMap.det F * LinearMap.det G = c ^ Module.finrank K V`.
3. Both `charpolyRev.natDegree` values equal `Module.finrank K V`, and both
   evaluations at zero equal one. In particular the polynomials are nonzero, so
   natural degree agrees with the integer degree in the node (also for n = 0).
   `p.flip.toPerfPair` is precisely J(w)(v) = p(v,w). Its conjugation of G is
   asserted equal to `c • (Ring.inverse F).dualMap`: the transpose of the inverse,
   rather than an unnamed dual equivalence or merely a characteristic-polynomial
   equality. `Ring.inverse` is Mathlib's total inverse on endomorphisms, which is
   the genuine inverse here by clause 2. The final polynomial equality uses
   `C (LinearMap.det F)`, `C ((-1 : K) ^ Module.finrank K V)`, and
   `F.charpoly.comp (C c * X)` for the stated scalar multiplication and substitution.
4. The last conjunct universally quantifies over `(L : Type t) [Field L]
   [IsAlgClosed L] (ι : K →+* L)`. It does not require L/K to be algebraic,
   and imposes no algebraically closed hypothesis on K. Universe t is explicit
   and arbitrary, independently of u, v and w. Its four subclauses are:
   - the multiset of roots of `G.charpolyRev.map ι`, mapped by inversion, equals
     the corresponding reciprocal-root multiset for F mapped by `α ↦ ι c / α`;
   - for every `α : Fin (Module.finrank K V) → Lˣ`, the assumed product formula
     for `F.charpolyRev.map ι` implies the exact product formula for
     `G.charpolyRev.map ι` with factors `1 - C (ι c * (↑(α r) : L)⁻¹) * X`;
   - ordinary root multisets are related by `z ↦ (ι c * z)⁻¹`;
   - characteristic-root multisets (eigenvalues with algebraic multiplicity) are
     related by `α ↦ ι c / α`.
   `Polynomial.roots` records multiplicities: its definition and
   `Polynomial.count_roots` were read in `Mathlib.Algebra.Polynomial.Roots`.
   The latter identifies counts with the dependency's `Polynomial.rootMultiplicity`.
   No set of distinct roots or squarefree assumption replaces these multisets.
   Zero is not a root of either reverse characteristic polynomial by clause 3;
   the determinant identity and invertibility exclude zero characteristic roots.
   Thus inversion in the reciprocal-root description loses no elements. The identity
   embedding when K is algebraically closed is one of the universally quantified maps.

Dependency declarations used:

- `Mathlib.LinearAlgebra.FiniteDimensional.Defs`: `FiniteDimensional`, the recorded
  match for def-weil-finite-dimensional-subspace (lines 73–76 read).
- `Mathlib.LinearAlgebra.Dimension.Finrank`: `Module.finrank`, recorded for
  def-weil-vector-space-dimension (definition and docstring at lines 51–63 read).
- `WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix`:
  `LinearMap.charpolyRev`, the exact recorded basis-free reverse polynomial. Its
  definition and docstring were read, together with its evaluation and matrix lemmas.
- `Mathlib.LinearAlgebra.Charpoly.Basic`: `LinearMap.charpoly`, the recorded match
  for def-weil-characteristic-polynomial (full signature and definition read).
- `Mathlib.LinearAlgebra.Determinant`: `LinearMap.det`, the recorded match for
  def-weil-endomorphism-determinant (definition and basis-independent docstring read).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, explicitly included in
  the match record for def-weil-algebraic-closure; the statement needs arbitrary
  algebraically closed extensions, not only the chosen `AlgebraicClosure K`.
- `Sheaf.Algebra.Polynomial.ReciprocalRootFactorization`:
  `Polynomial.reciprocal_root_factorization`, whose full signature and proof docstring
  were read. It supplies the unit-indexed factorization and multiplicity convention
  used by clause 4, with no second definition of reciprocal roots.
- `Mathlib.Algebra.Polynomial.Div`: `Polynomial.rootMultiplicity`, through the
  `roots` multiset convention explained above (definition and zero convention read).
- `Mathlib.LinearAlgebra.PerfectPairing.Basic`: `LinearMap.IsPerfPair` and
  `LinearMap.toPerfPair`, read in full, provide the perfect pairing and canonical J.

The proof-only imports follow the node: `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`
(matrix determinant), `WeilConjectures.LinearAlgebra.Matrix.CauchyBinet` (square case of
`Matrix.cauchy_binet`), `Mathlib.Algebra.Polynomial.Degree.Lemmas` (coefficient-extension
degree), and `Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff` (reversal identity).
The Cauchy–Binet source is missing from the older local checkout; its full current source
and declaration were read with `scompile.py --source` and its published module is imported.
The other proof dependencies' modules are already public imports because they are also
statement dependencies.

Edge cases checked before drafting:

- n = 0: perfectness forces both spaces to be zero; the endomorphisms are bijections
  of singleton spaces, both determinants and polynomials are one, and all root
  multisets are empty. `Fin 0` gives the empty product one. No positive-rank binder
  or nontrivial-space instance excludes this case.
- n = 1: for a nonzero scalar f, G acts by c/f. The determinant product is c and
  the polynomial identity is f(1 - (c/f)T) = -(cT - f), checking the sign and
  substitution direction. Reciprocal roots are f and c/f; ordinary roots are
  1/f and f/c, checking both inverse formulas.
- A nonscalar Jordan block F with nonzero eigenvalue and G = c times its inverse
  transpose satisfies the hypothesis. The formulas preserve repeated roots;
  no eigenbasis hypothesis has appeared.
- Characteristic two: minus signs specialize correctly, and no division by two
  or alternating-form assertion appears. Finite fields are permitted.
- c = 0 is deliberately excluded by the node; otherwise zero endomorphisms in
  positive dimension would contradict invertibility and the degree clauses.
- Coefficient extensions use arbitrary field homomorphisms, including the identity;
  no independent algebra structure, algebraicity, or fixed algebraic closure is imposed.

Searches actually performed:

- `msearch.py leanfinder`: “A perfect bilinear pairing with two endomorphisms of
  nonzero similitude multiplier gives reciprocal characteristic roots and determinant
  product”. Eight unrelated root-system pairing hits, no full statement.
- `msearch.py loogle`: `LinearMap.IsPerfPair, LinearMap.det, LinearMap.charpolyRev`.
  No hits; the service reported unknown identifier `LinearMap.charpolyRev`
  (a project definition, not a Mathlib definition).
- `msearch.py grep`: `similitude|charpoly.*dualMap` in `LinearAlgebra`.
  Zero hits.
- `msearch.py leansearch`: “A perfect bilinear pairing with a pair of linear
  endomorphisms that scale the pairing by a nonzero scalar implies reciprocal
  eigenvalues with multiplicity”. Eight perfect-pairing interface hits, including
  `LinearMap.IsPerfPair`, its constructor, and congruence; no full statement.
- `msearch.py loogle`: `LinearMap.IsPerfPair`. Twelve hits including the class,
  `Module.finrank_of_isPerfPair`, and perfect-pairing constructions, not the bundle.
- `rg -n 'similitude|Similitude'` in the upstream `WeilConjectures` and project
  `lean/Sheaf` trees. Upstream `ZetaLinearAlgebra/Pairing.lean` has the determinant,
  conjugation, polynomial, degree, and root identities separately. Its full relevant
  source and inherited hypotheses were read. No declaration states the whole node,
  notably the universal assertion for every indexed factorization together with the
  other clauses. The project tree contains no full bundled match.
- `grep -rn 'lem-weil-similitude-pairing-reciprocity'` in upstream `WeilConjectures`:
  no hits. `rg` for `similitude_pairing_reciprocity|similitudePairingReciprocity` in
  the upstream-name index, upstream sources, and project `lean/Sheaf`: no hits,
  so the new declaration name does not collide.

Validation: the required `scompile.py` per-file check passed cleanly, with no
warnings, for both the sandbox and library overlay checks (16.4 s and 19.6 s).
Static packet inspection confirmed that only `lean` changes in the node, the recorded
signature matches the file verbatim, there is exactly one `sorry`, and no Lean line
exceeds 100 columns. The required `deliver2.py --no-push` preflight follows before
delivery; its tool output records the result.

## Second reading by Q07

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
