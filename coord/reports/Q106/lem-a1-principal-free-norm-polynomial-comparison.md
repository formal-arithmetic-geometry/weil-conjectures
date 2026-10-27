## Worker report

The module `Sheaf.RingTheory.PrincipalFreeNormPolynomialComparison` states
`Algebra.principal_free_norm_polynomial_comparison`, with its sole proof `sorry`.
No definitions, auxiliary theorems, new nodes, dependency repairs, or statement
corrections are needed. The existing statement is retained verbatim in the node.

Hypothesis and clause correspondence:

- Commutative rings A and B are `{A : Type u} {B : Type v} [CommRing A]
  [CommRing B]`. The unital map φ is encoded by `[Algebra A B]`, whose map
  is `algebraMap A B`. This is the standard equivalent packaging of an arbitrary
  unital ring map, with no injectivity or finiteness assumption.
- Rank r and finite family size m are natural numbers `{r m : ℕ}`. The
  family is `f : Fin m → A`, and generating the unit ideal is exactly
  `hgen : Ideal.span (Set.range f) = ⊤`.
- Each prescribed local basis is `e i : Module.Basis (Fin r)
  (Localization.Away (f i)) (LocalizedModule.Away (f i) B)`.
  The ring and module localizations are exactly the recorded dependency
  definitions. No global basis is supplied or assumed.
- The arbitrary norm function is `N : Polynomial B → Polynomial A`.
  Its required local characterization is `hN`, quantified over every polynomial
  q and every cover index i. Its left side is coefficientwise localization.
  For each coefficient c of degree d in q, `LinearMap.mul A B c` is
  multiplication by c, `IsLocalizedModule.mapExtendScalars` is its canonical
  localization, and `LinearMap.toMatrix (e i) (e i)` gives its entries.
  The polynomial matrix entry is `q.sum fun d c ↦ Polynomial.monomial d (...)`.
  This is precisely the multiplication matrix of the localized polynomial q
  in the constant polynomial basis: multiplying q by C(eᵢₖ) has in degree d
  the localized multiplication-by-c image of eᵢₖ. The determinant is
  `Matrix.det`, the basis formula for the recorded `LinearMap.det` notion
  (`LinearMap.det_toMatrix`), with no replacement notion or helper definition.
  Thus `hN` specifies exactly the hypothesis for every q, without assuming
  multiplicativity, additivity, or compatibility under other base changes.
- The element is `(b : B)` and P_b is written in full as
  `N (Polynomial.X - Polynomial.C b)`.
- The scalar-extension characteristic polynomial χ_b is used directly as
  `Classical.choose (charpoly_locallyFree_exists_unique.{u, v, w}
  f hgen (fun i ↦ ⟨e i, trivial⟩) (LinearMap.mul A B b))`.
  The dependency states existence AND uniqueness, so its witness is determined
  as a polynomial; this is not a choice of undetermined mathematical data.
  Its hfree input is supplied from the actual local bases. No new characteristic
  polynomial definition is introduced. The dependency's test-algebra universe w
  remains arbitrary, with no equality imposed on u, v, or w.
- The first conjunct is P_b = χ_b. The second is the requested expansion,
  `∃ a : Fin r → A, P_b = Polynomial.X ^ r + ∑ j : Fin r,
  Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)`. Together they render the
  displayed chained equality and all lower coefficients.
- The third conjunct is exactly the requested evaluation after coefficientwise
  polynomial extension of φ: `(P_b.map (algebraMap A B)).eval b = 0`.
- The nonzero-base clause is `Nontrivial A → P_b.Monic ∧ P_b.natDegree = r`.
- The rank-zero clause is `r = 0 → Subsingleton B ∧ P_b = 1`.
  The global evaluation conjunct already states that this polynomial's image
  evaluates to zero, so that part applies here without another assumption.
- The zero-base clause is `Subsingleton A → Subsingleton B`. The expansion
  and evaluation are unconditional conjuncts, hence they remain asserted in
  this case and for an empty family. No `Nonempty (Fin m)` is present.

Dependency declarations read and used:

- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`, made
  available through the public localization imports of `CharpolyLocallyFree`.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule.Away` and
  `LocalizedModule.mkLinearMap`, likewise publicly available through the
  recorded characteristic-polynomial module.
- `Mathlib.LinearAlgebra.FreeModule.Basic`: `Module.Free` and `Module.Basis`;
  the specified local bases use `Module.Basis` directly, rather than an
  independent notion of freeness.
- `Mathlib.Algebra.Polynomial.Basic`: `Polynomial` and its standard C, X,
  map, monomial, sum, eval, Monic, and natDegree API.
- `Mathlib.LinearAlgebra.Determinant`: `LinearMap.det` and its matrix formula
  `LinearMap.det_toMatrix`; `Matrix.det` renders the determinant in the given
  constant polynomial basis through its explicit entries.
- `WeilConjectures.Algebra.CharpolyLocallyFree`:
  `Algebra.charpoly_locallyFree_exists_unique`, read in full, including its
  scalar-extension characterization, uniqueness, expansion, and free-case clause.
- `Mathlib.Algebra.Algebra.Bilinear`: `LinearMap.mul`, multiplication by an element.
- `Mathlib.RingTheory.Localization.Module`:
  `IsLocalizedModule.mapExtendScalars`, canonical localized multiplication.

The proof-dependency imports are plain imports:
`Mathlib.RingTheory.Localization.BaseChange` (localization/tensor comparison),
`Mathlib.LinearAlgebra.Charpoly.BaseChange` (free characteristic-polynomial
properties, with its public ToMatrix API), and
`Mathlib.RingTheory.LocalProperties.Submodule` (localization descent).
The Cayley–Hamilton API is reached through the characteristic-polynomial
imports; `Matrix.charpoly` and `LinearMap.toMatrix` are already public through
`CharpolyLocallyFree`. The declaration docstring carries all six proof steps
and their DAG references, including evaluation of Cayley–Hamilton at 1.

Edge cases checked before writing:

- r=0: every local module has an empty basis and is zero; localization descent
  makes B zero. The 0×0 determinant is 1 and the expansion has empty sum.
- A=0: the unital algebra map forces B=0; all polynomials over A coincide,
  the expansion remains meaningful, and the evaluation is zero. Degree is
  claimed only under `Nontrivial A`.
- m=0: unit-ideal generation forces A=0. The local hypotheses are empty,
  while all conclusions remain valid in the zero rings.
- A nonzero and B=0: a rank-zero cover is allowed and produces P_b=1;
  positive rank is excluded by the actual local basis data where the base
  localization is nonzero, not by an extra hypothesis.
- Some fᵢ=0 or a zero local ring: the definitions and matrix entries still make
  sense; the other charts carry the descent information. No local nontriviality
  is assumed.
- Independent ring universes u and v and the dependency's arbitrary test-algebra
  universe w remain present.

Sources read: Stacks `exercises.tex`, exercise-trace-det-rings (02DV)(1),(3);
`algebra.tex`, lemma-charpoly (00DX) and lemma-cover-module (00EK);
`groupoids.tex`, lemma-integral-over-invariants (03BJ), especially the
monicity and precise Cayley–Hamilton paragraph. These give the exact local
matrix comparison and evaluation descent used by the node. No scheme
hypothesis from the motivating groupoid is imposed on this algebra statement.

Searches for an existing statement:

- msearch LeanFinder: "A polynomial norm defined by local determinants on a
  principal free cover equals the characteristic polynomial of multiplication
  and annihilates the element". Eight hits included `Algebra.norm`,
  `Algebra.norm_apply`, `Algebra.norm_eq_matrix_det`, and
  `LinearMap.polyCharpoly`; none covers an arbitrary locally characterized N.
- msearch Loogle: `"norm", "charpoly"`. Zero hits.
- msearch LeanSearch: "The norm of X minus an element of a finite locally free
  algebra is its multiplication characteristic polynomial". Eight hits concern
  the globally free norm or specialized norm identities; none states this lemma.
- msearch grep:
  `norm.*charpoly|charpoly.*norm|basis.*[Pp]olynomial|[Pp]olynomial.*basis`.
  Twenty-five hits, including tensor/polynomial bases and free characteristic
  polynomial ingredients, but no local-cover comparison theorem.
- Project rg on `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `norm.*charpoly|charpoly.*norm` and the
  proposed names found unrelated analytic norm estimates for roots and no
  matching theorem. Searching the item id in both source trees found no module.
- Direct source inspection located the recorded characteristic-polynomial
  theorem and the exact localization-of-linear-map API. No duplicate notion
  was introduced.

Validation: the delivered module passed `scompile.py` on the server in module
mode, both sandbox and library passes, with no compiler errors or warnings.
No statement dispute or node fault was found.

## Second reading by Q106

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
