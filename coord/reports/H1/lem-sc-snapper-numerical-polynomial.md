## Worker report

The module `lean/Sheaf/AlgebraicGeometry/SnapperNumericalPolynomial.lean` states
`AlgebraicGeometry.Scheme.Modules.exists_mvPolynomial_eulerChar_tensorPowers`, with its
only proof `sorry`. It gives the full multivariate, integer-exponent Snapper statement;
there are no new definitions, new nodes, or dependency modules. The polynomial notion is
expanded directly into the existing Mathlib `MvPolynomial` and its evaluation and degree,
just as the source's univariate Hilbert theorem expands it into `Polynomial ℚ`.

Hypotheses and clauses matched with the node:

- Field k: `(k : Type u) [Field k]`.
- Scheme X over k: `(X : Scheme.{u}) [X.Over (Spec (.of k))]`.
- Proper over k: `[IsProper (X ↘ Spec (.of k))]`. No projectivity, ampleness,
  nonemptiness, positive characteristic, or separate Noetherian hypothesis is imposed.
- Coherent O_X-module F: `(F : X.Modules)` and
  `(hF : RingedSpace.IsCoherent X.toRingedSpace F)`, the dependency's exact coherent
  predicate, not the source's weaker `isCoherent` (quasi-coherent plus finite presentation).
- Finitely many invertible O_X-modules: `(r : ℕ) (L : Fin r → X.Modules)` with
  `[∀ i : Fin r, (L i).IsInvertible]`; r may be zero.
- Input Z^r: `∀ n : Fin r → ℤ`, covering every integer tuple, including negative entries.
- L_i to the integer tensor power n_i: when `0 ≤ n i` use the recorded `tensorPow`
  applied to `(n i).toNat`; otherwise use the recorded `dual.tensorPow (-n i).toNat`.
  This is a direct expression in the existing natural tensor-power and dual operations,
  not a second named definition of either operation. For invertible sheaves the dual
  is precisely the tensor inverse (`nonempty_tensorObj_dual_iso_unit` in Modules.Dual).
- F tensor L_1^{n_1} tensor ... tensor L_r^{n_r}: `List.ofFn` in Fin order, followed by
  `foldl (fun M N : X.Modules => M ⊗ N) F`. Thus the empty list returns F itself.
- Euler characteristic: the recorded `Scheme.Modules.eulerChar k` of that folded sheaf.
  It is integer-valued; the equality casts this integer to ℚ to compare with polynomial
  evaluation. No scalar extension of k to ℚ is assumed.
- Numerical polynomial: `∃ P : MvPolynomial (Fin r) ℚ` with
  `∀ n, MvPolynomial.eval (fun i => (n i : ℚ)) P = ...`.
  Being equal to the integer Euler characteristic on the whole integer lattice gives
  precisely the required integer-valued rational polynomial, not eventual polynomiality
  or merely polynomiality for nonnegative inputs.
- Total degree at most dim Supp(F):
  `P = 0 ∨ ((P.totalDegree : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim ...`.
  The support is written directly as the subtype
  `{x : X | ¬ Subsingleton ↑(TopCat.Presheaf.stalk F.val.presheaf x)}`,
  with its subspace topology. The additive stalk is zero exactly when its underlying
  type is subsingleton, so this is the usual O_X-module support. It uses the existing
  categorical stalk, not the affine support of a module over a ring or the zero locus
  of an ideal. Mathlib's natural totalDegree assigns 0 to the zero polynomial, so the
  separate `P = 0` branch faithfully gives degree minus infinity, including empty support.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`, `Field` (mathlib_match of def-weil-field).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`:
  separated, universally closed, locally finite type; universal closedness supplies
  quasi-compactness, agreeing with the properness node's finite-type formulation.
- `Sheaf.AlgebraicGeometry.Coherent`, `AlgebraicGeometry.RingedSpace.IsCoherent`:
  finite type plus finite-type kernels of every map from a finite free sheaf on an open.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` (imported through Modules.Dual):
  locally isomorphic to the structure sheaf; also uses its `tensorPow` and monoidal
  structure on X.Modules.
- `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`,
  `AlgebraicGeometry.Scheme.Modules.eulerChar`: the alternating finsum of finrankH.
  Properness and coherence give the finite-dimensionality and vanishing needed to
  interpret it as the actual Euler characteristic; these are consequences, not added
  assumptions.
- `Mathlib.Topology.KrullDimension`, `topologicalKrullDim`: Krull dimension in
  `WithBot ℕ∞` by chains of nonempty irreducible closed subsets.
- Additional existing operations: `Scheme.Modules.dual` in Modules.Dual;
  `MvPolynomial.totalDegree` in Mathlib.Algebra.MvPolynomial.Degrees;
  `MvPolynomial.eval` in Mathlib.Algebra.MvPolynomial.Eval;
  `TopCat.Presheaf.stalk` in Mathlib.Topology.Sheaves.Stalks.

Edge cases checked: r = 0 is a constant polynomial on a singleton tuple space and the
fold is F. Zero exponents use the tensor unit; negative exponents use the dual, including
n = -1. F = 0 has empty support (dimension bottom) and admits P = 0; the same handles the
empty scheme. Nonzero dimension-zero support gives a constant polynomial. Any field
characteristic is allowed: rational polynomial coefficients do not act on k. Universe u
is explicit and shared by k and X, as in the recorded Euler characteristic definition;
Fin r and integer tuples impose no additional size restrictions. No auto-bound variables.

Searches (2026-10-11):

- msearch leanfinder: "Euler characteristics of coherent sheaf twists by several invertible
  modules form a numerical polynomial": eight unrelated results, e.g. Proj.pow_apply,
  Scheme.Modules.instAbelian and Sheaf.H; no matching theorem.
- msearch loogle: "MvPolynomial, totalDegree": zero hits, unknown identifier totalDegree.
- msearch grep: "numerical polynomial|IsNumericalPolynomial": zero Mathlib hits.
- msearch leansearch: "integer valued multivariate polynomial rational coefficients numerical
  polynomial": service unavailable (Internal Server Error); no mathematical verdict.
- msearch leanfinder: "integer tensor powers of invertible sheaves using dual for negative
  exponents": unrelated affine Picard groups and presheaf monoidal structures; no scheme
  integer tensor-power declaration.
- msearch grep: "tensorIntPow|tensorZPow|IsNumericalPolynomial|NumericalPolynomial": no hits.
- rg in source WeilConjectures/AlgebraicGeometry/Modules for numerical, tensorZPow,
  tensorInt, zpow, support: Ample.lean has only a univariate Hilbert theorem for an ample
  sheaf and natural exponents, so it does not state this node. Dual.lean provides the
  needed existing dual and Invertible.lean provides natural tensor powers.
- rg of the item ID in source WeilConjectures: no hits.
- rg in dag/lean_names_upstream.json, dag/nodes, lean/Sheaf and source WeilConjectures for
  tensorIntPow, tensorZPow, IsNumericalPolynomial, NumericalPolynomial: only historical
  search text in this node, no existing declaration or definition node.
- blueprint_refs.py search "numerical polynomial": only the Hilbert-polynomial statement
  and Hilbert-degree definition, neither gives this theorem or a separate numerical
  polynomial predicate. Search "integer tensor": no blueprint nodes.
- Direct Mathlib source reads verified totalDegree as the maximum sum of exponents of
  supported monomials, and eval as a ring homomorphism from a multivariate polynomial.

Source checked at https://stacks.math.columbia.edu/tag/0BEM (also section 0BEL).
The local literature/stacks-project/varieties.tex is absent on this machine, so the official
Stacks page supplies the statement and proof. The node's source label names 0BEL (a section);
the actual lemma is 0BEM, as already used throughout its proof. This is a source-place typo,
not a statement fault; the module identifies both tags. No statement correction or
STATEMENT-DISPUTED marker is needed. Its five proof steps are retained in the docstring.

Validation: single-file server compilation via scompile.py; delivery dry run via
`deliver2.py H1 lem-sc-snapper-numerical-polynomial --no-push`. The independent second
reader supplies the second-reading section and performs delivery.

## Second reading by H1

I read the node as introducing: a field `k`; a scheme `X` proper over `Spec k`; a coherent
`O_X`-module `F`; a natural number `r`; and `r` invertible modules `L : Fin r → X.Modules`.
Its conclusion has two clauses: there is a rational multivariate polynomial `P` in `Fin r`
whose total degree is at most the Krull dimension of `Supp(F)` (with the zero-polynomial
case representing dimension `-∞`), and for every integer tuple `n : Fin r → ℤ`, its value is
the Euler characteristic of `F` tensor the integer powers of the `L i`.

The Lean renders these items as `(k : Type u) [Field k]`, `(X : Scheme.{u})
[X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]`, `(F : X.Modules)` with
`hF : RingedSpace.IsCoherent X.toRingedSpace F`, and `(r : ℕ) (L : Fin r → X.Modules)`
with `[∀ i, (L i).IsInvertible]`.  The conclusion is `∃ P : MvPolynomial (Fin r) ℚ`,
followed by the degree bound and `∀ n : Fin r → ℤ` evaluation equality.  The support is
exactly the subtype of points whose categorical stalk is not subsingleton, and the tensor
list is `List.ofFn` in `Fin` order folded from `F`; nonnegative exponents use `tensorPow`
and negative exponents use `dual.tensorPow`.  The Euler characteristic is the recorded
`eulerChar k`, cast to `ℚ`.

Verdict: every object, hypothesis, quantifier, and conclusion clause matches the node and
Stacks Tag 0BEM.  The shared universe `u` does not exclude any case.  The empty index
case `r = 0` gives a constant polynomial and an empty fold; zero and negative exponents
are represented; the zero module and empty scheme are covered by the zero-polynomial
branch; dimension-zero support and arbitrary field characteristic remain allowed.  No
extra Noetherian, projective, ampleness, nonempty, or finiteness assumption was added.
The node's source label says section tag 0BEL, while the actual lemma is Tag 0BEM; the
module documents both and this is only a source-place label issue.

I searched Mathlib, `WeilConjectures`, `lean/Sheaf`, the upstream-name index, and DAG
nodes for numerical-polynomial and integer tensor-power declarations, and used LeanFinder,
Loogle, grep, and the project's msearch helper.  No existing declaration states this
multivariate result or defines a competing notion.  Existing dependency declarations
were opened and match the uses: `IsProper`, `RingedSpace.IsCoherent`,
`Scheme.Modules.IsInvertible`, `Scheme.Modules.eulerChar`, and `topologicalKrullDim`.
The module compiled cleanly with `scompile.py`; no mismatch was found and no source or
Lean change was needed in this second reading.
