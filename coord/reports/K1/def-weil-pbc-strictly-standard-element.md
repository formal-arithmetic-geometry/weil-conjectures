## Worker report

The module defines `Algebra.IsElementaryStandardElement` and
`Algebra.IsStrictlyStandardElement`, the two properties in Stacks Project,
Smoothing Ring Maps, Definition Tag 07C7. The local `literature/stacks-project/smoothing.tex`
checkout is absent on this machine; I read the source at
https://stacks.math.columbia.edu/tag/07C7 and compared all four equations.

- The commutative rings, their map, and its finite presentation are
  `{R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
  [FinitePresentation R A]`. The element is `(a : A)`.
- The existential presentation and nonnegative integers are
  `∃ (n m c : ℕ) (P : Presentation R A (Fin n) (Fin m))
  (hc : c ≤ min n m)`. `P.relation` is the ordered family of equations,
  `P.val` evaluates the variables, and `P.span_range_relation_eq_ker`
  ensures that the equations present `A`.
- Elementary equation (1) is `a = a' * Matrix.det ...` with `(a' : A)`.
  The matrix entries are `aeval P.val (pderiv i (P.relation j))` for the
  first `c` variable and relation indices.
- Strict equation (3) is the sum over
  `{s : Finset (Fin n) // s.card = c}`, with one coefficient `a' s : A`
  per subset. `s.val.orderEmbOfFin s.property` orders its columns
  increasingly; the matrix rows are the first `c` relations.
- Equations (2) and (4) are the shared `∀ j : Fin m, c ≤ j.val → ...`
  clauses. `P.σ a` is a lift of `a`, and membership in
  `Ideal.span {f | ∃ k : Fin m, k.val < c ∧ f = P.relation k} +
  (Ideal.span (Set.range P.relation)) ^ 2` is precisely the required
  sum of the initial relation ideal and the square of the full ideal.
  Reindexing `j` as `c+j` gives the source's range `1,...,m-c`.

Dependencies: `Mathlib.RingTheory.FinitePresentation`,
`Algebra.FinitePresentation` and `Mathlib.RingTheory.Extension.Presentation.Basic`,
`Algebra.Presentation` realize `def-weil-pbc-finitely-presented-algebra`;
`Mathlib.Algebra.MvPolynomial.PDeriv`, `MvPolynomial.pderiv` realizes
`def-weil-pbc-polynomial-partial-derivative`. Both full declarations and
their docstrings were checked in the source. The latter is a derivation
whose value on each variable is the Kronecker delta.

Edge cases: `n=0` and `m=0` remain allowed; `c=0` has empty determinant
equal to `1` and exactly one subset of size zero; `c=m` makes the
remaining-relation clause vacuous. The ring may be the zero ring and may
have any characteristic. Changing the lift changes its product with a
relation by an element of the square ideal. The two definitions quantify
over presentations rather than choosing a preferred one.

Searches: `msearch.py leanfinder` with "strictly standard element of
finitely presented algebra: Jacobian minors and relations modulo square
of ideal" returned submersive presentations and standard smoothness, no
match. `msearch.py loogle` with "Algebra.Presentation,
MvPolynomial.pderiv, Algebra.FinitePresentation" returned no joint hit.
`msearch.py grep` with
"strictlyStandard|StrictlyStandard|elementaryStandard|ElementaryStandard"
returned no hit. `rg` for standard-element names in the source
`WeilConjectures` and project `lean/Sheaf` returned no hit;
`grep -rn` for this node id in source `WeilConjectures` returned no hit.
The node's earlier Mathlib searches also found no exact definition.

The node's proof discusses well-formedness and elementary implies strictly;
those are claims for later proof work and are not asserted as proved here.

## Second reading by K1

I reread the node, Definition 07C7, and
`lean/Sheaf/RingTheory/StrictlyStandardElement.lean` independently.

- The base objects are `{R : Type u}`, `{A : Type v}`, `[CommRing R]`,
  `[CommRing A]`, `[Algebra R A]`, and `[FinitePresentation R A]`; the element
  is `a : A`. These are exactly the node's ring map of finite presentation and
  element, with no Noetherian, characteristic, or universe restriction.
- A presentation and its finite data are rendered by
  `∃ (n m c : ℕ) (P : Presentation R A (Fin n) (Fin m))
  (hc : c ≤ min n m)`. `P` supplies the polynomial relations, the evaluation
  map `P.val`, and the lift `P.σ`; this is the recorded
  `Algebra.Presentation` dependency rather than a private presentation notion.
- The elementary equation (1) is rendered by
  `a = a' * Matrix.det (fun i j : Fin c =>
  aeval P.val (pderiv (...) (P.relation (...))))`, with the first `c`
  variables and first `c` relations. The casts from `Fin c` are justified by
  `hc`, so this is precisely the node's `(i,j)` minor.
- The elementary equation (2) is rendered by
  `∀ j : Fin m, c ≤ j.val → P.σ a * P.relation j ∈
  Ideal.span {f | ∃ k : Fin m, k.val < c ∧ f = P.relation k} +
  (Ideal.span (Set.range P.relation)) ^ 2`. This is exactly the source's
  `a f_{c+j}` membership condition, with the lift-independence convention.
- The strictly standard equation (3) is rendered by the sum over
  `{s : Finset (Fin n) // s.card = c}`, with one coefficient `a' s` and the
  determinant `fun j i : Fin c => ...`, using `orderEmbOfFin` to put columns
  in increasing order. This matches the node's rows `j = 1,…,c` and columns
  `i ∈ I`.
- The strictly standard equation (4) is the same relation-ideal clause above,
  as required by the node.

Edge cases checked: `n = 0` and `m = 0` are permitted; `c = 0` gives the
empty determinant and the unique empty subset; `c = m` makes the relation
clause vacuous; zero rings and arbitrary characteristics remain allowed. The
`Type u`/`Type v` binders do not exclude any node case.

Searches were repeated with `msearch.py` (`leanfinder`, `loogle`, and `grep`)
for strictly/elementary standard elements and Jacobian-minor definitions,
plus `rg` over Mathlib, `WeilConjectures`, and project `lean/Sheaf`; no exact
declaration exists. The dependency declarations used are
`Algebra.Presentation` from `Mathlib.RingTheory.Extension.Presentation.Basic`
and `MvPolynomial.pderiv` from `Mathlib.Algebra.MvPolynomial.PDeriv`.

No mismatch was found, so no source or Lean change was needed. The module
compiles cleanly with `scompile.py`; the node statement is represented by the
two definitions exactly as written above.
