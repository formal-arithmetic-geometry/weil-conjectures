## Worker report

The module states `AlgebraicGeometry.ProjectiveLine.koszul_resolution` for
`S = MvPolynomial (Fin 2) k`, with `I = Ideal.span {X 0, X 1}` and
`K = S ⧸ I`. The existential maps render the three displayed arrows: `f a =
(a * X 1, -a * X 0)`, `g (a,b) = a*x₀+b*x₁`, and `q` is the quotient map.
`Function.Injective f`, `Function.Exact f g`, and `Function.Surjective g` render
exactness at the first three terms; `q a = 0 ↔ a ∈ I` renders the quotient
kernel, and `g (f a)=0` renders the zero composite. The module docstring records
that the underlying copies carry the total-degree shifts `S(-2), S(-1)` from
`def-weil-pbc-proj-twisting-sheaf`, so multiplication maps have degree zero.

Dependencies consulted: `def-sc-p1-standard` (`AlgebraicGeometry.ProjectiveLine.TwistData`
in `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits`),
`def-weil-pbc-proj-twisting-sheaf` (`AlgebraicGeometry.Proj.twist`), and
`lem-sc-p1-linear-syzygy` (`MvPolynomial.exists_eq_mul_X_and_eq_neg_mul_X`). The
polynomial-domain dependency is a Mathlib leaf
`MvPolynomial.instIsDomainOfIsCancelAdd`.

Edge cases checked in the source statement: zero syzygy (`c = 0`), the generator
syzygy `(x₁,-x₀)` (`c = 1`), and characteristic two; the existential formulation
also permits the zero field-polynomial elements and all fields.

Searches: `msearch.py leanfinder "Koszul complex exact regular sequence x0 x1 polynomial ring"`
(no exact graded declaration); `msearch.py loogle "Koszul exact regular sequence"`
(no graded match); grep of Mathlib for `Koszul.*exact|regularSequence.*koszul`
(no match); `rg` of WeilConjectures found only the sheaf-level
`ProjectiveLine.koszul_shortExact`, which is a different statement.

## Earlier second reading (a previous round; superseded)

The statement was reread clause by clause against the blueprint source. The three arrows, exactness clauses, quotient identification, and zero composite are all present; shifts are documented as the total-degree shifts in the module header.

## Second reading by F1

Read the node, the delivered Lean, both statement-dependency nodes and their
recorded source declarations, and the linear-syzygy node and its landed module.
The local literature checkout lacks the cited files, so I read the blueprint
and Stacks algebra.tex/constructions.tex through read-only SSH on the server.
The blueprint's graded-resolution statement assumes a field and cites graded
Hilbert syzygy; it does not literally display this Koszul sequence. The node
is the stage-1 agent's explicit algebraic expansion. Stacks algebra.tex,
Section 00JL, lines 13230–13238, gives exactly M(d)_n = M_(d+n).
There are no further standing hypotheses on the field.

Clause-by-clause checklist and verdicts:

- Arbitrary field k: `{k : Type u} [Field k]`, with bound universe `u`.
  Correct; no characteristic, finiteness, or extra instance hypothesis.
- S = k[x₀,x₁]: `S[k]` is local notation for `MvPolynomial (Fin 2) k`.
  Correct; the two indices are precisely 0 and 1.
- Standard total grading: Mathlib `IsWeightedHomogeneous w a n`, with
  `w = fun _ : Fin 2 => (1 : ℤ)`. Its definition says every nonzero monomial
  coefficient has weight n, hence its ordinary total degree, cast to ℤ, is n.
  Correct, including negative degrees.
- S(-2) and S(-1)²: their underlying S-modules are S and S × S. The two
  homogeneity clauses use degree n-2 for the source, degree n-1 for both
  middle coordinates, and degree n for the target. Correct by the exact
  shift convention in the dependency node's clause (2).
- First displayed arrow: S-linear `f` with `f a = (a * X 1, -a * X 0)`.
  Correct.
- Second displayed arrow: S-linear `g` with `g p = p.1 * X 0 + p.2 * X 1`.
  Correct.
- k = S/(x₀,x₁) and quotient arrow: `S[k] ⧸ I[k]`, with I[k] exactly the
  span of the two variables, and S-linear `q a = Ideal.Quotient.mk I[k] a`.
  Correct; the node explicitly identifies k with this quotient.
- Exactness at the first nonzero term: `Function.Injective f`. Correct.
- Exactness at the middle: `Function.Exact f g`. Correct; Mathlib's
  definition says g y = 0 iff y is in the range of f.
- Exactness at S: `Function.Exact g q`. Correct; this was missing.
- Exactness at the quotient and final zero: `Function.Surjective q`.
  Correct; this was missing. The first worker instead asserted surjectivity
  of g, which is false: its image is the proper ideal (x₀,x₁), so 1 is not
  in that image. Removed that erroneous assertion.
- Quotient kernel and complex condition: `q a = 0 ↔ a ∈ I[k]` and
  `g (f a) = 0`. Correct; retain the first worker's explicit clauses.
- Every map homogeneous of degree zero: the last three conjuncts assert
  f takes degree n-2 into degree n-1 in both coordinates, g takes the pair
  of degree n-1 coordinates into degree n, and q kills every homogeneous
  component of degree n ≠ 0. The latter is exactly homogeneity into the
  quotient concentrated in degree zero (at n = 0 no constraint is needed).
  Correct; the original Lean had no such conjuncts despite its docstring.

Dependency reading: `ProjectiveLine.TwistData` describes trivializations of
sheaf twists on the standard cover, not shifted graded modules. `Proj.twist`
defines the sheaf O(d), not S(d). Neither declaration is an object needed in
this ring-level statement, and neither is used as a substitute for S(d).
The shift clause (2) is rendered directly by integer degree indices using
Mathlib's existing homogeneity predicate; no private shift definition or
extra definition node is needed. The syzygy dependency's landed theorem
`MvPolynomial.exists_eq_mul_X_and_eq_neg_mul_X` has exactly the field,
two-variable ring, relation, and existential multiple needed in proof step 3.
No dependency modules or new nodes are delivered.

Edge cases: zero polynomials are homogeneous in every integer degree by
Mathlib's coefficient definition; negative-degree components are zero,
not excluded by a natural-number index or truncated subtraction. At n = 0,
the shifted source and middle components are zero and the quotient keeps
constants; at n = 1 the first component is zero; at n = 2 the generator
syzygy (x₁,-x₀) is the image of 1. Characteristic two is covered because the
minus sign has its usual additive meaning. Arbitrary field universes are
allowed. There is no variable index set that may be empty: Fin 2 is part of
the statement. Empty schemes and a zero coefficient ring are not cases of
this field-polynomial statement.

Independent searches (different wording from the first worker):

- `msearch.py leanfinder "Exact polynomial sequence multiplication by two
  indeterminates with quotient by their ideal"`: eight hits, including
  cotangent-complex exactness and Ideal.exact_mulQuot_quotOfMul; none states
  this graded polynomial sequence.
- `msearch.py loogle "MvPolynomial.IsHomogeneous"`: twelve hits; the existing
  Mathlib total-degree homogeneity notion is usable, but no Koszul resolution.
- `msearch.py leansearch "exact sequence of graded modules polynomial ring
  two variables quotient by variables"`: service returned Internal Server
  Error, recorded as unavailable, not a negative search verdict.
- Independent rg of Mathlib RingTheory and Algebra/Homology for Koszul,
  syzygy, and graded resolutions, and of WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json: no exact matching declaration. Opened the
  upstream ProjectiveLine.koszul_shortExact: its objects are O(m), O(m+1)²,
  O(m+2) on a scheme and it has no final residue-field quotient; it is a
  different sheaf-level statement. The project's ExteriorAlgebra Koszul
  complex is a general exterior-power construction, not this statement.
  Opened Mathlib WeightedHomogeneous.lean: IsWeightedHomogeneous and
  weightedHomogeneousSubmodule already provide the required grading, so
  used the former rather than defining another notion.

Repairs: removed the false surjectivity of g; added exactness at S and
surjectivity of q; made maps S-linear; added all three homogeneity clauses
with the actual integer shift indices; removed the three statement-level
let binders, using parameterized local notation; added the standard license
header and replaced the misleading docstring with the four proof steps and
explicit source references. Removed the unused syzygy import (the proof
remains sorry; the docstring names the dependency). The node statement and
its proof and dependencies are unchanged. There is one named theorem with
sorry and no definitions or proved lemmas. All variables and universes are
bound; the node's lean.statement is the file signature verbatim after
whitespace normalization.

Validation: scompile.py on the repaired 73-line module returned exit code 0
with no warnings. The delivery dry run returned OK: preflight passed and
the module compiled. No node-statement correction was required.
