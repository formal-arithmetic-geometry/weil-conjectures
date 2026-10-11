## Worker report

The module `Sheaf.RingTheory.LciConormalFreeRankCodimension` states
`Ideal.exists_basis_cotangent_localization_of_completeIntersection`, with a `sorry` proof.
No new definitions, new nodes, dependency modules or statement corrections are needed.

Hypotheses and clauses:

- The field is `{k : Type u} [Field k]`, with explicitly declared universe `u`.
- The nonnegative integer number of variables is `(n : ℕ)`; the polynomial ring is
  `MvPolynomial (Fin n) k`, and `(I : Ideal (MvPolynomial (Fin n) k))` is its ideal.
- The ring `S` is literally `MvPolynomial (Fin n) k ⧸ I`, with the canonical `k`-algebra
  structure, and `q : PrimeSpectrum S` is its prime point. Its ideal is `q.asIdeal`.
- The hypothesis `hci` says `∃ g : S, g ∉ q.asIdeal ∧
  Algebra.IsGlobalCompleteIntersection k (Localization.Away g)`.
  It preserves exactly the existential hypothesis; there is no assumption of global
  complete intersection on `S`, smoothness, or a prechosen regular sequence for `I`.
- `∃ d : ℕ, topologicalKrullDimAt q = (d : WithBot ℕ∞)` says the dimension at the
  point is a finite nonnegative integer. `d ≤ n` is the upper bound. This uses the
  topological dimension at a point, not the Krull dimension of the local ring.
- `I.Cotangent` is Mathlib's quotient `I / (I • ⊤)` with its existing module action by
  `S = P/I`; it is the conormal module `I/I²`, not the cotangent space of `q`.
- `LocalizedModule q.asIdeal.primeCompl I.Cotangent` is localization of this `S`-module
  at `S \ q`. Its scalars are `Localization.AtPrime q.asIdeal`. The local instance
  `LocalizedModule.moduleOfIsLocalization` supplies the canonical fraction action.
- `Nonempty (Module.Basis (Fin (n - d)) (Localization.AtPrime q.asIdeal) ...)`
  asserts freeness and rank `n-d` together. Because `d ≤ n` is asserted alongside it,
  natural subtraction is the specified integer difference. A finite basis is equivalent
  to the stated finite-rank free module; this adds no chosen generators.

Dependency declarations read and used:

- `def-weil-pbc-mv-polynomial-ring`: Mathlib `MvPolynomial` in
  `Mathlib.Algebra.MvPolynomial.Basic`; also read `MvPolynomial.algHom_ext` and
  `MvPolynomial.aeval` in Basic/Eval for the node's universal-property clauses.
- `def-weil-pbc-complete-intersection-over-field`:
  `Algebra.IsGlobalCompleteIntersection` from
  `Sheaf.RingTheory.CompleteIntersectionOverField`, read in full, including its zero-ring
  convention, polynomial quotient presentation and dimension equality.
- `def-weil-affine-spectrum`: Mathlib `AlgebraicGeometry.Spec` / `Spec.map` from
  `Mathlib.AlgebraicGeometry.Scheme`, whose underlying topological space is
  `PrimeSpectrum S`; only that topological space is needed here.
- `def-kun-topological-dimension-at-point`: `topologicalKrullDimAt` from
  `WeilConjectures.Mathlib.Topology.KrullDimension`, read with its docstring and full
  definition as the infimum over open neighborhoods.
- `def-weil-pbc-module-localization`: `LocalizedModule` from
  `Mathlib.Algebra.Module.LocalizedModule.Basic`, read with its fraction definition and
  canonical localization-ring module structure.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime` from
  `Mathlib.RingTheory.Localization.AtPrime.Basic`. Read its full abbreviation and
  docstring; also read the dependency's `Ideal.ResidueField` and `Ideal.Fiber` clauses.

Edge cases checked before writing:

- `n = 0` is allowed; a proper quotient of the polynomial ring in zero variables over a
  field has dimension zero and zero conormal module, giving the empty basis `Fin 0`.
- `I = ⊥` gives a zero conormal module and local topological dimension `n`, hence rank zero.
- `I = ⊤` makes `S` the zero ring, whose spectrum has no points; there is no `q`, exactly
  as in the natural-language statement. No extraneous nonzero hypothesis is necessary.
- `d = n` uses an empty basis and expresses the zero module. Neither infinite dimension
  nor bottom is silently coerced to zero: the conclusion excludes them by its equality.
- Nonclosed prime points are included. Using the local ring dimension instead would fail
  already at the generic point of affine space; the recorded dimension definition is used.
- All characteristics and arbitrary field universe `u` are allowed.

Searches:

- `msearch.py ... leanfinder "At a local complete intersection point a polynomial quotient
  conormal module localized at a prime is free of rank number of variables minus dimension
  at the point"`: eight hits, smooth/standard-smooth localization statements and local
  cotangent-space facts; none states the complete-intersection result.
- `msearch.py ... loogle "Ideal.Cotangent, LocalizedModule"`: zero hits.
- `msearch.py ... grep 'Cotangent|conormal|CompleteIntersection' RingTheory/Ideal`:
  `Ideal.Cotangent` and cotangent-base-change constructions, no theorem of this statement.
- `rg -n 'lci|conormal|CompleteIntersection'` in source `WeilConjectures/RingTheory` and
  `WeilConjectures/AlgebraicGeometry`: only a deformation-to-normal-cone docstring mention.
- `rg -n 'lem-weil-pbc-lci-conormal-free-rank-codimension'` in source `WeilConjectures`:
  no tagged declaration.
- `rg -n 'conormal|CompleteIntersection|dimensionAt'` in project `lean/Sheaf/RingTheory`
  and `lean/Sheaf/Topology`: complete-intersection definition and separate conormal
  comparison/intersection/etale lemmas, no duplicate of this theorem.
- Read `Ideal.Cotangent` and its canonical `Module (R ⧸ I)` instance directly in pinned
  Mathlib; no private conormal or localization definition is introduced.

The cited local Stacks file is absent on this machine. Read the official
[Stacks Tag 00SC](https://stacks.math.columbia.edu/tag/00SC) instead: the node is its
implication (1) to (4), with codimension expressed as `n - dim_q(S)`.
The declaration docstring carries all six proof steps from the DAG, naming the lemmas
that supply each step. No statement dispute or dependency fault was found.

Validation: server single-file compilation and delivery dry run (results recorded below).

Server compilation passed with exit code 0 in 1.6 seconds, without warnings.
`deliver2.py E1 lem-weil-pbc-lci-conormal-free-rank-codimension --no-push` printed
`OK (dry run)`: compilation and preflight passed except for the independent second reading,
which the next worker supplies. Nothing was pushed.
A final whole-source `rg 'lci|conormal|CompleteIntersection'` found only the same
normal-cone docstring. The new theorem name was absent from `dag/lean_names_upstream.json`,
all pinned Mathlib sources, the whole upstream project and `lean/Sheaf`.

## Second reading by E1

Independent reading of the node, its six proof steps, the delivered Lean module, and
all six statement-dependency nodes and their recorded source declarations.
The local `literature/stacks-project/algebra.tex` is absent. I read the actual TeX
from https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex,
labels `definition-lci-field` (00S9) and `lemma-lci` (00SC), including the complete
proof of the latter, and checked the official rendered tags as well.
The source assumes a field and a finite type algebra throughout. The finite
polynomial quotient in this item already supplies finite type; a further instance
binder would be redundant. Implication (1) to (4), with the source's equality
`dim_q(S) = n - c`, is precisely this node. No source hypothesis is missing.

Object/hypothesis/conclusion inventory, with the corresponding Lean and verdict:

- Field k: `{k : Type u} [Field k]`. Exact; no characteristic or perfection assumption.
- Integer n >= 0: `(n : ℕ)`. Exact, including zero.
- Polynomial ring P = k[x_1,...,x_n]: `MvPolynomial (Fin n) k`. Exact, up to the
  harmless bijection of variable labels with `Fin n`. Read `MvPolynomial` in
  Mathlib/Algebra/MvPolynomial/Basic.lean: finitely supported sums of monomials,
  with coefficients in k. It is the dependency's polynomial ring.
- Ideal I of P: `(I : Ideal (MvPolynomial (Fin n) k))`. Exact; not required proper.
- Quotient S = P/I: every occurrence is literally `MvPolynomial (Fin n) k ⧸ I`,
  with its canonical quotient k-algebra. Exact; no unrelated algebra S is introduced.
- Prime ideal q of S: `(q : PrimeSpectrum (MvPolynomial (Fin n) k ⧸ I))` and
  `q.asIdeal`. Exact: a bundled prime, not a maximal or closed-point restriction.
  Read `AlgebraicGeometry.Spec` and `Spec.map` in Mathlib/AlgebraicGeometry/Scheme.lean;
  its underlying space is the same `PrimeSpectrum S` used in the statement.
- Existence of a complete-intersection principal neighborhood:
  `hci : ∃ g : S, g ∉ q.asIdeal ∧
  Algebra.IsGlobalCompleteIntersection k (Localization.Away g)`. Exact existential
  order and membership condition, with the canonical k-algebra localization action.
  Read all of Sheaf/RingTheory/CompleteIntersectionOverField.lean. The used definition
  is `Subsingleton T ∨ ∃ n c f, c ≤ n ∧ Nonempty ((k[Fin n]/span(range f)) ≃ₐ[k] T)
  ∧ topologicalKrullDim (PrimeSpectrum T) = ↑(n-c)`. This is exactly 00S9:
  c <= n makes the nonzero presentation's integer difference nonnegative, and the
  separate zero-ring clause is the source's convention. No regular-sequence or
  smoothness hypothesis has been substituted.
- Dimension d at q: `∃ d : ℕ, topologicalKrullDimAt q = (d : WithBot ℕ∞)`.
  Exact: d is determined by the stated topological dimension, rather than quantified
  independently as an assumption. Read the definition and docstring in
  WeilConjectures/Mathlib/Topology/KrullDimension.lean, LocalDimension section:
  `⨅ (U : Opens X) (_ : x ∈ U), topologicalKrullDim U`. This is the recorded
  dependency's minimum over open neighborhoods. It is not local-ring dimension.
- Bounds 0 <= d <= n: `d : ℕ` supplies the lower bound, and `d ≤ n` supplies the
  upper bound. Exact, with finiteness supplied by the dimension equality.
- Conormal S-module I/I²: `I.Cotangent`. Exact. Read its definition in
  Mathlib/RingTheory/Ideal/Cotangent.lean: quotient of I by `I • ⊤`, the derived
  `Module (P ⧸ I)` instance, and `map_toCotangent_ker`, which identifies the
  submodule's image with I². This is not the cotangent space of the prime.
- Localization of that module at S minus q:
  `LocalizedModule q.asIdeal.primeCompl I.Cotangent`. Exact. Read the abbreviation,
  `mk`, and `mk_eq` in Mathlib/Algebra/Module/LocalizedModule/Basic.lean: fractions
  with the usual relation. The multiplicative subset is in S, not in P.
- Local-ring scalars S_q: `Localization.AtPrime q.asIdeal`. Exact. Read its
  abbreviation in Mathlib/RingTheory/Localization/AtPrime/Basic.lean as localization
  at the prime complement. The file's local instance
  `LocalizedModule.moduleOfIsLocalization` supplies the canonical fraction action;
  it adds no hypothesis. Also opened the dependency's `Ideal.ResidueField` and
  `Ideal.Fiber` clauses; neither is needed to state this theorem.
- Freeness and rank n-d together:
  `Nonempty (Module.Basis (Fin (n - d)) (Localization.AtPrime q.asIdeal)
  (LocalizedModule q.asIdeal.primeCompl I.Cotangent))`. Exact. Read Basis/Defs.lean:
  a basis is a linear equivalence with finitely supported coordinate functions.
  Existence of this finite basis is equivalent to being free of the specified rank;
  it asserts no chosen generating sequence. Since `d ≤ n` is in the same conjunction,
  natural subtraction is the actual nonnegative integer difference, not truncation
  hiding a dimension mismatch. The local ring at a prime is nonzero, so the basis
  cardinality has its usual rank meaning.

Edge cases: n=0 is permitted and any q forces I proper, hence I=0 over k; the
conclusion has d=0 and the empty basis. I=0 for arbitrary n has zero conormal module,
d=n at every prime, and again `Fin 0`. I=top has zero quotient and empty spectrum,
so there is no q, as in the node. d=n gives an empty basis; d=0 gives rank n.
A nonreduced example k[x]/(x²) at (x) has d=0 and conormal rank one, so singular
complete intersections are retained. Generic/nonclosed primes are retained: for
k[x] at (0), topological dimension is one although the local-ring dimension is zero.
The dimension equality excludes bottom and infinity by conclusion, not by an extra
hypothesis. All field characteristics and every universe u are covered; P, S,
the conormal module and their localizations naturally live in that same universe.
There is no independent test-object universe or unbound variable.

Independent searches (different phrasing from the worker):

- `msearch.py ... leansearch "The localized relation ideal modulo its square in a
  finite polynomial algebra over a field has a basis of size codimension at a
  complete intersection prime"`: service unavailable (Internal Server Error),
  recorded by the search tool; no mathematical verdict inferred from the outage.
- `msearch.py ... loogle "Ideal.Cotangent, Module.Basis"`: zero hits.
- `msearch.py ... leanfinder "For a quotient of a polynomial ring over a field that
  is locally a complete intersection, its localized ideal quotient I modulo I
  squared is free with rank n minus local topological dimension"`: eight hits,
  concerning smooth loci, standard smooth presentations and cotangent spaces of
  maximal ideals; none gives this statement.
- `msearch.py ... grep 'complete.?intersection|conormal|basisCotangent'
  RingTheory/Smooth`: five hits in StandardSmoothCotangent.lean. Opened
  `SubmersivePresentation.basisCotangent` and its surrounding signatures: it
  requires a submersive presentation, a stronger condition than a complete
  intersection (e.g. k[x]/(x²)). It cannot replace this node.
- Independent `rg -n -i 'complete.?intersection|conormal|cotangent.*(rank|basis)|
  basis.*cotangent'` over the whole upstream WeilConjectures tree, repository
  lean/Sheaf, Mathlib/RingTheory/Ideal and Mathlib/RingTheory/Smooth found the
  existing complete-intersection definition, equidimensionality/localization
  lemmas, unrelated conormal comparisons and standard-smooth results, but no
  equivalent theorem. `rg` for the full new declaration name over pinned Mathlib,
  upstream WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json gave no hit.

H5/H6/H8/H9: no definitions, private copies or hollow data are introduced; the sole
new theorem has `by sorry`. Its docstring names 00SC and the exact blueprint id,
and carries all six node steps: localization and presentation; dimension and
 equidimensionality; regular sequence and conormal basis; exact localization;
comparison of presentations; finite projective/flat local freeness and rank.
The module docstring and namespace are correct. All imports name declarations
used by the statement, and all lines satisfy the 100-character bound.
The node's `lean.statement` agrees verbatim with the theorem signature.
No new definition nodes, dependency modules or statement corrections are present
or needed. No mismatch found; the Lean and node were left unchanged. The only
change is this independent review and its search evidence.

Validation: repeated server single-file compilation using the absolute sandbox
module path; delivery dry run and push results follow below.

Second-reader server compilation: exit code 0, 1.6 seconds, no warnings.
Second-reader `deliver2.py ... --no-push`: OK; preflight and compilation passed.
