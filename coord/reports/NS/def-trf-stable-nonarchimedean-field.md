## Worker report

The module `Sheaf.FieldTheory.StableNonarchimedeanField` defines
`IsStableNonarchimedeanField`. This is a full Prop-valued definition with no
`sorry`, theorem, extra hypothesis, helper definition, or new node. Only the
item's `lean` record changes. I downloaded and visually read the primary BGR
scan, PDF page 164 (printed page 156), Definition 3.6.1/1 and the following
paragraph. Its definition is precisely that every finite extension with its
spectral norm is a cartesian vector space; it imposes neither completeness nor
separability. The following paragraph includes algebraically closed fields.

Clause-by-clause rendering:

- The field k is `(K : Type u) [NormedField K]`. `NormedField` includes `Field`,
  and its real-valued norm is multiplicative; its metric is the one induced by
  that norm. `[IsUltrametricDist K]` makes the absolute value nonarchimedean.
  A real absolute value canonically supplies this normed-field structure, so
  the metric data add no mathematical restriction.
- Every finite-dimensional field extension E/k is quantified as
  `∀ (E : Type u) [Field E] [Algebra K E] [FiniteDimensional K E]`.
  The universe is tied to the base field, rather than independently smaller.
  This covers all finite extensions up to K-algebra equivalence: a finite
  basis identifies the underlying set with `Fin n → K`, in `Type u`, and
  the field structure transports there. Minimal polynomials, and therefore
  spectral norms and the displayed orthogonality property, are preserved by
  such equivalences. There is no size restriction on the mathematical notion.
- The minimal-polynomial norm s(E/k) is exactly Mathlib's `spectralNorm K E`,
  the function named by the spectral-norm dependency, not a chosen extending
  multiplicative norm. Its definition is `spectralValue (minpoly K z)`.
- Existence of a k-basis v_1,...,v_n, n = dim_k(E), is
  `∃ b : Module.Basis (Fin (Module.finrank K E)) K E`.
  Using indices 0,...,n-1 rather than 1,...,n only relabels the basis.
- All coefficients are `∀ a : Fin (Module.finrank K E) → K`.
- The left side of the formula is
  `spectralNorm K E (∑ i, a i • b i)`.
- The right side is `⨆ i, ‖a i‖ * spectralNorm K E (b i)`, an indexed
  supremum in ℝ. This is exactly the finite maximum: the index type is finite
  and nonempty, since a nonzero field extension has positive finite dimension.
  Its range is finite and bounded above, so no empty/unbounded conditional
  supremum convention is used.
- Neither the base nor the extension has a completeness or separability
  hypothesis. There is no `NontriviallyNormedField` assumption, so trivial
  absolute values are retained. E has no independently chosen norm or topology.

Dependencies read and used:

- `def-weil-field`: `mathlib_match = ["Field"]`; no `lean` record is needed.
  I read `Field`'s full signature and docstring in
  `Mathlib.Algebra.Field.Defs`; it is inherited by `NormedField`.
- `lem-trf-incomplete-spectral-algebra-norm`: its Mathlib record names
  `spectralAlgNorm`, `isNonarchimedean_spectralNorm`, and `spectralNorm_one`
  in `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`. I read their signatures,
  docstrings, all surrounding section variables, `spectralAlgNorm_def`,
  `spectralNorm`, `spectralValue`, and `spectralValueTerms`. The module publicly
  imports this dependency. The definition uses its underlying `spectralNorm`.
  The algebraic hypotheses required by the norm laws follow from finite
  dimensionality; they are not extra assumptions on the definition.
- I also read `NormedField`, `IsUltrametricDist`, `Module.Basis`, and
  `Module.finrank` in their Mathlib sources.

Edge cases checked before writing: E = K has its one-vector basis and the
formula reduces to the extension-of-norm identity. For all-zero coefficients
both sides are zero. A field extension cannot have dimension zero, so the
maximum is never empty. Trivial absolute values remain allowed: for algebraic
nonzero elements the monic minimal polynomial has nonzero constant coefficient
and spectral norm 1, so any basis gives the required formula. Positive
characteristic and inseparable extensions are not excluded. An incomplete
base is allowed; the definition does not invoke Mathlib's later complete-base
normed-field construction on E. Algebraically closed bases have only degree
one finite extensions, agreeing with the paragraph following BGR's definition.

Searches (2026-10-24, through msearch.py):

- LeanFinder: "A nonarchimedean valued field is stable when every finite field
  extension admits an orthogonal basis for the minimal polynomial spectral
  norm". Eight hits on spectralNorm, invariantExtension, and norm-extension
  results; none defines stability or the required orthogonal-basis predicate.
- Loogle: `"spectralNorm", "Basis"`. Zero hits.
- LeanSearch: "A stable nonarchimedean valued field is one whose every finite
  extension has an orthogonal basis for its spectral norm". Eight hits on
  spectralNorm and its associated algebra-norm/complete-space constructions;
  no stability predicate.
- Mathlib grep: `StableField|IsStableField|[Cc]artesian.*[Ff]ield|[Oo]rthogonal.*[Ss]pectral`.
  One irrelevant formal-multilinear-series Cartesian-product docstring.
- Direct rg of the project's `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` with that pattern: only unrelated Cartesian
  diagrams and Cartesian coefficient-module results. Searching the item id
  in WeilConjectures found nothing. A separate collision search for
  `StableNonarchimedeanField|StableNormedField|IsStableNonarchimedeanField`
  in Mathlib, upstream, Sheaf, and the upstream-name index had no hits.

The first required scompile.py run compiled both the sandbox view and the
library module without errors or warnings (3.9 s and 8.3 s respectively).
There are no node faults or statement disputes.

## Second reading by NS

This section records the dispatcher's single worker's second pass, not a claim
of an independent second agent: the assignment prohibits starting other agents
and assigns the independent delivery review to the maintainer. I reopened the
node, source page, and finished module. The field/absolute-value assumptions
are exactly NormedField plus IsUltrametricDist; every finite field extension
is quantified without completeness/separability; the basis has exactly finrank
indices; both sides use the dependency's minimal-polynomial spectralNorm; the
coefficient quantifier includes zero coefficients; and the finite real supremum
is a genuine nonempty maximum. The universe convention was checked via finite
coordinate models, and no false empty-dimensional case is admitted. No
mismatch or correction was found. No new or dependency modules need review.
