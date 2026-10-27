## Worker report

The module `Sheaf.RingTheory.MonotoneBoundaryBox` states
`MonomialDiagram.monotone_boundary_box`, with `sorry` as its only proof.
No definitions, dependency repairs, new nodes, or statement corrections are needed.
The node copy changes only `lean`.

The source is the agent elementary refinement recorded in this node's statement
and four proof steps, historically motivated by Bierstone--Milman (1997), section 8,
Lemma 8.2 and Remarks 8.4, pp. 274--275. I read the current blueprint ancestor
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md`
and its proof. As the stage-1 report records, that current blueprint ancestor now concerns
contracting correspondences; it does not state this auxiliary combinatorial lemma.
The mathematical assertion and full elementary argument here are those of the assigned
DAG node; no claim is made that the present blueprint ancestor or ILO states this bound.

Hypothesis and conclusion correspondence:

- `n ≥ 1` is `{n : ℕ} (hn : 1 ≤ n)`.
- Exponent vectors of the polynomial ring in `n` variables over `ℤ` are exactly
  `Fin n →₀ ℕ`, the monomial exponent type in `MvPolynomial (Fin n) ℤ`.
  Since `Fin n` is finite, this includes every vector of `ℕ^n`. Labels are shifted
  from `1,...,n` to `0,...,n-1`, preserving every order comparison and final index.
- The finite set is `(A : Set (Fin n →₀ ℕ)) (hA : A.Finite)`, without a nonempty,
  minimality, irredundancy, or ordered-vertex-family assumption.
- The integer `M ≥ 1` is `(M : ℤ) (hM : 1 ≤ M)`. It is not replaced by a natural
  parameter. `hdegree` says for every `a ∈ A` that the natural total coordinate sum,
  cast to `ℤ`, is at most `M`.
- The displayed union `U = ⋃ a ∈ A, (a + ℕ^n)` is Mathlib's `upperClosure A`.
  Its defining predicate is `∃ a ∈ A, a ≤ x` (`mem_upperClosure`). These are exactly
  the same sets: an orthant element dominates its generator; a dominating vector
  is the generator plus its coordinatewise natural difference. No independent
  choice of `U` or extra hypothesis is introduced.
- Coordinatewise order is Mathlib's order on `Finsupp`; `Finsupp.single k 1` is `e_k`.
  Scalar multiples `u_p e_p` are `Finsupp.single p (u p)`.
- The whole-coordinate transfer assumption is `htransfer`, quantified over every
  `u ∈ upperClosure A` and every `p t : Fin n` with `p < t`. Natural subtraction
  is pointwise, so subtracting `Finsupp.single p (u p)` zeros exactly coordinate `p`.
- The chosen coordinate and vector are `(k : Fin n) (v : Fin n →₀ ℕ)`;
  `hv` is `v ∉ upperClosure A`, and `hvk` is membership of `v + e_k`.
- The conclusion `∃ a ∈ A` supplies the required actual generator.
  `a k = v k + 1 ∧ 0 < a k` renders both the equality and strict positivity.
  `∀ t : Fin n, t ≠ k → a t ≤ v t` renders every other-coordinate inequality.
  `∀ j : Fin n, k ≤ j → (v j : ℤ) < M` renders the entire boundary box,
  including coordinate `k`, using the original integer bound.

Dependencies and source declarations read:

- `def-weil-pbc-mv-polynomial-ring`: recorded module
  `Mathlib.Algebra.MvPolynomial.Basic`, declaration `MvPolynomial`, imported publicly.
  I read its full abbreviation and docstring: `AddMonoidAlgebra R (σ →₀ ℕ)`.
  I also read the recorded universal-property declarations `MvPolynomial.algHom_ext`
  in that module and `MvPolynomial.aeval`/`aeval_unique` in
  `Mathlib.Algebra.MvPolynomial.Eval`. This combinatorial statement only needs
  the exponent type, so evaluation is not imported separately.
- `Mathlib.Order.UpperLower.Closure`: `upperClosure` and `mem_upperClosure` give
  the existing upper-set construction directly; no private replacement is defined.
- The item has no proof dependencies. The docstring gives all four elementary
  proof steps, including the exact transferred-coordinate comparisons.

Searches for an existing statement:

- `msearch.py ... leanfinder` with query
  "For an upper set of natural exponent vectors generated in total degree at most M
  and closed under transferring a whole earlier coordinate to a later coordinate,
  its one step coordinate boundary has all later coordinates less than M": eight
  hits, headed by `FormalMultilinearSeries.mem_compPartialSumSource_iff` and
  `ChevalleyThm.MvPolynomialC.degBound`; none states this boundary bound.
- `msearch.py ... loogle 'upperClosure, Pi.single'`: zero hits.
- `msearch.py ... grep
  'monotone.?boundary|monomial.*boundary|boundary.*monomial|strongly.?stable'
  RingTheory`: zero hits.
- `msearch.py ... leansearch` with query
  "Boundary of an upward closed subset of natural vectors stable under whole
  coordinate transfers is bounded by the total degree of its finite generators":
  eight hits, including `BddBelow.upperClosure`, finite-generation instances for
  bounded polynomial submodules, and Chevalley degree bounds; no matching theorem.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and Mathlib for
  `monotone_boundary_box|monotoneBoundaryBox|boundary_box`, and of
  `dag/lean_names_upstream.json`, found no existing declaration with the chosen name.
  A separate search for this exact blueprint id in `lean/WeilConjectures` found none.
- Conceptual searches in `lean/WeilConjectures` and `lean/Sheaf` for
  `monotone.?boundary|monotone.?diagram|boundary.*box|whole.coordinate` found
  `SupportedHomogeneousDivision`, `MonotoneDiagramFaceExceptions`, and
  `InitialDiagramStabilization`. I read the first two modules. They define
  monotonicity and indexed generated diagrams, or assert finiteness of translated
  vertex-region exceptions, respectively. None states the present result for an
  arbitrary finite generator set and arbitrary integer bound. The generic Mathlib
  `upperClosure` already gives the needed union of orthants.

Edge cases checked before delivery:

- For `A = ∅`, `upperClosure A` is empty, so `hvk` cannot hold.
- If `U` is the whole exponent space (e.g. `0 ∈ A`), `hv` cannot hold.
- At `n = 1` and at the final coordinate in any dimension, the transfer quantifiers
  to later coordinates are empty; the witness still bounds the current coordinate.
- For `M = 1`, boundary coordinates at or after `k` must be zero; the witness has
  `a k = 1`. Nonminimal/redundant generators are allowed throughout.
- A finite Python enumeration checked 136 generator families satisfying transfer
  closure and 409 boundary instances, for `n = 1,2,3` and `M = 1,2`, with generator
  subsets of size at most three and total degree at most `M`, and test vectors
  with coordinates through `M+1`. Both witness and all later-coordinate bounds
  held. Transfer closure was tested on generators, which is sufficient for the
  whole generated upper set: transferring a vector above a generator leaves it
  above that generator's transfer.
- All variables are explicitly bound, and `set_option autoImplicit false` enforces
  the requirement. There are no extra structure or characteristic assumptions.

Validation: the prescribed `scompile.py Q61 lem-trf-monotone-boundary-box` compiled
both its sandbox check and the actual module cleanly (1.7 s and 1.2 s).

## Second reading by Q61

This is the worker's second pass, not an independent-agent review; the prompt
forbids starting other agents, and the maintainer independently reviews the delivery.
I reopened the node and the completed module and compared each binder and clause.
The signature retains finite `A`, positive integer `M`, the total-degree bound,
transfer for all upper-set members and every strictly ordered coordinate pair,
and both boundary membership conditions. Its existential keeps the same generator
for the equality, positivity, and all other-coordinate comparisons; the later-box
bound uses all `j ≥ k`. The standard upper closure exactly equals the specified
union of natural orthants, and finite-support exponents exclude no vector because
the coordinate type is finite. The final-coordinate and empty/full cases remain
vacuous for exactly the reasons recorded in the node. No mismatch or source-based
correction was found, and no statement was changed during this pass.
