## Worker report

The module `Sheaf.RepresentationTheory.BoundedFiniteEvaluationRectangleReplacement`
states `ContinuousCohomology.exists_boundedFiniteEvaluationRectangleReplacement`.
This is the sole declaration and its proof is `sorry`. There are no new definitions,
new nodes, dependency repairs, or statement changes. The existing stage-1 split is
retained verbatim; its reviewed status concerns the natural-language argument, not
an existing Lean statement. The earlier stale-assignment notice concerned repeating
stage 1, whereas this delivery supplies stage 2.

Source read: the current main-20261015 blueprint direct-images proof, paragraph (3),
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`,
and all fourteen steps of this auxiliary node. As the node explicitly says, its
quantitative finite-evaluation construction is an agent-written expansion below
that paragraph; an exact literature reference remains WANTED. No external source
is represented as stating the quantitative lemma verbatim.

Hypotheses and clauses, individually:

- Prime ell: `(l : ℕ) [Fact l.Prime]`; its field is exactly `ℚ_[l]`.
- Profinite G: `(G : Type u)` with `Group`, `TopologicalSpace`,
  `IsTopologicalGroup`, `CompactSpace`, `T2Space`, `TotallyDisconnectedSpace`.
  This is precisely a compact Hausdorff totally disconnected topological group.
- Open subgroup: `(H : OpenSubgroup G)`, with its actual induced topology;
  `H.toSubgroup.index` is the node's m. Openness and compactness make it finite.
  `(hindex : Nat.Coprime H.toSubgroup.index l)` says m is prime to ell.
  No normality assumption is added.
- Positive degree: the node's degree N is written `n + 1`, for `(n : ℕ)`.
  Consequently N-1 is `n` and the anchors are `(a : Fin (n + 2) → G)`.
  This reindexing covers exactly all N >= 1 without casts between tuple sizes.
- Coefficient space: `∀ (V : Type v) [NormedAddCommGroup V]
  [NormedSpace ℚ_[l] V]`. These supply the separated norm, norm topology,
  pointwise vector-space operations, and the exact scalar norm identity.
  `(∀ x y : V, ‖x + y‖ ≤ max ‖x‖ ‖y‖)` is precisely the extra ultrametric
  inequality. There is no completeness hypothesis.
- Continuous cochains: `C(Fin (n + 1) → G, V)` and `C(Fin n → G, V)`
  are exactly C^N and C^(N-1). They consist of jointly continuous functions
  on the finite products; no discreteness or iterated-map convention is used.
- Trivial action and differential: the initial face is `c (fun i ↦ g i.succ)`;
  the remaining faces are
  `∑ j, (-1 : ℚ_[l]) ^ (j.val + 1) • c (Fin.contractNth j (· * ·) g)`.
  `Fin.contractNth` multiplies adjacent entries for j before the final index,
  and at that final index omits the last entry. The same formula is displayed
  for the cocycle condition, residual cocycle condition, and coboundary of T c.
  Thus every sign and both end faces match the node. These pointwise equations
  specify the differential already written in the node; they introduce no
  second named cochain complex or differential.
- Fixed finite evaluations: the outer existential binds `(t r : ℕ)`,
  coefficients `α : Fin t → ℚ_[l]`, `β : Fin r → ℚ_[l]`, and continuous maps
  `ψ : Fin t → C(G^n,G^(n+1))`, `χ : Fin r → C(G^(n+1),G^(n+1))`.
  All are chosen before `∀ V`, hence independently of V and of its cochains.
  Their coefficient bounds are the first two conjuncts `∀ j, ‖α j‖ ≤ 1` and
  `∀ j, ‖β j‖ ≤ 1`.
- Linear operators: the inner existential binds the specified Q_l-linear
  `T` and `R` on the continuous cochain spaces. The next two conjuncts give
  their exact pointwise finite-sum formulas for every cochain and tuple.
  No arbitrary maps are substituted for the evaluation formulas.
- For every cocycle: the displayed degree-N cocycle equation is the antecedent
  of the next universal implication. Its three conclusions are the same
  cocycle equation for `R c`, the pointwise identity `c = d(T c) + R c`,
  and annihilation of the residual under rectangle vanishing.
- Rectangle: quantify `x : Fin (n + 2) → H`. The tuple
  `((x i.castSucc : G) * a i.castSucc)⁻¹ * ((x i.succ : G) * a i.succ)`
  is exactly the consecutive-ratio tuple of a point of
  H a_0 × ... × H a_N. Requiring c of it to vanish is the node's condition
  on f_c, and the conclusion is equality `R c = 0` as a continuous cochain.
- Supremum-norm bound one: `∀ c, ‖T c‖ ≤ ‖c‖ ∧ ‖R c‖ ≤ ‖c‖` uses
  Mathlib's supremum norm on continuous maps from compact spaces. Completeness
  of V is not needed for this norm. The bound also implies continuity of the
  linear operators; no extra operator-topology assumption is imposed.
- Every linear coefficient subspace: quantify `W : Submodule ℚ_[l] V` and c
  with `∀ x, c x ∈ W`; conclude both `∀ x, T c x ∈ W` and
  `∀ y, R c y ∈ W`. In particular nonclosed subspaces are included.
- Profinite parameter families: quantify arbitrary `S : Profinite.{w}` and
  `c : C(S × G^(n+1), V)`. The final two conjuncts assert continuity of
  `(s,x) ↦ Σ α_j c(s,ψ_j x)` and `(s,y) ↦ Σ β_j c(s,χ_j y)`.
  They keep the same parameter s fixed. The earlier T/R formulas identify
  these functions on each slice with T and R of that slice, so the already
  asserted cocycle and rectangle identities apply separately at every s.
  There is no exchange of jointly continuous and separately continuous maps.

Recorded statement dependencies read and used:

- `def-weil-l-adic-numbers`: its `mathlib_match` is `Padic`,
  `Mathlib.NumberTheory.Padics.PadicNumbers`. Its docstring and definition
  identify Q_l as the Cauchy completion of Q for the l-adic norm. The module
  imports that declaration and uses its notation and normed-field structure.
- `def-weil-size-convention`: its recorded convention has no declaration.
  The explicit universes `u v w` separate the group, coefficients and parameter
  space. No site skeleton or derived category is required in this statement.

Proof dependencies: plain imports of
`Sheaf.RepresentationTheory.TopologicalHomogeneousCochainCoordinates`
(`ContinuousCohomology.exists_jointContinuousCochainCoordinates`, with the full
`JointContinuousCochainCoordinates` specification read) and
`Mathlib.LinearAlgebra.FreeModule.Basic` (`Module.Free`). The recorded
`lem-sfb-ordered-join-partial-contraction` currently has no Lean record or
Mathlib match, so there is no module to import for it yet. It is used only in
the proof, not in the statement. The docstring retains all fourteen proof steps,
including the ordered-join contraction's exact degree range, input-dependent
anchors on basis tuples, the augmented homotopy induction and finite-coset
averaging for a possibly nonnormal subgroup.

Edge cases checked before delivery:

- N=1 is n=0. `Fin 0 → G` is a one-point space. For the coboundary of T c,
  the initial face and the sole final face have the same empty tuple and
  coefficients 1 and -1, so the formula gives the stipulated d^0=0.
- V=0 and other incomplete normed spaces are allowed. No Nontrivial or
  CompleteSpace binder on V appears.
- H=G has index one, and no properness requirement appears. Nonnormal open
  subgroups remain included; the proof averages right cosets without using
  a quotient-group structure.
- Empty finite evaluation lists are syntactically allowed. The existential
  theorem still requires every asserted identity; this does not assume a
  list is empty or weaken the conclusion.
- Empty S is allowed because `Profinite` has no Nonempty assumption. Both
  family-continuity statements then have empty domain.
- The zero subspace, whole space and nonclosed subspaces are all quantified.
- All group, coefficient and parameter universes are independent. Explicit
  `set_option autoImplicit false` checks that every variable is bound.

Searches run for an existing exact statement:

1. `msearch.py ... leanfinder` query:
   "Bounded finite sums of evaluations replace continuous group cocycles by a
   residual detected on a rectangle of open subgroup cosets uniformly in
   nonarchimedean coefficient spaces".
   Eight hits, led by
   `ContinuousMap.exists_finite_sum_smul_approximation_of_mem_uniformity`,
   finite-product approximation and nonarchimedean-group lemmas. None constructs
   an exact cochain replacement or asserts its rectangle and norm properties.
2. `msearch.py ... loogle` query: `"ContinuousMap", "sum"`.
   Twelve hits, including `ContinuousMap.sum_apply`, `coe_sum` and `tsum_apply`.
   These concern sums of continuous maps, not the cochain operators.
3. `msearch.py ... grep` query:
   `(rectangle|finiteEvaluation).*(cochain|cocycle)|(cochain|cocycle).*(rectangle|finiteEvaluation)`
   in `RepresentationTheory`: zero hits.
4. `msearch.py ... leansearch` query:
   "Norm one linear operators on continuous group cochains given by coefficient
   independent finite evaluation formulas and annihilating cocycles vanishing
   on a rectangle".
   Eight hits: low-degree cocycles and general operator norms. No exact match.
5. Project `rg` searches in both `lean/WeilConjectures` and `lean/Sheaf` for
   rectangle/cocycle and bounded/evaluation combinations, plus the exact node id
   with `grep -rn` in `lean/WeilConjectures`: no existing exact statement.
   `HomogeneousCocycleRectangleDetection` supplies only an existential subgroup
   primitive; `ContinuousCochainFiniteIndexTransfer` supplies transfer without
   the requested finite-evaluation rectangle residual and norm-one bounds.
   Both were read, as was Mathlib's inhomogeneous differential and the actual
   `Fin.contractNth` definition. None is this stronger quantitative statement.

Validation: `scompile.py` compiled the module separately as sandbox and library
module, cleanly within the fixed 60-second limit. The final module has one
named postponed theorem, no helper axioms, no data chosen from sorry, no probes,
no private declarations and no local instances or notation.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
