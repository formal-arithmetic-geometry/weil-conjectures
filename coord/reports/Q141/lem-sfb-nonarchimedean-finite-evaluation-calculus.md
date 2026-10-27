## Worker report

The module `Sheaf.Analysis.Normed.FiniteEvaluationCalculus` states
`ContinuousMap.nonarchimedean_finiteEvaluation_calculus`, with one postponed theorem
proof. Its two helper definitions, `ContinuousMap.finiteEvaluationLinearMap` and
`ContinuousMap.finiteEvaluationParameterMap`, implement the operators named in this
node: the former is the finite sum of scalar multiples of Mathlib's
`ContinuousMap.compCLM.toLinearMap`, and the latter uses that same construction on
`id_S × b_i`. Both contain actual data and no postponed proofs. They belong to this
node's own evaluation formulas, not an independent new notion. All three declarations
are listed in `lean.declarations` and have source/blueprint docstrings.

The node and its source were read. The source text used is the current
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3), together with the retained scalar tame-kernel expansion in this node's
six proof steps and the rectangle-replacement module's steps 12–14. The blueprint
paragraph itself does not assert this analytic auxiliary lemma; the existing node
correctly identifies it as an agent-formulated expansion. No different literature
claim is attributed to it. There is no statement correction, new node, or dependency
repair in this delivery.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Prime ℓ and its field/absolute value: `(l : ℕ) [Fact l.Prime]`, `ℚ_[l] = Padic l`,
  and Mathlib's norm on this field. These are exactly the Mathlib match of
  `def-weil-l-adic-numbers`. The actual definition and its completion docstring in
  `Mathlib.NumberTheory.Padics.PadicNumbers` were read, as were `norm_int_le_one`
  and `norm_natCast_eq_one_iff` for the final clause.
- Nonempty compact topological spaces X and Y: independent `Type u`, `Type v`,
  `[TopologicalSpace X/Y]`, `[CompactSpace X/Y]`, `[Nonempty X/Y]`.
  Neither Hausdorff nor local compactness is imposed.
- Finite I, continuous b_j, coefficients λ_j: `(I : Type t) [Fintype I]`,
  `b : I → C(Y, X)`, `c : I → ℚ_[l]`. A finite set is represented by its finite
  index type. No nonemptiness is assumed of I.
- B ≥ 0 and every coefficient bounded by B: `B : ℝ`, `hB : 0 ≤ B`,
  `hc : ∀ i, ‖c i‖ ≤ B`.
- Normed coefficient vector space V: independent `Type w`, `[NormedAddCommGroup V]`,
  `[NormedSpace ℚ_[l] V]`; this already entails `norm_smul`, the exact equality
  `‖a • v‖ = ‖a‖ * ‖v‖`. The nonarchimedean hypothesis is precisely
  `hV : ∀ v w : V, ‖v + w‖ ≤ max ‖v‖ ‖w‖`. Its topology comes from the normed
  group. There is no completeness or nontriviality assumption on V.
- Linear map and evaluation formula: `finiteEvaluationLinearMap` has type
  `C(X,V) →ₗ[ℚ_[l]] C(Y,V)`, and the first conjunct gives its exact pointwise sum.
  Its definition uses existing composition maps rather than an arbitrary existential
  linear map or a separately assumed continuity proof.
- Finite supremum norms: the second conjunct gives `BddAbove (Set.range ...)` for
  both pointwise norm functions and identifies their real suprema with the actual
  Mathlib continuous-map norms via `‖f‖ = ⨆ x, ‖f x‖` and its output analogue.
  The same conjunct states `‖finiteEvaluationLinearMap ... f‖ ≤ B * ‖f‖`.
- Every linear coefficient subspace, closed or otherwise: the next conjunct
  quantifies over `W : Submodule ℚ_[l] V`, assumes `∀ x, f x ∈ W`, and concludes
  `∀ y, finiteEvaluationLinearMap ... f y ∈ W`. No `IsClosed` appears.
- Arbitrary topological parameter S: `∀ (S : Type s) [TopologicalSpace S]`.
  The inputs are exactly continuous `f : C(S × X,V)`. The parameter conjunct
  asserts continuity of the raw finite formula, identifies it with the actual
  `finiteEvaluationParameterMap`, and equates its value at `(q,y)` with L applied
  to `f.comp ((ContinuousMap.const X q).prodMk (ContinuousMap.id X))` at y.
  That composition is exactly the continuous slice x ↦ f(q,x).
- Pointwise linear identities on parameter families: the next subclause allows
  an arbitrary finite index A of formulas, separate finite term types `J : A → Type r`,
  separate maps `d`, coefficients `e`, linear-combination coefficients `α`, and
  input families `f : A → C(S × X,V)`. A zero identity for the linear combination
  on every slice implies the corresponding pointwise zero identity on `S × Y`.
  Subtracting two sides expresses equality identities in this form. There is no
  coefficient-norm assumption on this algebraic transfer clause.
- Empty lists give zero operators: the `IsEmpty I` implication gives both
  `finiteEvaluationLinearMap ... = 0` and `finiteEvaluationParameterMap ... S = 0`
  for every topological S. Empty S gives the unique family: its `IsEmpty S`
  implication states equality of any two continuous maps on `S × Y`.
- Closure under composition: arbitrary nonempty compact Z, finite J, continuous
  `d : J → C(Z,Y)`, and coefficients e give equality of the composite linear map
  with the formula indexed by `J × I`, maps `(b q.2).comp (d q.1)` and coefficients
  `e q.1 * c q.2`. The product-index sum is the displayed double sum in the node.
  The choices of index, maps, and coefficients contain no dependence on V.
- Precomposition by any fixed continuous u: the next conjunct equates
  `(L f).comp u` with the same evaluation formula using `(b i).comp u`.
- Positive denominator prime to ℓ: `∀ (m : ℕ), 0 < m → Nat.Coprime m l → ...`.
  First every `k : ℤ` has `‖(k : ℚ_[l]) / (m : ℚ_[l])‖ ≤ 1`; next the formula
  with those coefficients has supremum norm at most `‖f‖`; finally the same
  estimate holds after arbitrary continuous coordinate precomposition.
  The subspace and parameter clauses apply to these coefficients by specializing
  c and B = 1, using the stated coefficient bound. They are not omitted or
  replaced with additional completeness/closedness assumptions.
- V = 0 and singleton cochain domains are included by the unrestricted coefficient
  and space types; the statement imposes no `Nontrivial V` or cardinality condition
  on X/Y/Z beyond nonemptiness.

Dependency declarations and imports:

- `def-weil-l-adic-numbers` is a Mathlib leaf. Used `Padic` / `ℚ_[l]` and its norm
  from `Mathlib.NumberTheory.Padics.PadicNumbers` (public import). No duplicate
  field or absolute value is introduced. The recorded dependency has no `lean`
  field and needs none.
- The proof dependency `lem-sfb-compact-real-function-minimum` is the Mathlib leaf
  `IsCompact.exists_isMinOn`, `Mathlib.Topology.Order.Compact`. Its signature and
  docstring were read. It is a plain proof import and is named in proof step 2.
- `Mathlib.Analysis.Normed.Module.Basic` supplies the coefficient-space assumptions;
  `Mathlib.Topology.ContinuousMap.Compact` supplies the actual supremum norm and
  exposes `ContinuousMap.compCLM`, product maps, and algebraic operations.
  Read the full `compCLM` definition in `ContinuousMap.Algebra`, the compact norm
  definitions and `norm_le`/`norm_eq_iSup_norm`, and product-map definitions.

Edge cases checked before finalization: empty I, empty J, empty identity index A,
empty S, B = 0, zero coefficients, zero integer k, m = 1, the zero vector space,
one-point X/Y/Z, and compact spaces without separation. Empty sums are zero, so
B ≥ 0 handles the estimate even without any term. No supremum on the possibly
noncompact parameter space S is taken. The prime-to-ℓ assumption excludes division
by a nonunit denominator; e.g. m = 2 at ℓ = 3 is allowed, m = 2 at ℓ = 2 is not.
All universe parameters and variables are explicitly bound, with `autoImplicit false`.
No `STATEMENT-DISPUTED` issue was found.

Searches (2026-10-24; exact receipts are in the sandbox `searches.jsonl`):

- `msearch.py leanfinder`, query “Finite continuous evaluation sums on nonarchimedean
  normed spaces preserve subspaces and continuous parameter families and are bounded
  by the maximum coefficient norm”: eight hits, including
  `IsUltrametricDist.exists_norm_finset_sum_le` and
  `ContinuousMap.exists_finite_sum_smul_approximation_of_mem_uniformity`. These give
  finite-sum estimates or approximations, not this evaluation/parameter calculus.
- `msearch.py loogle`, query `ContinuousMap.sum, ContinuousMap.compL,
  Padic.norm_intCast_le_one`: unavailable as a usable match because Loogle rejected
  `ContinuousMap.sum` as unknown. Repeated with `ContinuousMap.compCLM`: found
  `compCLM` and `compCLM_apply`; the former is used to construct the operators.
- `msearch.py leansearch`, query “A finite weighted sum of continuous precompositions
  over a nonarchimedean field is bounded in supremum norm and preserves all linear
  subspaces and parameter families”: eight results, including
  `BoundedContinuousFunction.norm_compContinuous_le`,
  `IsNonarchimedean.apply_sum_le_sup_of_isNonarchimedean`, and bounded-function
  composition maps. These are building blocks, not the combined statement.
- `msearch.py grep`, query `sum.*comp|comp.*sum|norm_le` in
  `Topology/ContinuousMap`: 19 hits; read `Compact.lean` and `Algebra.lean` directly.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for `finite.evaluation`,
  `finiteEvaluation` and the node id: related rectangle-replacement/cochain modules
  and unrelated six-functor finite evaluations, but no declaration stating this node.
  Read `BoundedFiniteEvaluationRectangleReplacement.lean` and checked the nearby
  `RectangleCorrectedPointwiseFinitePrimitives.lean` interface.
- `grep -rn` of the node id in `lean/WeilConjectures`: no hits.
  Final exact-name `rg` over Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` found none of the three new declaration names.

Validation: `scompile.py Q141 lem-sfb-nonarchimedean-finite-evaluation-calculus` checks
both the isolated sandbox module and the final library module path against the live
published build. The initial version passed with no unexpected warnings; the final
empty-list clause was then made explicit for parameter operators and recompiled.
The theorem's proof docstring contains all six node proof steps and the two DAG
references used by the proof. Only the theorem proof is `sorry`; nothing is proved
or axiomatically defined in this delivery.

## Second reading by Q141

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
