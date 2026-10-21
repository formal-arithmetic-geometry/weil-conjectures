## Worker report

The module `Sheaf.RingTheory.TateResidue.FinitePotentTraceCalculus` states
`Module.End.finitePotent_trace_calculus`, with one `sorry`, for the complete node.
No definitions, dependency modules, new nodes, or statement corrections are needed.
The statement is unchanged. There is no STATEMENT-DISPUTED flag.

The source was read directly using `pdftotext -f 1 -l 3` on
`literature/tate-residues-of-differentials-on-curves_ASENS-1968.pdf`: §1,
printed pp. 149–150, (T1)–(T5), including the characterization paragraph and
(T4)'s proof. The finite-sum clause is precisely its pairwise-product specialization.
The docstring gives all seven node proof steps and their supporting DAG nodes.

Hypothesis and conclusion correspondence (the conjunctions below are in file order):

- Field and arbitrary vector space: `(k : Type u) [Field k] (V : Type v)
  [AddCommGroup V] [Module k V]`. No finite-dimensional, characteristic, or
  nonzero-space assumption is imposed on `V`.
- Finite potency uses the existing `Module.End.IsFinitePotent`:
  `∃ n : ℕ, (LinearMap.range (T ^ n)).FG`. Over a field `U.FG` is equivalent to
  `FiniteDimensional k U` by `Submodule.fg_iff_finiteDimensional`. The upstream
  predicate allows `n = 0`, which does not change the notion: that case makes
  the whole space finite dimensional, hence the image of `T ^ 1` is finite
  dimensional. A positive witness is therefore always available. Conversely
  the node's positive witness is directly an upstream witness.
- Canonical scalar: the real, previously existing construction
  `Module.End.tateTrace T` takes the trace on the image of the least finite-rank
  power, using `Nat.find`, and returns zero for a non-finite-potent operator.
  Its data contains no `sorry` and no unspecified choice of a scalar.
- First conjunct: for every finite-potent `T`, every `U : Submodule k V`,
  `FiniteDimensional k U`, stability `hU : ∀ x ∈ U, T x ∈ U`, and every
  `N : ℕ` with `1 ≤ N` and `LinearMap.range (T ^ N) ≤ U`, the equality
  `T.tateTrace = LinearMap.trace k U (T.restrict hU)` is the asserted
  characterization, independently of both `U` and `N`.
- Second conjunct: under the same finite-potency hypothesis, `∃! t : k, ...`
  repeats exactly that characterization. This records existence and uniqueness;
  combined with the first conjunct the unique scalar is the existing `tateTrace`.
- Third conjunct: `∀ [FiniteDimensional k V] (T : Module.End k V),
  T.tateTrace = LinearMap.trace k V T` gives ordinary trace on finite-dimensional
  spaces. That typeclass assumption occurs only in this conjunct.
- Fourth conjunct: `IsNilpotent T → T.IsFinitePotent ∧ T.tateTrace = 0`.
  Nilpotence is the existence of a zero power. As above exponent zero adds
  only the zero-space case, where a positive zero-power witness exists too.
- Fifth conjunct: `L : Submodule k V`, `hL : ∀ x ∈ L, T x ∈ L` encode precisely
  a `T`-stable subspace. `T.restrict hL` is the actual restriction on `L`;
  `L.mapQ L T hL` is the canonical induced endomorphism of `V ⧸ L`.
  Both are asserted `IsFinitePotent`, followed by
  `T.tateTrace = tateTrace (T.restrict hL) + tateTrace (L.mapQ L T hL)`.
  There is no finite-dimensional assumption on `L` or its quotient.
- Sixth conjunct: for each `c : k`, `(c • T).IsFinitePotent` and
  `(c • T).tateTrace = c * T.tateTrace`, under the original finite-potency
  hypothesis on `T`. The finite-potency assertion makes the displayed trace
  a trace of an operator in the stated domain.
- Seventh conjunct: arbitrary `(W : Type w) [AddCommGroup W] [Module k W]`,
  `a : V →ₗ[k] W`, `b : W →ₗ[k] V`. Its sole operator hypothesis is
  `IsFinitePotent (b ∘ₗ a)` and its conclusions are
  `IsFinitePotent (a ∘ₗ b)` and
  `tateTrace (b ∘ₗ a) = tateTrace (a ∘ₗ b)`. The independent universe `w`
  permits unequal dimensions and universes for the two vector spaces.
- Eighth conjunct: `r : ℕ`, `T : Fin r → Module.End k V` give the node's
  finite list. `∀ i j : Fin r, FiniteDimensional k (LinearMap.range (T i * T j))`
  is exactly its pairwise finite-image hypothesis, including diagonal products
  and both orders. It concludes `(∀ i, (T i).IsFinitePotent)`, finite potency
  of `∑ i, T i`, and the stated equality of its trace with the sum of traces.

Dependency declarations read and used:

- `def-weil-finite-dimensional-subspace` is a Mathlib leaf with
  `mathlib_match = ["FiniteDimensional"]`, not a missing Lean attachment.
  Its declaration is `FiniteDimensional` in
  `Mathlib.LinearAlgebra.FiniteDimensional.Defs`, an abbreviation for
  `Module.Finite`. `Submodule.fg_iff_finiteDimensional` in the same module
  identifies it with the upstream finite-potency predicate's use of `FG`.
- `def-weil-endomorphism-trace` is a Mathlib leaf naming `LinearMap.trace`
  in `Mathlib.LinearAlgebra.Trace`. Its full definition and basis formula
  were read: it is the basis-independent diagonal sum on a finite free module.
  Over a field all finite-dimensional spaces are finite free. Both statement
  dependency modules are imported explicitly and publicly.
- The existing construction and trace identities were read in full in
  `WeilConjectures.RingTheory.TateResidue.FinitePotent` (public import).
  These include `Module.End.IsFinitePotent`, `Module.End.tateTrace`,
  `Module.End.mapsTo_range_pow`, `Module.End.tateTrace_eq_trace_restrict`,
  `Module.End.tateTrace_eq_trace`, `Module.End.tateTrace_eq_zero_of_pow_eq_zero`,
  `Module.End.tateTrace_smul`, `Module.End.tateTrace_eq_add_of_exact`,
  `Module.End.tateTrace_comp_comm`, and `Module.End.tateTrace_sum`.
- Proof dependencies: `lem-pc-finite-dimensional-trace-exact` has no attachment,
  but its exact, already proved signature is `LinearMap.trace_eq_add_of_exact`
  in that same upstream module (including injectivity, surjectivity,
  `Function.Exact`, and both intertwining equations). No replacement is needed
  to state this item. The other two proof dependencies' Mathlib matches are
  `LinearMap.isNilpotent_trace_of_isNilpotent` and
  `LinearMap.trace_comp_comm'` in `Mathlib.LinearAlgebra.Trace` (already a public
  statement import). Their full signatures and surrounding hypotheses were read.

Why a new statement module rather than an `existing: true` record: the upstream
trace identities do not conclude finite potency of restriction/quotient, the
opposite cyclic composite, or the finite sum. Their proofs construct the needed
finite-rank image witnesses internally. This theorem exposes these conclusions
and the canonical-scalar characterization, in precisely the node's combined
statement. It does not introduce another finite-potency predicate or trace.

Edge cases checked mathematically before writing: zero vector space, zero and
nilpotent operators (including infinite-dimensional nilpotents), finite-dimensional
`V`, stable `L = 0` and `L = V`, scalar `c = 0`, distinct dimensions and universes
for `V,W`, and `r = 0`. In the last case `Fin 0` is empty, the pairwise assumption
and individual finite-potency conclusion are vacuous, the sum is zero and has
zero trace. No nonempty instance is required. A nonzero identity on an infinite-
dimensional space is not finite-potent, so it does not accidentally satisfy a
premise. In positive characteristic the ordinary trace is still the scalar
matrix trace, not a natural-number dimension.

Searches for an existing complete statement (all searches read-only):

- `msearch.py ... leanfinder` query: "Trace of finite potent endomorphisms
  arbitrary dimensional vector spaces restriction quotient scalar cyclic finite
  rank pairwise products". Eight ordinary-trace hits: `LinearMap.IsProj.trace`,
  `LinearMap.trace_comp_eq_zero_of_commute_of_trace_restrict_eq_zero`,
  `LinearMap.trace_eq_sum_trace_restrict_of_eq_biSup`,
  `LinearMap.trace_restrict_eq_of_forall_mem`, `LinearMap.trace_one`,
  `LinearMap.trace_eq_zero_of_mapsTo_ne`,
  `LinearMap.trace_eq_sum_trace_restrict'`, and `LinearMap.trace_id`.
  None states finite-potent trace calculus.
- `msearch.py ... loogle '"tateTrace"'`: zero hits.
- `msearch.py ... grep 'finite.?potent|tateTrace|IsFinitePotent'`: zero Mathlib hits.
- `msearch.py ... leansearch` query: "Tate trace of a finite potent endomorphism
  with finite dimensional power image". Eight hits on ordinary trace:
  `Matrix.trace_toLin_eq`, `LinearMap.trace_transpose'`, `Matrix.trace_toLin'_eq`,
  `LinearMap.trace_eq_contract_of_basis`, `LinearMap.traceAux_def`,
  `LinearMap.trace_baseChange`, `LinearMap.trace_conj'`, `Algebra.trace`.
  None states the requested calculus.
- `rg -n 'finite.?[Pp]otent|tateTrace|TateTrace'` on both
  `lean/WeilConjectures` and `lean/Sheaf` found the upstream TateResidue modules
  and their consumers. The full `FinitePotent.lean` was then read, as above.
- `rg -n 'lem-pc-finite-potent-trace-calculus' lean/WeilConjectures`: no hits.
- Name checks for `finitePotent_trace_calculus` in both library trees and
  `dag/lean_names_upstream.json`: no existing declaration.

All delivered universes and variables are explicit, with `set_option autoImplicit false`.
The only postponed proof is this node's one theorem, whose docstring contains
its seven-step natural-language proof. Compilation uses only `scompile.py`.

## Second reading by NV

The dispatcher brief reserves the independent review for the maintainer and
forbids starting other agents. This section records the worker's final self-check,
not an independent reading. The clause-by-clause correspondence above was checked
against the node and final Lean file. The only compiler repair was replacing dot
notation on restrictions and composites (whose elaborated head is `LinearMap`)
with the explicit `IsFinitePotent` and `tateTrace` functions from `Module.End`.
It changes no mathematical object or hypothesis. No definition or node statement
was changed, and every finite-potency conclusion remains present.
