## Worker report

The module `Sheaf.Algebra.Lie.ChevalleyStringCentralParity` states
`LieAlgebra.chevalley_string_central_parity`, with its sole proof `sorry`.
There are no new definitions, helper theorems, dependency repairs, or statement corrections.
The node is unchanged except for `lean`. The theorem docstring carries the complete
six-step natural-language proof, including the coordinate tables and the exceptional G₂
half-sum calculation. The result is a local Lie-algebra statement, not an assertion about
divided powers in an enveloping algebra.

The source was read in `literature/milne-algebraic-groups_iAG2017.pdf`, Theorem 23.71,
printed pp. 508–509, and Appendix C, section g, table (180) and the four diagrams,
printed pp. 621–622. The current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
and its direct-image proof were read for the originating context. This node is an
agent-stated supporting consequence, not the blueprint unit's statement and not a theorem
explicitly stated by Milne.

Hypothesis-by-hypothesis correspondence:

- A rational finite-dimensional Lie algebra is `(L : Type u) [LieRing L]
  [LieAlgebra ℚ L] [FiniteDimensional ℚ L]`.
- Semisimple means `[HasTrivialRadical ℚ L]`, exactly the predicate recorded by
  `def-wf-semisimple-lie-algebra`, rather than a replacement notion of semisimplicity.
- The specified splitting Cartan is `(H : LieSubalgebra ℚ L)
  [H.IsCartanSubalgebra] [LieModule.IsTriangularizable ℚ H L]`. Mathlib's Cartan docstring
  explicitly specifies this mixin for a splitting Cartan.
- The finite reduced crystallographic root system in H-dual, with its coroots, is
  `(I : Type v) [Finite I] (P : RootPairing I ℚ (Module.Dual ℚ H) H)` and
  `[P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]`. The independent index universe
  introduces no restriction on the algebra or the finite root set.
- `heval` identifies the pairing with evaluation, so `P.root_coroot_two` expresses
  γ(h_γ)=2 for these actual linear functionals. Roots and coroots are not unrelated data.
- `Δ : P.Base` chooses the simple roots. The given Chevalley basis is
  `B : Module.Basis (Δ.support ⊕ I) ℚ L`, with `Bh` identifying its first block as the
  simple coroots and `Be` identifying its second block with `e : I → L`.
  These are the same explicit basis hypotheses used by the landed consumer
  `Sheaf.Algebra.Lie.ChevalleyRankTwoStraightening`.
- `he` gives both membership in the ordinary simultaneous eigenspace
  `LieModule.weightSpace L (P.root i)` and nonzeroness. By its defining membership
  equivalence, this is exactly `[h,e_γ]=γ(h)e_γ` for every h in H.
- `hopp` expresses `[e_γ,e_{-γ}]=h_γ`: `P.reflectionPerm i i` is the index of -γ.
  Together with `he`, it places h_γ in the bracket of the two root spaces;
  evaluation normalization is supplied by `heval` and `P.root_coroot_two`.
- `hadd` quantifies every triple of root indices whose first two roots sum to the
  third. Its integer `ε` is explicitly 1 or -1, and its bracket coefficient is
  `((ε : ℚ) * (P.chainBotCoeff i j + 1))`. The Mathlib backward string coefficient
  is precisely the node's maximum p for independent roots. Root sums in a reduced
  system can only arise here from independent roots.
- `hzero` states zero bracket when the sum is outside `Set.range P.root` and is
  nonzero, retaining both exclusions.
- `(α β : I) (hne : α ≠ β) (hnopp : P.root α ≠ -P.root β)` supplies the given
  distinct nonopposite pair without prescribing an orientation or a length inequality.

Conclusion clause-by-clause correspondence:

- `∃ a b : I, ((a = α ∧ b = β) ∨ (a = β ∧ b = α)) ∧ ...` is exactly an ordering
  of the given pair. The same chosen a,b control every subsequent conjunct.
- `LinearIndependent ℚ ![P.root a, P.root b]` is rational independence.
- `let p := P.chainBotCoeff a b` and `let q := P.chainTopCoeff a b` are the maximum
  backward and forward root-string indices. Their definitions were read in
  `Mathlib.LinearAlgebra.RootSystem.Chain`; independence avoids their junk-value branch.
- `let Y : ℕ → L := fun k ↦ ((k.factorial : ℚ)⁻¹) •
  ((ad ℚ L (e a)) ^ k) (e b)` is exactly the divided iterated adjoint in L.
- The next three conjuncts are `p + q ≤ 3`, `Y 0 = e b`, and
  `∀ k : ℕ, q < k → Y k = 0`.
- For every `k ≤ q`, existential `r : I` has
  `P.root r = P.root b + k • P.root a`, and existential `c : ℤ` satisfies
  `Y k = (c : ℚ) • e r` and `c.natAbs = (p + k).choose k`.
  The root index is uniquely determined since `P.root` is an embedding. This avoids
  any arbitrary extension of e to nonroots, and asserts the required root exists.
- `∀ i j k : ℕ, i ≤ q → j ≤ q → k ≤ q → ⁅⁅Y i, Y j⁆, Y k⁆ = 0` includes diagonal,
  reversed, and zero indices as well as increasing pairs; natural indices supply the
  three lower bounds 0.
- `let C` is the rational half of the sum over `i ∈ Finset.range (q+1)` and
  `j ∈ (Finset.range (q+1)).filter (fun j ↦ i < j ∧ i+j=d)`.
  Each pair satisfying 0≤i<j≤q and i+j=d occurs exactly once. Empty Finset sums are zero.
- `∀ d : ℕ, 1 ≤ d → d ≤ 2*q → ...` retains precisely the stated degree range.
  For a nonroot weight, the first implication gives `C d = 0`. For a root weight,
  the second implication gives `∃ z : ℤ, C d = (z : ℚ) • e r` for its root index r.
  The universal r is equivalent to the node's conditional notation e_(2b+da), since
  a weight in `Set.range P.root` has exactly one index. There is no assertion about C
  outside this degree range.

Dependency declarations used:

- `def-wf-lie-algebra`: Mathlib's `LieRing`, `LieAlgebra` from
  `Mathlib.Algebra.Lie.Basic`, and `LieAlgebra.ad` from
  `Mathlib.Algebra.Lie.OfAssociative` (available through the public imports).
  Their full signatures and docstrings were read, including `ad_apply`.
- `def-wf-semisimple-lie-algebra`: `LieAlgebra.HasTrivialRadical` from
  `Mathlib.Algebra.Lie.Semisimple.Defs`, publicly imported through
  `Mathlib.Algebra.Lie.Semisimple.Basic`. Its characterization
  `hasTrivialRadical_iff_no_solvable_ideals` was read there.
- Other existing notions are `LieSubalgebra.IsCartanSubalgebra` from
  `Mathlib.Algebra.Lie.CartanSubalgebra`, `LieModule.IsTriangularizable` and
  `LieModule.weightSpace` from `Mathlib.Algebra.Lie.Weights.Basic`,
  `RootPairing` / `IsRootSystem` from `Mathlib.LinearAlgebra.RootSystem.Defs`,
  its crystallographic and reduced mixins, `RootPairing.Base` from
  `Mathlib.LinearAlgebra.RootSystem.Base`, and the two chain coefficients from
  `Mathlib.LinearAlgebra.RootSystem.Chain`. All are reused, not privately copied.
- Proof dependency `lem-sfb-rank-two-root-coordinate-classification` has no recorded
  Lean declaration/module on the read base, so it has no module to import. It remains
  a DAG proof dependency and is explicitly named in the theorem's proof docstring.
  No proof-only dependency is used as a statement hypothesis.

Edge cases checked before writing:

- Empty root set and the zero algebra remain permitted. There are then no choices of
  α,β satisfying the hypotheses; no nonempty-root or positive-rank assumption is added.
- For rank one, two distinct roots are opposite, so the nonopposition hypothesis
  excludes exactly that case, as in the node.
- For q=0, Y₀=e_b and the only triple is (0,0,0), killed by alternation. The range
  1≤d≤2q is empty. No artificial positive-q assumption occurs.
- At k=0 the coefficient has absolute value choose(p,0)=1, and the factorial is one.
  At k=q the root is retained; vanishing is only asserted for strictly greater k.
- The degree endpoints d=1 and d=2q are included. At d=2q no increasing pair with
  both indices ≤q contributes, so C_d=0 and z=0 works if its weight is a root.
- G₂ exceptional orientations: (p,q)=(0,3) has |c|=(1,1,1,1) and grouped coefficient
  (±1±3)/2, always integral; (1,2) has |c|=(1,2,3), sole coefficient ±6/2=±3.
  Arbitrary allowed Chevalley signs are retained; no extra sign-coherence hypothesis.
- Rational scalar multiplication expresses both divisions. In characteristic zero,
  no factorial or the scalar two vanishes. No field-characteristic cases are omitted,
  since the node already fixes ℚ.

Searches for an existing declaration:

- `msearch.py ... leanfinder "Chevalley root string divided iterated adjoints central
  brackets integral half sums"`: 8 hits, including `IsKilling.chainLength_nsmul`,
  `chainLength_smul`, and `RootPairing.GeckConstruction.e_lie_v_ne` / `f_lie_v_ne`;
  none states centrality and integral grouped half-sums for arbitrary Chevalley data.
- `msearch.py ... leansearch "Chevalley root string divided adjoints central brackets
  integral half sums"`: 8 hits, including `GeckConstruction.lie_h_e`,
  `CartanMatrix.Relations.adF`, and `LieAlgebra.isNilpotent_ad_of_mem_rootSpace`;
  no exact match.
- `msearch.py ... loogle "RootPairing.chainBotCoeff, RootPairing.chainTopCoeff"`:
  12 hits. `chainBotCoeff_add_chainTopCoeff_le_three` gives the string-length bound
  only; the chain definitions are reused for p,q.
- `msearch.py ... grep "Chevalley|chevalley|central|parity" LinearAlgebra/RootSystem`:
  no hits. Follow-up grep `"chainBotCoeff|chainTopCoeff|GeckConstruction"` returned
  25 hits in the chain, base and Geck model files, with no exact match.
- Local `rg -n` for `Chevalley|chevalley|RootPairing|IsCartanSubalgebra|IsSplitting`
  in project Lie-algebra directories, and for `root string|Chevalley|central.*parity`
  in `lean/WeilConjectures` and `lean/Sheaf/Algebra/Lie`: the nearby project modules
  are root normalization, Kostant PBW, root decomposition, and rank-two straightening.
  Their conclusions differ; straightening is a consumer of this item, not a substitute.
- Exact item-id search in `lean/WeilConjectures` found no declaration. The DAG concept
  search `rg -l 'Chevalley basis|ChevalleyBasis|chevalleyBasis' dag/nodes` found the
  supporting Chevalley nodes and this item, but no existing standalone definition
  needing duplication. The hypothesis list is expressed entirely with Mathlib notions.
- Raw msearch results are logged in the sandbox `searches.jsonl`.

No STATEMENT-DISPUTED issue was found. No node fields beyond `lean` were changed.

Validation: `scompile.py NB lem-sfb-chevalley-string-central-parity` compiled the sole
module against the server's published build in both sandbox and library modes, with
no errors or warnings (3.1 seconds and 2.7 seconds respectively). Both auto-implicit
options are disabled in the delivered module. Every Lean line is at most 100 characters.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
