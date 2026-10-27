## Worker report

The module `Sheaf.Algebra.Lie.ChevalleyRootNormalization` states
`LieAlgebra.exists_chevalley_basis_of_pinning`, with its entire proof `sorry`.
It introduces no definitions, auxiliary theorems, new nodes, or dependency modules.
The item's statement and its accepted stage-1 split are unchanged.

The inherited BLOCKED message concerned another stage-1 split. The current node
has Q74's reviewed stage-1 split and no Lean attachment; the stage-2 handoff in
`coord/brief-stage2.md` §0 therefore applies. This delivery supplies the absent
Lean statement without reopening Q74's split.

I read Milne, Algebraic Groups (2017), printed pp. 508–509 (PDF pp. 520–521),
including the prescribed pinning, the opposite-root normalization, Theorem 23.71,
and the integral bracket table. The rational form and the allowance for the zero
semisimple algebra are the node's existing formulation. No statement correction
or STATEMENT-DISPUTED flag is needed.

Hypotheses, in the order of the node:

| Node | Lean rendering |
| --- | --- |
| Rational Lie algebra | `L : Type u`, `[LieRing L]`, `[LieAlgebra ℚ L]`; the inherited Mathlib bracket is used everywhere. |
| Finite-dimensional | `[FiniteDimensional ℚ L]`. |
| Semisimple | `[HasTrivialRadical ℚ L]`, exactly the predicate recorded by `def-wf-semisimple-lie-algebra`, rather than a new semisimplicity definition. |
| Maximal abelian subalgebra | `H : LieSubalgebra ℚ L`, `[IsLieAbelian H]`, and `hmax`: every abelian Lie subalgebra containing `H` equals `H`. This means maximal among abelian subalgebras. |
| Reduced root system in the dual of H, with its coroots in H | `I : Type v`, `[Finite I]`, `P : RootPairing I ℚ (Dual ℚ H) H`, `[P.IsRootSystem]`, `[P.IsCrystallographic]`, `[P.IsReduced]`. The root and coroot families are injective by the existing Mathlib structure. |
| The root-coroot pairing is evaluation | `heval : ∀ f h, P.toLinearMap f h = f h`; this prevents an unrelated perfect pairing on the same spaces. `P.root_coroot_two` now says precisely `α(h_α) = 2`. The pairing, reflections, spanning, and integrality are the root-system data meant by the node, not unrelated input. |
| The diagonal root decomposition, with zero-weight summand H | `hdecomp : DirectSum.IsInternal (Sum.elim (fun _ : Unit ↦ H.toSubmodule) (fun i ↦ (LieModule.weightSpace L (P.root i)).toSubmodule))`. The single left summand is H; the right summands are the root spaces. Bijectivity of the canonical direct-sum inclusion is exactly the stated internal direct sum. It also expresses simultaneous diagonal action. |
| Exact root-space equation for all h | `LieModule.weightSpace L (P.root i)` has membership `∀ h : H, ⁅h, z⁆ = P.root i h • z` by `LieModule.mem_weightSpace`. These are ordinary eigenspaces; I do not substitute generalized root spaces. |
| Each root space is one-dimensional | `hdim : ∀ i, Module.finrank ℚ (LieModule.weightSpace L (P.root i)) = 1`. All these spaces are finite-dimensional subspaces of L. |
| Coroot belongs to the bracket of the opposite root spaces | `hcoroot` places `(P.coroot i : L)` in the rational span of all brackets `⁅a,b⁆` with `a` of weight `P.root i` and `b` of weight `-P.root i`. This is the linear span meant by `[g_α,g_-α]` in `def-wf-lie-algebra`. Combined with `heval` and `root_coroot_two`, this is the prescribed normalized coroot, not an arbitrary element of H. |
| Simple-root base Δ is a basis of the dual | `Δ : Set I`, `b : Module.Basis Δ ℚ (Dual ℚ H)`, and `hb : ∀ i : Δ, b i = P.root i`. Identifying the roots with their injectively indexed image turns a subset of roots into a subset of I. The basis data has precisely the fixed simple-root values. |
| All root coordinates are sign-coherent integers | `hsign` puts each root or its negative in `AddSubmonoid.closure (P.root '' Δ)`, the finite sums with nonnegative integer coefficients. Since b is a basis, these are exactly the stated coordinates. No coroot-base condition is added to the input. |
| Prescribed arbitrary nonzero rational simple-root vectors | `x : Δ → L`, `hx` puts each vector in its ordinary root space, and `hxne` asserts it is nonzero. All vectors are in the given rational vector space L. No positivity or normalization of x is assumed. |

Conclusions, clause by clause:

| Node | Lean rendering |
| --- | --- |
| Nonzero rational root vectors for every root | `∃ e : I → L, (∀ i, e i ∈ LieModule.weightSpace L (P.root i) ∧ e i ≠ 0) ∧ ...`. |
| Preserve the pinning | `∀ i : Δ, e i = x i`. |
| Opposite-root normalization | `∀ i, ⁅e i, e (P.reflectionPerm i i)⁆ = (P.coroot i : L)`. The reflection at a root sends that same root to its negative by `reflectionPerm_root` and `root_coroot_two`. Injectivity identifies this with exactly the index of `-α`. |
| Root-sum brackets with sign ±1 | `∀ i j k, P.root i + P.root j = P.root k → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ⁅e i,e j⁆ = ((ε : ℚ) * (P.chainBotCoeff i j + 1)) • e k`. Root injectivity makes k unique. |
| p is the maximum downward root-string length | `P.chainBotCoeff i j`. I read its definition and `root_sub_nsmul_mem_range_iff_le_chainBotCoeff`: `β - n α` is a root iff `n ≤ chainBotCoeff`. When α+β is a root in a reduced system, α and β are linearly independent; the coefficient's junk value for dependent pairs is never used by the bracket clause. The order of arguments is α, β, as in the node. |
| Brackets zero outside roots and zero | `∀ i j, P.root i + P.root j ∉ Set.range P.root → P.root i + P.root j ≠ 0 → ⁅e i,e j⁆ = 0`. Opposite-root brackets are expressly excluded from this vanishing claim. |
| The simple coroots and root vectors form a rational basis | `∃ B : Module.Basis (Δ ⊕ I) ℚ L`, with `B (Sum.inl i) = (P.coroot i : L)` and `B (Sum.inr i) = e i`. This includes both linear independence and spanning. |
| All structure constants are integers | `∀ i j k : Δ ⊕ I, ∃ n : ℤ, B.repr ⁅B i, B j⁆ k = (n : ℚ)`. This includes every Cartan-Cartan, Cartan-root, opposite-root and other root-root product, not just root sums. |
| Empty base allowed | There is no `Nonempty` or `Nontrivial` assumption on Δ, I, H, or L. With Δ empty the basis of the dual forces H to be zero, the nonzero-root axiom forces I empty, and the internal decomposition forces L zero. The empty basis is admitted by `Module.Basis (Δ ⊕ I) ℚ L`. |

Dependency declarations read and used:

- `def-wf-lie-algebra`: `LieRing`, `LieAlgebra`, `LieSubalgebra`, from
  `Mathlib.Algebra.Lie.Basic` and `Mathlib.Algebra.Lie.Subalgebra`, as recorded
  in its `mathlib_match`. Its own root-space bracket notation is rendered by
  `Submodule.span` of the actual brackets, not by a Lie ideal or a Lie closure.
- `def-wf-semisimple-lie-algebra`: `LieAlgebra.HasTrivialRadical` from
  `Mathlib.Algebra.Lie.Semisimple.Defs`, and the equivalence
  `LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals` from
  `Mathlib.Algebra.Lie.Semisimple.Basic`. I also read the recorded closed upstream
  signature `LieAlgebra.hasTrivialRadical_iff_forall_isSolvable_eq_bot` in
  `WeilConjectures.Mathlib.Algebra.Lie.Radical`; it is exactly that equivalence.
  The new theorem uses the recorded predicate directly, so no dependency repair
  or private copy is needed.
- Other existing notions used: `LieModule.weightSpace` and its membership lemma
  in `Mathlib.Algebra.Lie.Weights.Basic`; `DirectSum.IsInternal` in
  `Mathlib.Algebra.DirectSum.Basic`, exposed by the imported
  `Mathlib.Algebra.DirectSum.Module`; `RootPairing` and `IsRootSystem` in
  `Mathlib.LinearAlgebra.RootSystem.Defs`, `IsReduced` in its `Reduced` module,
  `IsCrystallographic` in `IsValuedIn`, and `chainBotCoeff` in `Chain`.
- Proof-dependency interfaces read: `RootPairing.Base.induction_add`,
  `Base.toWeightBasis`, `Base.toCoweightBasis`, `Base.span_int_root_support`,
  `Base.span_int_coroot_support`, and `Base.mk'`. These are the Mathlib matches
  recorded for `lem-sfb-root-base-additive-induction` and
  `lem-sfb-root-base-rational-integral-spans`. `BaseExists` is a plain proof-only
  import and publicly imports `Base`; both proof nodes' matched declarations
  are therefore available for stage 3. `lem-sfb-rational-opposition-involution`
  and `lem-sfb-opposition-root-bracket-norm` have no Lean declarations yet, so
  there are no modules of theirs to import. Their exact IDs and arguments are
  retained in the proof docstring. No proof dependency is removed or duplicated.

Edge-case checks: the zero algebra and empty simple base above; rank one, where
root sums never satisfy the root-sum premise, but opposite roots still have the
normalization clause; α = β and α = -β, which cannot have α+β a root in a reduced
system, so the chain coefficient's dependent-pair value is immaterial; roots in
different semisimple components, whose nonzero sum is not a root and has zero
bracket; arbitrary nonzero rational rescaling of the prescribed x; all root
lengths, including long strings, using Mathlib's downward chain coefficient.
`L : Type u` and `I : Type v` have separate explicitly bound universes; there is
no smallness or nonemptiness restriction. All identifiers are explicitly bound.
The classical decidability used by the internal-direct-sum API is confined by
`open Classical in` to the declaration; it is not an added mathematical
hypothesis or a new local instance/definition.

Searches for an existing statement (all run through the prescribed msearch.py):

- LeanFinder: "A split semisimple rational Lie algebra has a Chevalley basis
  extending prescribed simple root vectors with integral structure constants".
  Eight hits, headed by `RootPairing.GeckConstruction.lieAlgebra`,
  `cartanSubalgebra`, and its matrix-generator membership results. These describe
  a constructed matrix Lie algebra, not normalization in the given arbitrary L.
- Loogle: "LieAlgebra.Basis, LieAlgebra.IsSemisimple". Service succeeded,
  no hits for this combined query.
- Mathlib grep: "Chevalley|rootString|IsSemisimple", subdirectory `Algebra/Lie`.
  Twenty-five hits, including `Basis/Basic.lean`. I read its module docstring,
  which explicitly lists defining Chevalley bases as TODO. Its `LieAlgebra.Basis`
  packages only the simple generators and is not the theorem here.
- LeanSearch: "Chevalley basis extending arbitrary simple root vectors of a split
  semisimple Lie algebra over the rationals". Eight hits, including
  `RootPairing.Base.toWeightBasis`, `toCoweightBasis`, and
  `LieAlgebra.IsKilling.rootSystem`. They provide constituent root-system data,
  not the simultaneous normalization or the integral full Lie bracket table.
- Direct project rg of `Chevalley basis|chevalley_basis|chevalleyBasis|root_normalization|rootNormalization`
  in `lean/WeilConjectures` and `lean/Sheaf`: only unrelated scheme-normalization
  declarations. Earlier broader Chevalley/root-system search likewise found no
  Lie-algebra normalization declaration. Direct rg of the item ID in
  `lean/WeilConjectures`: no hits. The new full declaration name was also checked
  against Mathlib, upstream source and project source: no existing declaration.
- Source reading of `RootPairing.Base` confirmed it contains coroot-base conditions
  in addition to the input root-side conditions. Accordingly I used `Module.Basis`
  with `hb` and `hsign`, instead of silently adding the coroot assumptions.

The exact msearch outputs are retained in the sandbox's `searches.jsonl`.

## Second reading by Q72

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
