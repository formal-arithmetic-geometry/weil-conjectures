## Worker report

Item: lem-sfb-nonopposite-root-bracket-nonvanishing. Group Q119, stage 2, 2026-10-24.

The module `Sheaf.Algebra.Lie.NonoppositeRootBracketNonvanishing` states
`LieAlgebra.lie_ne_zero_of_nonopposite_root_vectors`. Its only proof is `sorry`.
No definition is introduced. The item node changes only in `lean`; its accepted
stage-1 split, natural-language statement, and all dependency lists are preserved.

The inherited BLOCKED report concerned treating Q49's accepted stage-1 split as
an unchanged stage-1 delivery. The current queue lists this item in stage 2,
the node has no Lean record, and brief-stage2 section 0 explicitly authorizes
the stage handoff. There is no repair note for this item and no Q119 return
reopening or restricting this statement. This is its first Lean statement.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A characteristic-zero field is `(K : Type u) [Field K] [CharZero K]`.
- A finite-dimensional K-Lie algebra is `(L : Type v) [LieRing L]
  [LieAlgebra K L] [FiniteDimensional K L]`. Both universes are explicit and independent.
- Nondegeneracy of the Killing form is `[IsKilling K L]`. Mathlib defines this
  as `LieIdeal.killingCompl K L ⊤ = ⊥`, exactly vanishing of the radical;
  `LieAlgebra.IsKilling.killingForm_nondegenerate` gives the bilinear formulation.
  `LieAlgebra.killingForm` is the trace form of the adjoint representation, so
  it is exactly the node's `Tr(ad(x)ad(y))`, with no other invariant form chosen.
- The subalgebra is `(H : LieSubalgebra K L)`.
- Nilpotence and self-normalization are exactly `[H.IsCartanSubalgebra]`, whose
  two fields are `LieRing.IsNilpotent H` and `H.normalizer = H`. The normalizer
  convention using brackets in the reversed order is equivalent by skew-symmetry.
- Diagonalizability over K for every h is `hdiag : ∀ h : H,
  (⨆ μ : K, (ad K L (h : L)).eigenspace μ) = ⊤`. This uses ordinary
  eigenspaces over K and says precisely that they span L. Distinct eigenspaces
  are independent, so in finite dimensions this is diagonalizability. It imposes
  no algebraic-closure assumption and no chosen simultaneous eigenbasis.
- The two linear functionals are `(α β : Module.Dual K H)`; their nonzero
  conditions are `hα : α ≠ 0` and `hβ : β ≠ 0`.
- The nonopposite condition is `hαβ : α + β ≠ 0` in that same linear dual.
- For any functional γ, the ordinary root space in the node is Mathlib's
  `LieModule.weightSpace L (γ : H → K)`. Its defining membership theorem is
  `LieModule.mem_weightSpace`: for every h, `[h,x] = γ(h) • x`.
  The action is the adjoint action restricted along the inclusion of H.
- Nonzero root spaces for α, β, α+β are the three separate hypotheses
  `hrootα`, `hrootβ`, `hrootαβ`, each asserting that the corresponding
  ordinary weight submodule differs from bottom. All three remain explicit,
  including the first two which also follow from the prescribed x and y.
- Arbitrary vectors and their membership are `(x y : L)`, `hx`, `hy`.
  Their required nonvanishing is `hxne : x ≠ 0`, `hyne : y ≠ 0`.
- The full conclusion, for these arbitrary nonzero root vectors, is `⁅x, y⁆ ≠ 0`.

Dependency declarations read and used:

- `def-wf-lie-algebra` is a Mathlib leaf. Its `mathlib_match` supplies `LieRing`
  and `LieAlgebra` in `Mathlib.Algebra.Lie.Basic`, `LieSubalgebra` in
  `Mathlib.Algebra.Lie.Subalgebra`, and `LieAlgebra.ad` in
  `Mathlib.Algebra.Lie.OfAssociative`. Their signatures and docstrings were read.
  These are the project's recorded definitions, not local replacements.
- The three proof prerequisites are also Mathlib leaves, not missing interfaces.
  `lem-sfb-killing-cartan-rank-one-spaces` records
  `LieAlgebra.IsKilling.traceForm_cartan_nondegenerate`,
  `lie_eq_smul_of_mem_rootSpace`, `root_apply_cartanEquivDual_symm_ne_zero`,
  `root_apply_coroot`, `exists_isSl2Triple_of_weight_isNonZero`,
  `IsSl2Triple.h_eq_coroot`, and `finrank_rootSpace_eq_one` in
  `Mathlib.Algebra.Lie.Weights.Killing`. Their full statements were inspected.
  This module is publicly imported because the statement itself uses `IsKilling`.
- `lem-sfb-nilpotent-module-generalized-weight-decomposition` records
  `LieModule.iSupIndep_genWeightSpace`, `finite_genWeightSpace_ne_bot`, and
  `iSup_genWeightSpace_eq_top` in `Mathlib.Algebra.Lie.Weights.Basic`, read in source
  and imported publicly through Killing. Ordinary spaces in the new statement
  remain `weightSpace`, not these generalized spaces.
- `lem-sfb-sl2-primitive-lowering-string` records
  `IsSl2Triple.HasPrimitiveVectorWith.exists_nat`,
  `pow_toEnd_f_ne_zero_of_eq_nat`, and `lie_e_pow_succ_toEnd_f` in
  `Mathlib.Algebra.Lie.Sl2`. Their full signatures were read. The module has an
  explicit non-public proof import. The theorem docstring gives all five DAG
  proof steps, including rescaling to the prescribed x, finite-support raising
  termination, the two primitive-vector applications, and the final contradiction.

Sources and edge cases:

Read Milne Section 23h, printed p. 503, including its definition of splitting
Cartan subalgebras and ordinary root spaces, and Theorem 23.71, pp. 508–509.
The node explicitly identifies its arbitrary-field local formulation as
agent-formulated; the proof docstring retains that attribution. Also read the
current latest blueprint's direct-image proof, paragraph (3), the ancestor
context recorded in the node. No blueprint unit statement is being changed.

The zero algebra and zero Cartan are allowed by the binders; their dual has no
nonzero α or β, so the hypotheses correctly fail there. Empty root systems and
rank-one systems with no nonopposite root sum likewise give no admissible pair.
The cases α=0, β=0, and α+β=0 are excluded exactly as in the node. If α=β,
the condition that 2α be a root is impossible in this characteristic-zero
Killing setting; no extra distinctness hypothesis was added. Zero x and zero y
are excluded exactly as stated. Arbitrary characteristic-zero fields, including
non-algebraically-closed ones, remain covered. Degenerate Killing forms and
positive characteristic are excluded only by the node's own hypotheses.
No statement dispute or node fault was found.

Searches for an existing statement (all used msearch.py with this group/item):

- LeanFinder: "The bracket of nonzero root vectors is nonzero if the sum of
  their nonopposite roots is a root". Eight hits, including
  `reflectRoot_isNonZero`, `rootSpace_zsmul_add_ne_bot_iff_mem`, opposite-root
  Killing formulas, and `RootPairing.GeckConstruction.f_lie_v_ne`.
  None states this arbitrary-L nonvanishing assertion.
- LeanSearch: "The bracket of nonzero vectors of two root spaces in a split
  semisimple Lie algebra is nonzero if their sum is a nonzero root".
  Eight hits: weight inclusion, root-space products, and opposite-root formulas;
  no exact match.
- Loogle: "LieAlgebra.rootSpaceProduct, LieModule.weightSpace". Zero hits for
  the combined query. The definitions were then inspected directly in source.
- Mathlib grep: `lie.*(ne_zero|nonzero)|rootSpaceProduct` in
  `Algebra/Lie/Weights`. Eight hits, giving product maps and their evaluation
  theorem, not nonvanishing. Read `rootSpaceProduct` and `rootSpaceProduct_tmul`.
- Project rg in both `lean/WeilConjectures` and `lean/Sheaf` for
  `nonopposite|root.*bracket|bracket.*root`, followed by
  `lie_ne_zero_of_nonopposite_weights|nonopposite_root|lie_ne_zero_of.*weight|lie_ne_zero_of.*root`.
  Existing Chevalley-basis and rank-two-straightening statements concern a
  different setup and do not state this arbitrary-field local theorem.
  Exact-id grep in `lean/WeilConjectures` found no declaration.
- Read the full current node, all statement dependencies, the recorded
  Mathlib matches of all proof dependencies, and the accepted Q49 stage-1 report.
  There is no usable existing declaration for the item's conclusion.

Validation: scompile.py compiled both the sandbox check and the actual module
successfully on the server (4.6 s and 7.3 s), with no reported errors or warnings.
Every variable and universe is explicitly bound; there are no auxiliary
declarations, local notation, local instances, hidden data choices, or definitions.

## Second reading by Q119

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
