## Worker report

The new module `Sheaf.RepresentationTheory.Sl2InvariantComplement` states
`RepresentationTheory.exists_sl2_invariant_complement`, with one postponed theorem
and no definitions. Only the item's `lean` field changes. No statement correction,
new node, dependency repair, or disputed statement is needed.

I read the item's statement, source, all six proof steps and dependencies. I read
its sole statement dependency `def-weil-finite-dimensional-subspace`: its Mathlib
match is `FiniteDimensional`, not a missing Lean record. The declaration in
`Mathlib.LinearAlgebra.FiniteDimensional.Defs`, lines 72–76, is finite generation
of a vector space, exactly the finite-span definition in the dependency node.

Hypothesis and clause correspondence:

- A rational vector space of arbitrary size is `(V : Type u) [AddCommGroup V]
  [Module ℚ V]`, with `universe u` explicit. `[FiniteDimensional ℚ V]` gives the
  finite-dimensional hypothesis; it does not require positive dimension.
- `E F H : Module.End ℚ V` are exactly the three rational linear endomorphisms.
  Endomorphism multiplication is composition, in the order used by the node.
- `hHE : H * E - E * H = (2 : ℚ) • E` renders HE − EH = 2E.
- `hHF : H * F - F * H = (-2 : ℚ) • F` renders HF − FH = −2F.
- `hEF : E * F - F * E = H` renders EF − FE = H.
- `U : Submodule ℚ V` supplies the rational linear subspace. The binders `hEU`,
  `hFU`, and `hHU` separately say that membership in U implies membership of
  E v, F v, and H v in U. These are precisely the three image-containment
  hypotheses, without adding invariance under any other operator.
- `∃ C : Submodule ℚ V` supplies a rational linear complement. `IsCompl U C`
  means disjointness and supremum equal to top. For submodules this is exactly
  existence and uniqueness of v = u + c. I checked Mathlib's
  `Submodule.existsUnique_add_of_isCompl_prod` and
  `Submodule.existsUnique_add_of_isCompl` in `Mathlib.LinearAlgebra.Projection`,
  lines 235–242: they explicitly recover the unique pair in U × C.
- The three final conjuncts separately assert E(C) ⊆ C, F(C) ⊆ C, and H(C) ⊆ C.
- There are no faithfulness, nilpotence, diagonalizability, algebraic-closure,
  nonzero-vector, or positive-dimension hypotheses.

Edge cases checked before writing: if V = 0, U = C = 0 is allowed. If U = 0,
C = V is stable under every linear operator. If U = V, C = 0 is stable. If
E = F = H = 0, the three commutator hypotheses hold and every ordinary linear
complement is stable. The general universe u retains vector spaces of every
size. No structure is chosen in a definition and no new notion is introduced.

Sources and proof dependencies:

- Read the local Milne PDF, physical pages 519–520 (printed pp.507–508):
  Theorem 23.70 assumes characteristic zero, and proof (a) invokes Weyl's
  theorem for semisimple Lie algebras. Read physical pages 487–489 (printed
  pp.475–477) for the trace form, Casimir, Lemma 22.40 and Proposition 22.41.
  The module docstring identifies the Weyl input, rather than claiming the
  group-integration conclusion. Its theorem docstring carries all six node
  proof steps, including the rational-field replacement for Schur's lemma.
- `def-wf-lie-algebra` and `def-wf-semisimple-lie-algebra` are Mathlib matches.
  The proof import `WeilConjectures.Mathlib.Algebra.Lie.Radical` also supplies
  their recorded upstream declarations
  `LieAlgebra.isSolvable_iff_exists_derivedSeries_eq_bot` and
  `LieAlgebra.hasTrivialRadical_iff_forall_isSolvable_eq_bot`; their complete
  signatures and docstrings were read in that module.
- Read `Sheaf.Algebra.Lie.PerfectLieHyperplaneCriterion`, including its full
  proof docstring and `LieModule.exists_isCompl_of_perfect_of_simple_hyperplane`.
  It is imported as a proof dependency. Its test-module universe is `max u w`,
  and it imposes no characteristic or dimension restriction on the Lie algebra.
- `lem-pc-finite-dimensional-trace-cyclic` records
  `LinearMap.trace_comp_comm'`, in `Mathlib.LinearAlgebra.Trace`, lines 265–269.
  `def-weil-endomorphism-trace` records `LinearMap.trace`, lines 72–76. Read
  both declarations; this module is imported for the proof plan.
- `lem-sfb-faithful-semisimple-trace-form` has no Lean attachment or Mathlib
  match in the read repository. It is only a proof dependency, so no interface
  for it is needed to state this item. Its future module must be added as a
  proof import when stated, per the project's normal proof-import maintenance.

Searches actually run using `msearch.py Q38 lem-sfb-sl2-invariant-complement`:

- leansearch, query “Every invariant subspace of a finite dimensional rational
  sl2 representation has an invariant complement”: eight hits. They include
  `Module.End.isSemisimple_iff` and `isSemisimple_iff'` (one endomorphism),
  `Submodule.exists_isCompl` (no invariant conclusion), and
  `LieAlgebra.InvariantForm.orthogonal_isCompl_toSubmodule` (adjoint ideals).
  None states this theorem.
- leanfinder, query “Three rational linear endomorphisms satisfying sl2
  commutator relations have a common invariant complement to each common
  invariant subspace”: eight hits on primitive vectors, weight subalgebras,
  invariant-submodule lattice equivalence, and commuting eigenspaces. None
  supplies this common stable complement. The zero/nonzero alternatives of
  the present statement are not covered by a primitive-vector lemma alone.
- loogle, query `LieSubmodule, IsCompl`: three hits,
  `LieSubmodule.isCompl_toSubmodule` and two Fitting decomposition results.
  The former translates complements already given; the latter require a
  nilpotent Lie algebra and split particular spaces. Neither is Weyl's theorem.
- grep, query `IsSemisimple|[Ww]eyl|[Cc]ompletely[Rr]educible|IsCompl` in
  `Algebra/Lie`: 25 hits. Read the invariant-form complement signature in
  `Mathlib/Algebra/Lie/InvariantForm.lean`, lines 119–140. Its input is an
  atomic ideal in an adjoint representation with a nondegenerate invariant
  form, so it is not an existing declaration of the item.
- Local rg searches for `sl2|Sl2|invariant.complement|exists_isCompl` in the
  relevant algebra folders, then `sl2|Sl2|invariant.complement|exists_isCompl.*sl`
  in all `lean/WeilConjectures` and `lean/Sheaf`, found the polynomial-model
  consumer and the conditional perfect-Lie criterion, but no exact theorem.
  The polynomial-model consumer additionally assumes nilpotent E,F and an
  integral eigenbasis, so it cannot replace this theorem. Searching the item
  id in `lean/WeilConjectures` and its complement names in
  `dag/lean_names_upstream.json` found no attachment. A search for
  `exists_sl2_invariant_complement` in Mathlib and both project source trees
  found no name collision.

Validation: prescribed scompile.py compiled the delivered module in both
sandbox and library mode, cleanly (1.3 and 1.4 seconds). `autoImplicit false`
is set; every universe and variable is explicit. The only proof is `sorry`.
Every line is at most 100 characters. No shared repository file was edited.

## Second reading by Q38

I reopened the node and the final theorem signature for a separate second
reading. This is a worker self-check; the dispatcher prohibits starting another
agent, and the maintainer performs the independent delivery review.

The three commutator binders use the same multiplication order and signs as
HE − EH = 2E, HF − FH = −2F and EF − FE = H. The U-membership implications
supply precisely all three invariance hypotheses. The existential supplies
one C with a single `IsCompl U C` and three separate stability clauses. The
unique-pair characterization of `IsCompl` in Projection confirms the node's
explicit meaning of direct sum. There are no extra assumptions on E,F,H or U.
The unrestricted `Type u` and absence of a nontriviality assumption preserve
all listed zero cases. The finite-dimensionality dependency uses its existing
Mathlib match, and the proof imports follow the currently stated dependencies.
No mismatch was found and no signature change was needed after compilation.
