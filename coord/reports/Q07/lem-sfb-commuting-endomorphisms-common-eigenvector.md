## Worker report

This stage-2 delivery states `Module.End.exists_common_eigenvector_of_commute` in
`Sheaf.LinearAlgebra.CommutingEndomorphismsCommonEigenvector`. Its proof is `sorry`;
no definitions or additional nodes are needed. The natural-language statement and the
accepted Q16 stage-1 split are unchanged. The inherited failure was a stage-1 deliver.py
unchanged-node refusal; coord/brief-stage2.md §0 explicitly permits this stage-2 handoff.
The queue lists this item at stage 2 with no existing Lean record; there is no repair note.

Source checked: Milne, *Algebraic Groups* (2017), Lemma 16.11, printed p.327
(PDF page 339). Its proof restricts commuting endomorphisms to an invariant eigenspace.
The node gives the finite-family consequence and records honestly its alternative
induction on the number of operators. The module docstring carries that complete proof,
including the empty-family case, subspace finiteness, stability, restriction and assembly.

Each hypothesis and clause is rendered as follows:

| Node | Lean |
| --- | --- |
| k is a field | `{k : Type u} [Field k]` |
| k is algebraically closed | `[IsAlgClosed k]` |
| V is a k-vector space | `{V : Type v} [AddCommGroup V] [Module k V]` |
| V is finite-dimensional | `[FiniteDimensional k V]` |
| V is nonzero | `[Nontrivial V]`, equivalent for a vector space to existence of a nonzero vector |
| I is a finite set, possibly empty | `{I : Type w} [Finite I]`; no nonemptiness or chosen enumeration |
| k-linear endomorphisms indexed by I | `(T : I → Module.End k V)` |
| Every pair commutes under composition | `(hT : ∀ i j : I, Commute (T i) (T j))` |
| A common vector and scalars for every index | `∃ (x : V) (μ : I → k), ...` |
| The vector is nonzero | `x ≠ 0` |
| Every eigenvector equation | `∀ i : I, T i x = μ i • x` |

`Module.End` is Mathlib's linear endomorphism type, whose multiplication is
`LinearMap.comp`; `Commute` therefore expresses exactly the composition equality.
All universes and variables are explicitly bound. Independent universes u, v, w
allow arbitrary sizes of field, vector space and finite index set.

Dependency declarations read and used:

- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs, available through the public imports.
- def-weil-algebraic-closure: the `IsAlgClosed` clause of its Mathlib match, in
  Mathlib.FieldTheory.IsAlgClosed.Basic. No choice of an algebraic closure is imposed.
- def-weil-finite-dimensional-subspace: `FiniteDimensional`, in
  Mathlib.LinearAlgebra.FiniteDimensional.Defs (finite generation as a module).
- Endomorphisms: `Module.End`, `Module.End.mul_eq_comp`, `Module.End.mul_apply`,
  Mathlib.Algebra.Module.LinearMap.End.
- Proof dependency lem-zl-alg-closed-endomorphism-eigenvalue:
  `Module.End.exists_eigenvalue`, Mathlib.LinearAlgebra.Eigenspace.Triangularizable,
  imported without `public`.
- Proof dependency lem-trf-vector-space-quotient-dimension:
  `Submodule.finrank_quotient_add_finrank`, Mathlib.LinearAlgebra.Dimension.RankNullity,
  imported without `public`; its subspace-finiteness clause is
  `FiniteDimensional.finiteDimensional_submodule` in the public Defs import.
  Both submodule and quotient instances and the recorded rank-nullity signature were read.

Edge cases checked before writing: an empty index type leaves only a nonzero vector
and a vacuous function/equation family, supplied by Nontrivial V; a singleton is ordinary
eigenvalue existence; dimension one gives scalar operators; zero operators allow zero
scalars. A nilpotent Jordan block is allowed, so no diagonalizability or invertibility is
assumed. V = 0 is excluded exactly by the source's nonzero-space hypothesis. All positive
characteristics and characteristic zero are included without extra assumptions.

Searches made through msearch.py:

- leanfinder: "A finite commuting family of linear endomorphisms of a nonzero finite
  dimensional vector space over an algebraically closed field has a common eigenvector".
  Eight hits: single-operator eigenvalue existence and generalized-eigenspace results;
  no exact family theorem.
- loogle: `"Module.End", "eigen", "Commute"`. Two hits:
  `Module.End.map_add_of_iInf_genEigenspace_ne_bot_of_commute` and
  `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute`.
  The latter's signature and docstring were read; it states spanning by intersections of
  maximal generalized eigenspaces, rather than a common true eigenvector.
- grep: `common.*eigen|simultaneous.*(eigen|triang)|commuting family`.
  Nineteen hits in Eigenspace/Pi, Lie weights/theorem, JointEigenspace and related files.
  JointEigenspace assumes symmetric operators; Lie results have other algebraic data or
  characteristic hypotheses. None is an exact match.
- leansearch: "Pairwise commuting endomorphisms on a nonzero finite dimensional vector
  space over an algebraically closed field admit a simultaneous eigenvector". Eight hits,
  again single-operator existence, generalized eigenspaces and symmetric-operator theorems.
- rg in the project's WeilConjectures and Sheaf sources and dag/lean_names_upstream.json:
  `common.*[Ee]igen|[Ee]igenvector.*[Cc]omm|commut.*[Ee]igenvector|exists_common_eigenvector`.
  Found the distinct solvable Lie-algebra theorem and a Frobenius weight-gap comment.
  The Lie-algebra result is not this arbitrary-characteristic endomorphism-family statement.
- grep for the exact blueprint id in WeilConjectures: no hit. A further exact-name rg
  across Mathlib, WeilConjectures, Sheaf and the upstream name index found no collision.

No statement dispute, correction, missing dependency interface or new definition was found.
The sole postponed theorem has the matching DAG node and a full source/proof docstring.
Validation: scompile.py compiled both the sandbox and final library module name cleanly
with no warnings. The node differs only in lean; the recorded signature is verbatim and
all Lean source lines are at most 100 characters. The delivery dry run follows.

## Second reading by Q07

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
