## Worker report

Item `lem-weil-matrix-rank-field-extension`, module `Sheaf.LinearAlgebra.MatrixRankFieldExtension`,
theorem `Matrix.rank_map_field_extension` (proof `sorry`). The node was split on 2026-10-09 and
had no declaration; it appeared in the stage-2 queue today when a target reached it again.

Rendering:

- `ι : K → L` a ring homomorphism of fields: `{K : Type u} {L : Type v} [Field K] [Field L]
  (ι : K →+* L)` (def-weil-field; the node's general form, a subfield being the inclusion).
- `A` an `m × n` matrix over `K`, `m, n ≥ 0`: `{m n : ℕ} (A : Matrix (Fin m) (Fin n) K)`
  (def-weil-matrix); over `L` it is `A.map ι`.
- `rank_F(A)`, the dimension of the row span: `Matrix.rank` (the `mathlib_match` of
  def-weil-matrix-rank, `Matrix.rank_eq_finrank_span_row`).
- `rank_L(A) = rank_K(A)`: `(A.map ι).rank = A.rank`.
- "Equivalently, a family of rows is linearly independent over `L` iff over `K`":
  `∀ s : Set (Fin m), LinearIndependent L (fun i : s ↦ (A.map ι).row i) ↔
  LinearIndependent K (fun i : s ↦ A.row i)`.

Edge cases `m = 0`, `n = 0`; independent universes for `K` and `L`. All proof dependencies are
Mathlib leaves, so rule 7 adds no import. Searches: the node's (no `Matrix.rank` lemma for
`A.map f` in Mathlib), repeated in the pinned Mathlib (`grep rank_map` in
`LinearAlgebra/Matrix`) and in `lean/`: none. Compile: 1.2 s.

## Second reading by Z2

Independent reader Z2-mrf (a fresh `codex exec` session that did not write the module):

VERDICT: PASS

1. The Lean statement correctly formalizes fields `K`, `L` in independent universes, an arbitrary field homomorphism `ι : K →+* L`, and `A : Matrix (Fin m) (Fin n) K`; `m = 0` and `n = 0` behave correctly.

2. `(A.map ι).rank = A.rank` matches the intended row-span dimension equality via `Matrix.rank` and `rank_eq_finrank_span_row`, with no weakened or added hypotheses.

3. The equivalence clause is correctly represented as  
   `∀ s : Set (Fin m), LinearIndependent L (fun i : s ↦ (A.map ι).row i) ↔ LinearIndependent K (fun i : s ↦ A.row i)`. Subtype indexing by `s` gives exactly arbitrary families of selected rows.

4. The four proof steps in the docstring agree with the node’s four proof records, including all cited dependencies and the `(blueprint: lem-weil-matrix-rank-field-extension)` tag.

5. Imports are appropriate: `Mathlib.LinearAlgebra.Matrix.Rank` and `Mathlib.LinearAlgebra.LinearIndependent.BaseChange`.

6. The file is 54 lines, compiles successfully with `lcompile.py`, and the declaration name is not duplicated in the project or Mathlib.

7. Searches found no existing theorem establishing this matrix-rank-under-field-extension equality; related Mathlib lemmas only provide its ingredients.
