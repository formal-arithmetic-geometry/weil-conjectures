## Worker report

The module `Sheaf.RepresentationTheory.CyclotomicFieldBrauerSplitting` states
`MonoidAlgebra.exists_algEquiv_pi_matrix_of_exponent_roots`, with one `sorry` and
no new definitions. The node is unchanged except for its `lean` record.

Clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| K is a characteristic-zero field | `(K : Type u) [Field K] [CharZero K]` |
| Integer N ≥ 1 | `(N : ℕ) (hN : 0 < N)`; positive integers are encoded by positive naturals |
| Element ζ in K with ζ^N = 1 | `(ζ : K) (hζ : ζ ^ N = 1)` |
| ζ^j ≠ 1 for every integer 0 < j < N | `hζprim : ∀ j : ℕ, 0 < j → j < N → ζ ^ j ≠ 1`; every such integer is a positive natural |
| Finite group G | `(G : Type v) [Group G] [Finite G]` |
| g^N = 1 for every g | `hG : ∀ g : G, g ^ N = 1` |
| K[G], basis [g], bilinear product [g][h] = [gh] | `MonoidAlgebra K G`; its actual coefficients are finitely supported functions, and `MonoidAlgebra.single_mul_single` is the stipulated product |
| An integer r ≥ 1 | `∃ r : ℕ, 0 < r ∧ ...` |
| Positive integers d_1,...,d_r | `∃ d : Fin r → ℕ, (∀ i : Fin r, 0 < d i) ∧ ...` |
| Product of full d_i × d_i matrices over K | `∀ i : Fin r, Matrix (Fin (d i)) (Fin (d i)) K` with its standard product algebra structure |
| A K-algebra isomorphism to that product | `Nonempty (MonoidAlgebra K G ≃ₐ[K] ...)` |

The two input types use independent universes `u v`. The reindexing from
1,...,r to `Fin r` changes no objects or assumptions. There is no assumption
that K is algebraically closed, that N equals the least exponent, or that
the group is commutative.

Dependency interfaces read and used:

- Statement dependency `def-weil-matrix`: `Matrix` from
  `Mathlib.LinearAlgebra.Matrix.Defs`, read with its full docstring/signature.
  `Mathlib.Data.Matrix.Basic` supplies the square-matrix algebra instances.
- `Mathlib.Algebra.MonoidAlgebra.Basic`: the existing group algebra, whose
  definition and convolution multiplication were read in
  `Mathlib.Algebra.MonoidAlgebra.Defs`. The basis vector [g] is `single g 1`.
- Proof dependency `lem-per-maschke-finite-group-algebra`:
  `MonoidAlgebra.Submodule.instIsSemisimpleModule` from
  `Mathlib.RepresentationTheory.Maschke`.
- Proof dependency `lem-per-semisimple-algebra-matrix-division`:
  `IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite` from
  `Mathlib.RingTheory.SimpleModule.WedderburnArtin`.
- Proof dependency `lem-pc-algebraic-closure-exists-unique`:
  `AlgebraicClosure` and `IsAlgClosure.equiv`, imported through
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`.
- Proof dependency `def-weil-pbc-module-tensor-product`: `TensorProduct`
  and its map interface, imported through `Mathlib.LinearAlgebra.TensorProduct.Map`.
- Proof dependency `lem-per-semisimple-scalar-extension-kzero-criterion`:
  `RepresentationTheory.divisionFactors_bijective_of_splitGrothendieck_surjective`
  from `Sheaf.RepresentationTheory.SemisimpleScalarExtensionCriterion`;
  its complete signature and proof docstring were read. It is a private proof import.
- `lem-per-brauer-monomial-induction` currently has neither a Lean record nor
  a Mathlib match, so there is no proof module to import yet. Its full proof step
  is retained in the theorem docstring. Its statement is not needed to type this item.

Source check: read ILO Exposé X, printed pp.138–139 (PDF pages 144–145),
in particular the projective Λ[G]-module lifting cited to Serre immediately
before (5), and the cyclotomic coefficient localization. Read the current
blueprint's `lem-per-artin-gabber-affine-curve.md` and proof in
`literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/`.
The splitting theorem is the auxiliary representation-theoretic input already
identified by this node, not a literal assertion of ILO. Serre remains not obtained,
as recorded by the source field; no proof is supplied here. The docstring carries
all five accepted proof steps and names every cited proof dependency.

Edge cases checked mathematically before writing:

- N = 1: ζ = 1 and G is trivial; the primitive-root interval is empty, and
  r = 1, d = 1 gives K[G] ≃ K ≃ M_1(K).
- The trivial group is allowed also when N > 1 and K has the specified root.
- N = 0 is excluded explicitly, as required by the node.
- A group is nonempty; the nonzero basis element [1] excludes the empty
  matrix product. The conclusion states `0 < r` explicitly.
- `0 < d i` excludes zero-dimensional matrix factors.
- K = ℚ and G cyclic of order 2 satisfy N = 2, ζ = -1 and give ℚ × ℚ.
- ℝ and the quaternion group would not split, but ℝ lacks the stipulated
  primitive fourth root, so that counterexample is correctly excluded.
- A larger annihilating exponent is permitted: minimality of N is never imposed.

Searches (2026-10-24; wrapper outputs preserved in `searches.jsonl`):

- `msearch.py ... leanfinder "A characteristic zero field with a primitive root of unity of a finite group exponent splits its group algebra into a product of full matrix algebras"`:
  eight hits, including Maschke, character criteria, and
  `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`; no exact match.
- `msearch.py ... leansearch "Brauer splitting theorem finite group algebra primitive root exponent product matrix algebras"`:
  eight hits, including Wedderburn–Artin and `X_pow_sub_C_splits_of_isPrimitiveRoot`;
  no exponent-root group-algebra splitting theorem.
- `msearch.py ... loogle "MonoidAlgebra, Matrix"`: zero hits.
- `msearch.py ... grep "Brauer|splitting.field|Schur.index" RepresentationTheory`:
  zero hits.
- `rg -n -i 'cyclotomic.*split|split.*cyclotomic|brauer.*splitting|exponent.*roots|roots.*exponent'`
  on `lean/WeilConjectures` and `lean/Sheaf`: unrelated coefficient and root-sheaf
  constructions only. The initial broader Brauer search also found Galois/Brauer
  comparison modules, none stating this finite-group theorem.
- Search for this node id in `lean/WeilConjectures`: no matches.
- Read the closest Mathlib result in `RingTheory/SimpleModule/IsAlgClosed.lean`:
  it assumes `[IsAlgClosed F]`, so cannot serve as this statement.
- Exact proposed declaration and module-name searches in Mathlib, both project
  source roots and `dag/lean_names_upstream.json`: no existing declaration.

No statement correction, new node, dependency repair, or disputed statement.
`scompile.py Q137 lem-per-cyclotomic-field-brauer-splitting <module>` passed
both sandbox and library checks (5.2 s and 5.1 s), without errors or warnings.

## Second reading by Q137

Clause-by-clause self-review with the node and final source open confirms every
hypothesis and conclusion in the table above. Checked the standard group algebra's
convolution product, full square-matrix multiplication rather than entrywise
multiplication, product algebra structure, independent universes, both positivity
clauses, and the absence of an algebraically-closed-field hypothesis. No mismatch
was found and no statement was changed. This is a self-review; the dispatcher brief
assigns the independent delivery review to the maintainer and prohibits starting
other agents, so no independent worker review is claimed.
