## Worker report

The module `Sheaf.Algebra.Homology.DVRProjectiveComplexMatrixModel` states
`CochainComplex.exists_finite_matrix_model_of_projective_over_dvr`, with its proof
`sorry`. No definitions or other theorems are introduced. The node is unchanged
except for its `lean` record.

Hypotheses and conclusions, matched clause by clause:

- The scalar DVR is `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]`. In particular this includes the nonfield condition;
  no completeness, residue characteristic, or coefficient extension is assumed.
- The integer interval is `(a b : ℤ) (hab : a ≤ b)`.
- The given cochain complex is `P : CochainComplex (ModuleCat.{v} R) ℤ`.
  Its bundled differentials are R-linear, and its `d_comp_d` field supplies the
  square-zero relation. Both ring and module universes are bound independently.
- The exact support hypothesis is `hP : ∀ i : ℤ, i < a ∨ b < i →
  IsZero (P.X i)`. For modules, categorical zero means the underlying module is
  trivial, rather than literally requiring its carrier to equal a chosen zero type.
- Finite generation in every degree is `[∀ i : ℤ, Module.Finite R (P.X i)]`;
  projectivity in every degree is `[∀ i : ℤ, Module.Projective R (P.X i)]`.
- The ranks are `n : ℤ → ℕ`, exactly nonnegative integers, with
  `∀ i : ℤ, i < a ∨ b < i → n i = 0`.
- The requested coordinate isomorphisms are
  `e : ∀ i : ℤ, (Fin (n i) → R) ≃ₗ[R] P.X i`.
- The matrices are `D : ∀ i : ℤ, Matrix (Fin (n (i + 1))) (Fin (n i)) R`:
  the target degree indexes rows and the source degree indexes columns.
- Differential compatibility is stated pointwise for every vector:
  `(P.d i (i + 1)).hom (e i x) = e (i + 1) ((D i).mulVec x)`.
  `Matrix.mulVec` is multiplication of a matrix by a coordinate column vector.
- The relation on consecutive matrices is `∀ i : ℤ, D (i + 1) * D i = 0`.
- The concluding strict isomorphism of complexes is expressed by its full
  component data, the linear equivalences `e i` and their differential
  compatibility. The square-zero matrices make the coordinate modules into a
  complex; the forward compatibility is exactly its chain-map equation. Applying
  `(e (i + 1)).symm` and substituting `x = (e i).symm y` gives the inverse
  chain-map equation, and the LinearEquiv inverse laws give both composite
  identities degreewise. Thus this is an isomorphism of complexes, with all its
  data supplied, and not merely a quasi-isomorphism or a derived isomorphism.
  Every term of the coordinate complex is a finite free module over the same R;
  the rank condition makes it supported in the original interval.

Recorded dependency declarations were read with their docstrings and signatures:
`IsDiscreteValuationRing` in `Mathlib.RingTheory.DiscreteValuationRing.Basic`;
`Module.Finite` in `Mathlib.RingTheory.Finiteness.Defs`; `Module.Projective` in
`Mathlib.Algebra.Module.Projective`; and `Matrix` in
`Mathlib.LinearAlgebra.Matrix.Defs`. Each is imported publicly. Proof-only imports
are `Mathlib.LinearAlgebra.FreeModule.Basic` (`Module.Free`, the record for
`def-weil-pbc-free-module`) and `Mathlib.LinearAlgebra.FreeModule.PID`
(`Module.free_of_finite_type_torsion_free'`, the Mathlib match for
`lem-sc-dvr-fg-torsionfree-free`). The CochainComplex and ModuleCat definitions
and `HomologicalComplex.Hom.isoOfComponents` were also read.

Source read: current blueprint
`sec-six-functors-basics/sk-lem-int-integral-heart/sk-lem-int-integral-heart-local-model.proof.md`,
clause (1); Stacks `algebra.tex`, `lemma-characterize-projective` (05CF), and
`more-algebra.tex`, `lemma-dedekind-torsion-free-flat` (0AUW), part (3).
The docstring records all five steps of the node's proof, including the inverse
chain map, empty coordinates and unchanged support.

Edge cases checked before writing: the zero complex permits all ranks zero;
`a = b` leaves only one possibly nonzero term; negative bounds are allowed;
zero terms inside the interval and zero terms at its endpoints are allowed;
`Fin 0` coordinate modules and all empty rectangular matrices are valid, with
empty sums zero. The hypothesis excludes reversed intervals, as the node does.
The DVR class excludes fields and the zero ring, precisely as its definition
node requires. No characteristic is restricted. Independent universes u and v
avoid requiring the original modules to have carriers in the ring's universe.

Searches actually run for this item:

- `msearch.py ... leanfinder`, query “A bounded complex of finite projective
  modules over a discrete valuation ring has finite coordinate bases and matrix
  differentials with product zero and a strict isomorphism of complexes”: eight
  hits, including `Module.Finite.exists_comp_eq_id_of_projective` and generic
  projective-resolution/K-projective results; none states this simultaneous
  same-support coordinate theorem.
- `msearch.py ... loogle`, query `Module.Projective, Module.Free, CochainComplex`:
  successful search, zero hits.
- `msearch.py ... grep`, query `mulVecLin|def of|isoOfComponents`, subdirectory
  `Algebra/Homology`: 25 hits including `HomologicalComplex.Hom.isoOfComponents`
  and generic chain-complex constructors. These transport already supplied
  isomorphisms; they do not assert the node's DVR basis existence statement.
- `msearch.py ... leansearch`, query “Every bounded finite projective complex
  over a discrete valuation ring is isomorphic to a matrix complex with the same
  finite support interval”: eight hits, including the finite projective splitting
  theorem; none gives this theorem.
- Local `rg` of `lean/WeilConjectures` and `lean/Sheaf`, for the node id and
  `matrixModel|matrix_model|projective.*[Mm]atrix|[Mm]atrix.*[Cc]omplex`, followed
  by narrower source reads: no existing declaration of this statement.
  `MatrixComplex`, `MatrixComplex.complex`, and the minimal matrix-complex
  theorem `MatrixComplex.exists_iso_Q_obj_of_isPerfect` were inspected. The
  former constructs a complex from matrices already supplied; the latter gives
  a derived model after a homotopy replacement and does not state this strict
  same-term model. `MatrixComplex.complex` is specialized to equal ring/module
  universes. The present statement uses the existing Mathlib notions directly
  and expresses the strict isomorphism by its components, so no duplicate
  matrix-complex definition or universe restriction is introduced.
- The proposed full theorem name was searched in Mathlib, upstream, and Sheaf:
  no collision.

Validation: the server wrapper compiled the module successfully both as its
sandbox probe and under its library module name, without warnings or errors.
The delivery dry run repeats compilation and runs the server preflight.

No statement dispute, source correction, new notion, or dependency repair was
needed. No independent second reading is claimed; the maintainer performs it
under the current direct-delivery instructions.

## Second reading by Q48

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
