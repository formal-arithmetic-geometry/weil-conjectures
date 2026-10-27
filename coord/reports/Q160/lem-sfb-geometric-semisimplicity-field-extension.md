## Worker report

The delivery states `Module.End.geometricSemisimplicity_fieldExtension` in
`Sheaf.LinearAlgebra.GeometricSemisimplicityFieldExtension`. Its only proof is `sorry`.
There are no new definitions, dependency modules, or changes to the informal statement.
The item's node copy changes only `lean`.

Source read: Milne, *Algebraic Groups* (2017), Section 9(b), printed pp.166–169
(PDF pages 178–181), using `pdftotext -layout`. Page 166 defines diagonalizability by an
actual eigenbasis and geometric semisimplicity by diagonalizability after extension;
it states the minimum-polynomial criterion. The complement comparison and unrestricted
extension comparison are the supporting linear algebra already supplied in this DAG node.
No invertibility hypothesis from Theorem 9.11 is imported.

Hypotheses and clauses, matched individually:

- The perfect field k is `{k : Type u} [Field k] [PerfectField k]`. Mathlib's
  `PerfectField` says irreducible polynomials are separable, equivalent to the node's
  every-algebraic-extension formulation. Its instance
  `Algebra.IsAlgebraic.isSeparable_of_perfectField` was read in `FieldTheory/Perfect.lean`.
- The finite-dimensional vector space is `{V : Type v} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]`. The operator is `(T : Module.End k V)`.
- The specified monic least-degree annihilator is `minpoly k T`, not an arbitrary
  annihilating polynomial. `FieldTheory/Minpoly/Basic.lean` defines this very polynomial;
  finite dimensionality supplies integrality. Its `minpoly.subsingleton` gives one
  for the zero space, including the zero endomorphism algebra.
- Condition (i) is `T.IsSemisimple`, using Mathlib's existing notion. The full signature
  of `Module.End.isSemisimple_iff` was read: it is exactly
  `T.IsSemisimple ↔ ∀ p ∈ T.invtSubmodule, ∃ q ∈ T.invtSubmodule, IsCompl p q`.
  Membership is invariance under T, and `IsCompl` is the subspace direct-sum condition.
- Condition (ii) is `(minpoly k T).Separable`. This is coprimality with the derivative,
  equivalent to the node's distinct-root definition: the existing
  `Polynomial.nodup_aroots_iff_of_splits` gives the equivalence for every nonzero
  polynomial splitting over the chosen extension. The monic minimum polynomial is
  nonzero, and the chosen algebraic closure splits it. This equivalence includes one.
- Condition (iii) is written explicitly, with no duplicate definition:
  `∃ (n : ℕ) (b : Module.Basis (Fin n) (AlgebraicClosure k)
  (AlgebraicClosure k ⊗[k] V)) (μ : Fin n → AlgebraicClosure k),
  ∀ i : Fin n, Module.End.HasEigenvector (T.baseChange (AlgebraicClosure k)) (μ i) (b i)`.
  This asserts an actual basis of eigenvectors after scalar extension. Finite indexing
  is equivalent to an unrestricted basis here because V is finite dimensional.
- The first two conjuncts are `(i ↔ ii) ∧ (ii ↔ iii)`, expressing precisely the
  three-way equivalence, without asserting that any of the conditions holds unconditionally.
- Every extension is an arbitrary `(L : Type w) [Field L] [Algebra k L]`. There is no
  `PerfectField L`, algebraicity, finite-degree assumption, or equality of universes.
  A universally quantified arbitrary parameter outside the conjunction is equivalent
  to placing that universal quantifier in the extension clause: the other clauses are
  independent of L, and L = k is always available.
- The tensor product is Mathlib's `L ⊗[k] V`. The canonical operator is `T.baseChange L`;
  `LinearMap.baseChange_tmul` reads literally `T.baseChange L (a ⊗ₜ x) = a ⊗ₜ T x`.
  Its definition is `AlgebraTensorModule.map LinearMap.id T`; no arbitrary map is used.
- Geometric semisimplicity over L is the same explicit eigenbasis condition for
  `((T.baseChange L).baseChange (AlgebraicClosure L))` acting on
  `AlgebraicClosure L ⊗[L] (L ⊗[k] V)`. The final conjunct is its iff with condition
  (iii), in the direction stated by the node.
- Zero spaces are permitted: there is no `Nontrivial V`, positive-rank assumption,
  nonempty eigenvalue set, or invertibility hypothesis. Taking n = 0 represents the
  empty eigenbasis. The minimal polynomial is one, with no repeated roots.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`; supplied by public imports.
- `def-weil-polynomial-ring`: `Polynomial`, `Mathlib.Algebra.Polynomial.Basic`;
  this recorded dependency module is publicly imported.
- `def-weil-algebraic-closure`: `AlgebraicClosure`,
  `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`; publicly imported. The signature
  and docstring, and `IsAlgClosure` in `IsAlgClosed.Basic`, were read.
- Additional existing Mathlib interfaces used directly: `PerfectField`, `minpoly`,
  `Module.End.IsSemisimple`, `Module.Basis`, `Module.End.HasEigenvector`,
  `LinearMap.baseChange`, and `Polynomial.Separable`. These are existing notions,
  written inline where appropriate, so no new definition node is needed.

Proof-dependency imports: `Mathlib.LinearAlgebra.Semisimple` provides the squarefree
minimal-polynomial and squarefree-annihilator leaves; `Mathlib.FieldTheory.Perfect`
provides the squarefree/separable leaf; separability field-map and distinct-linear-factor
leaves are in its public dependency `Mathlib.FieldTheory.Separable`.
`Mathlib.LinearAlgebra.Eigenspace.Semisimple` and `Mathlib.Algebra.Polynomial.Splits`
are plain proof imports for eigenspace spanning and algebraically closed factorization.
The proof dependency `lem-sfb-endomorphism-minpoly-scalar-extension` currently has no
recorded Lean declaration or Mathlib match, so has no module to import. It is only
needed for the postponed proof, not to state this item; the module docstring records
its role in proof steps 3–5. Every remaining proof dependency has its Mathlib interface
available through the listed imports. There are no import cycles.

Edge cases checked before and after writing: zero V; a scalar operator, including
zero; a nonzero nilpotent Jordan block (all three conditions fail); a real rotation
whose eigenvalues require extending to the algebraic closure; characteristic p and
arbitrary imperfect/transcendental extensions L/k. The extension clause only uses
separability of the original minimum polynomial and does not infer L is perfect.
Independent universes u, v, w allow all sizes of base field, space, and extension.

Searches actually run with `batch2/msearch.py Q160` and this item:

- LeanFinder: “For a finite dimensional endomorphism over a perfect field invariant
  complements, separable minimal polynomial, and diagonalizability over an algebraic
  closure are equivalent, and geometric diagonalizability is preserved and reflected
  by any field extension”. Eight hits, including
  `Module.End.IsSemisimple.minpoly_squarefree` and Jordan–Chevalley existence; no
  complete statement matching this item.
- LeanSearch: “Invariant complements equivalent to geometric diagonalizability over
  perfect field and invariance under arbitrary scalar extension”. Eight hits,
  including `Module.End.isSemisimple_iff` and `isSemisimple_iff'`; partial interfaces.
- Loogle: `Module.End.IsSemisimple, LinearMap.baseChange`. Zero hits.
- Mathlib grep through msearch: `IsDiagonalizable|geometric.*semisimple|semisimple.*baseChange`
  in `LinearAlgebra`. Zero hits.
- Direct rg of Mathlib `LinearAlgebra` for diagonalizability, eigenbasis, eigenvectors,
  semisimplicity, and tensor base change found the existing `HasEigenvector`,
  `Module.End.IsSemisimple`, and `LinearMap.baseChange` interfaces. Direct reads
  established their signatures as described above.
- Direct rg of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for `IsDiagonalizable`, geometric semisimplicity, this item's id, and the proposed
  theorem name found no matching theorem. The monodromy module's
  `RepresentedDegreeDatum.IsGeometricallySemisimple` concerns restriction of a Weil
  representation to its geometric subgroup, which is a different notion.

No statement dispute or source correction was found. All explicit variables and
universes are bound. The theorem docstring reproduces all five proof steps, including
the distinct-root/coprimality bridge added in the accepted stage-1 review.

## Second reading by Q160

The dispatcher explicitly prohibits starting other agents; this section records a
separate second pass by the same worker, not an independent reviewer. The maintainer's
independent delivery review remains required.

Reopened the node statement and the final Lean declaration together. Checked the
perfect-field binder, finite-dimensional binder, and endomorphism; the specified
minimum polynomial; invariant complements through the read `isSemisimple_iff`;
separability through `nodup_aroots_iff_of_splits`; the actual eigenbasis over the
canonical closure; and the extension clause over the tensor product with no
perfectness or algebraicity restriction. The conjunction is exactly `(i ↔ ii) ∧
(ii ↔ iii) ∧ (iii over L ↔ iii over k)`. A finite basis indexed by `Fin n` allows
n = 0 and expresses every basis in these finite-dimensional spaces.

The compiler caught a missing tensor-notation scope and a namespace issue in field
notation for eigenvectors of a base-changed linear map. These were repaired by
`open scoped TensorProduct` and explicit `Module.End.HasEigenvector`; they do not
change the mathematics. One long line was wrapped. The second reading found no
hypothesis or conclusion mismatch and required no informal-node changes. The old
CompactObject example is now withdrawn; its recorded upstream module was read for
the current public module conventions.
