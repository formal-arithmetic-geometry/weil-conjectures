## Worker report

The module [lean/Sheaf/FieldTheory/FiniteSeparableClosure.lean](lean/Sheaf/FieldTheory/FiniteSeparableClosure.lean)
states `finite_separable_closure`.  It uses fields `k : Type u` and `K : Type v`, their field
instances and an algebra structure `[Algebra k K]`.  The hypothesis
`hfg : (⊤ : IntermediateField k K).FG` renders “the field extension `K/k` is finitely
generated”.  The relative separable closure `separableClosure k K` is Mathlib's intermediate
field of elements separably algebraic over `k`; this is the node's `k' ⊆ K`.  The first
conclusion,
`GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap (separableClosure k K) K)))`,
renders that `K/k'` is geometrically irreducible, using the structure morphism of the affine
spectrum.  The second conclusion `FiniteDimensional k (separableClosure k K)` renders that
`k'/k` is finite.  The proof is `sorry`, as required at stage 2.

The statement dependencies are recorded Mathlib declarations: `Algebra` (the field-extension
convention), `AlgebraicGeometry.GeometricallyIrreducible` (geometric irreducibility of the
spectrum morphism), `Algebra.IsSeparable`/`separableClosure` for the separable-algebraic
closure notion, and the associated `IntermediateField` structures.  The concrete declarations
used by the module are `AlgebraicGeometry.GeometricallyIrreducible`,
`separableClosure`, and `IntermediateField.FG`; the module imports
`Mathlib.AlgebraicGeometry.Geometrically.Irreducible` and
`Mathlib.FieldTheory.SeparableClosure` (the latter provides `IntermediateField.FG`; the
maintainer's review removed a redundant import of
`Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra`).

Edge cases checked against the statement are `K = k` (the closure is `k` and the identity
spectrum map is geometrically irreducible), a finite separable extension (the closure is all of
`K`, so the first map is an identity and the finite conclusion is the given finite extension),
a purely inseparable finitely generated extension (the closure can equal `k`, while geometric
irreducibility of `K/k` is retained), positive and zero characteristic, and the empty/zero
finite-generation set represented by `IntermediateField.FG`.

Existing-declaration searches were run before writing the module:

* `msearch.py ... leanfinder "For a finitely generated field extension, the subfield of elements
  separably algebraic over the base is finite and the extension is geometrically irreducible over
  that subfield"`: hits `separableClosure`, `IsSepClosure`, `Algebra.IsSeparable`, and
  `Field.exists_primitive_element`, but no combined theorem; no exact match.
* `msearch.py ... loogle "separableClosure, Algebra.FiniteType, GeometricallyIrreducible"`:
  zero hits (Loogle reports `GeometricallyIrreducible` as unknown); no exact match.
* `msearch.py ... grep "separableClosure.*FiniteType|GeometricallyIrreducible" Mathlib/FieldTheory`:
  zero hits for a combined declaration.
* `rg` over `WeilConjectures/` for `finite_separable`, `separableClosure`, and
  `geometricallyIrreducible`: only unrelated uses and helper declarations; no theorem for this
  node.  `grep -rn "lem-zl-finite-separable-closure" WeilConjectures` found no occurrence.
* The DAG search found no existing Lean record for this node and no duplicate theorem statement.

No `STATEMENT-DISPUTED` flag or node fault was found.

## Second reading by Q72

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

Maintainer's review (fix): the unused import `Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra`
was removed (H9), and step 1 of the statement docstring now follows the node's proof step 1
(the separable closure `F` of `k'` in `K`, permanence in the tower `k ⊆ k' ⊆ F`, `F = k'`, then
Tag 0G33 (2) ⇒ (1)) instead of claiming transitivity in the tower `k ⊆ k' ⊆ K` (H8). The
signature and `lean.statement` are unchanged.
