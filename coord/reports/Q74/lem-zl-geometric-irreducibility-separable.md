## Worker report

The module `Sheaf.FieldTheory.GeometricIrreducibilitySeparable` states
`AlgebraicGeometry.geometricallyIrreducible_iff_separableElements_mem`.  It uses
`k K : Type u` with `[Field k] [Field K] [Algebra k K]`, so the field extension is the
canonical algebra map `algebraMap k K`.  The left side is the Mathlib predicate
`GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap k K)))`, which is the
geometric irreducibility condition for `K/k`.  The right side quantifies every `α : K`; the
hypothesis `IsSeparable k α` is Mathlib's separably algebraic element predicate (its
`IsSeparable.isIntegral` theorem supplies algebraicity), and the conclusion
`α ∈ Set.range (algebraMap k K)` says that `α` belongs to the base field.  Thus each
hypothesis and both clauses of the equivalence are rendered directly in the declaration.

The statement dependencies are used as follows: `Algebra` from
`Mathlib.Algebra.Algebra.Defs` supplies the field-extension structure; the
`def-pc-geometrically-irreducible` dependency is the Mathlib declaration
`AlgebraicGeometry.GeometricallyIrreducible`; and
`def-weil-pbc-separable-algebraic-extension` is the Mathlib declaration
`Algebra.IsSeparable` for the extension notion, while the element-level predicate in this
statement is Mathlib `IsSeparable`.  The proof-dependency modules that are already stated
are imported: `Sheaf.FieldTheory.SeparableTensorAlgebraicClosure` and
`Sheaf.RingTheory.PowerGeneratedSpectrumHomeomorphism`, as well as the Mathlib modules
for `separableClosure`, `algebraicClosure`, `IntermediateField.adjoin.powerBasis`,
`IntermediateField.finiteDimensional_adjoin`, and `separableClosure.isPurelyInseparable`.
The tensor-product module already imports `Sheaf.FieldTheory.SeparableExtension`, so that
notion is available transitively. The recorded upstream separable-extension module was
also read with `scompile.py --source`; it has the same definitions. Importing it as well
would duplicate the declarations already provided by the tensor-product dependency.
The three geometric-irreducibility proof lemmas without Lean records have no modules to
import yet; their complete roles are retained in the six-step proof docstring.

Edge cases checked: `K = k` gives the identity map and every separable element is in its
range; purely inseparable extensions have no nontrivial `IsSeparable` elements by
`IsPurelyInseparable.inseparable`; and a nontrivial finite separable extension has a
separable element outside the base, so the right side fails as expected.  The universe is
shared (`Type u`), following the recorded Mathlib geometric-irreducibility interface. Any
pair of fields can be placed in a common universe by lifting the smaller one; the
statement imposes no algebraicity, finite generation, perfection, or characteristic
restriction. The geometric predicate quantifies field tests in the scheme universe, as
explained in `def-pc-geometrically-irreducible.mathlib_match`. Further checks: k(t)/k
satisfies the criterion, and C/R fails it because i is separably algebraic outside R.

Searches made:

* `msearch.py ... leanfinder "A geometrically irreducible field extension contains no nontrivial separable algebraic elements over the base"`: eight hits, including `IsPurelyInseparable.inseparable` and purely inseparable criteria, but no geometric-irreducibility equivalence.
* `msearch.py ... loogle "GeometricallyIrreducible, IsSeparable, Set.range algebraMap"`: zero hits; Loogle reported `GeometricallyIrreducible` unknown.
* `msearch.py ... grep "GeometricallyIrreducible.*IsSeparable" Mathlib/FieldTheory`: zero hits.
* `rg` over `WeilConjectures/` and `lean/Sheaf/` for geometric irreducibility and separable-element criteria: no existing declaration of this equivalence.

* `msearch.py ... leansearch "A field extension is geometrically irreducible if and only if each separably algebraic element lies in the base field"`: eight hits on purely inseparable criteria, relative separable closure and separability of a simple extension; no geometric-irreducibility criterion.
* Exact identifier and item-id searches in Mathlib, upstream, the shared Lean library and `dag/lean_names_upstream.json` found no declaration clash or existing statement.

The Stacks source `algebra.tex`, lemma-geometrically-irreducible-separable-elements
(Tag 0G33), was read in full and agrees exactly with the node. The dependency signatures
and docstrings were read directly in the pinned sources. `IsSeparable k α` includes
algebraicity, so no separate algebraicity hypothesis is needed or omitted.

No statement correction or `STATEMENT-DISPUTED` issue was found. The node differs from
the shared original only in `lean`; its date is the actual UTC date returned by `date -u`.
Compilation uses only the prescribed `scompile.py` / `deliver2.py` wrappers.

## Second reading by Q74

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
