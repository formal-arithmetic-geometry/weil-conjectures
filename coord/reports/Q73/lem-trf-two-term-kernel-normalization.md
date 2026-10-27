## Worker report

This repairs the returned immutable head `83f730d2f6c9`. The initial saved packet passed
`deliver2.py --no-push` as `949f9fa0efe`, but still had both substantive defects named in
the return. Those defects are repaired in the files, rather than merely rebased.

`Sheaf.SecTraceFormula.TwoTermKernelNormalization` states
`Module.two_term_kernel_normalization`, with its sole theorem proof `sorry`.
`Module.IsKernelNormalizedAssembly` is a fully defined proposition describing the
canonical maps and element; its data contains no postponed proof.

Hypothesis and clause correspondence with the unchanged item statement:

* `R : Type u` and `[CommRing R]` give the arbitrary commutative ring.
* `P Q : Arrow (ModuleCat.{v} R)` encode the two complexes exactly: `left` is degree
  -1, `right` is degree 0, `hom` is their differential, all other degrees are zero.
  `a : P ⟶ Q` is Mathlib's commuting square, with equation `a.w`. There is no extra
  condition on a differential: a two-term complex has no pair of nonzero consecutive
  differentials whose composite needs to vanish.
* The eight `Module.Finite` / `Module.Projective` instances on `P.left`, `P.right`,
  `Q.left`, `Q.right` state that the four terms are direct summands of finite free modules.
* `ha : TwoTerm.DegreewiseSurjective a` is surjectivity of both component linear maps.
* `hqa : TwoTerm.QuasiIso a` is bijectivity on H^-1 (the kernel map `kernelNeg`) and on
  H^0 (injectivity and surjectivity modulo the differential ranges). No cohomology
  hypothesis is replaced by a chain isomorphism or by an unconstrained predicate.
* The four initial conclusion conjuncts give finiteness and projectivity of both
  `LinearMap.ker` terms. The two existential linear sections with `a.left ∘ₗ s = id`
  and `a.right ∘ₗ s = id` state splitting of their canonical kernel sequences.
* `Function.Bijective (TwoTerm.kernelDifferential a)` is the asserted isomorphism d_N.
  The definition is the actual restriction of `P.hom`, using the commuting square.
* `TwoTerm.determinant E` is `det(E.right) ⊗ Dual(det(E.left))` and
  `TwoTerm.kernelDeterminant a` is `det(ker a.right) ⊗ Dual(det(ker a.left))`.
  Both use the recorded `Module.determinantModule`, rather than a local determinant model.
* The final conclusion quantifies Γ as a linear equivalence `D(Q) ⊗ D(N) ≃ D(P)`
  and δ as an element of D(N), under the unique inverse T. Their predicate now quantifies
  one shared pair `γneg, γzero` and requires the recorded
  `Module.IsDeterminantExactSequenceMap` for the canonical kernel inclusions and
  the actual components of a. This pins the exact-sequence maps kernel-first.
* Γ's pure-tensor clause says
  `Γ ((qzero ⊗ φq) ⊗ (nzero ⊗ φn)) = γzero(nzero ⊗ qzero) ⊗ ψ`, where
  `ψ = (TensorProduct.lift (φn.smulRight φq)).comp γneg.symm.toLinearMap`.
  Thus ψ evaluates at p by applying γneg inverse, then the product functional
  `(n,q) ↦ φn(n) * φq(q)`. This is the inverse dual of the SAME γneg, and the positive
  factor uses the SAME γzero. Pure tensors generate, so Γ is fully determined.
* δ's clause tests every nneg and nzero with
  `ExteriorAlgebra.map (TwoTerm.kernelDifferential a) nneg.val = nzero.val`.
  Its conclusion
  `TensorProduct.rid R _ (TensorProduct.map LinearMap.id (LinearMap.applyₗ nneg) δ)
   = nzero`
  is precisely contraction of δ with nneg. The contraction sends `m ⊗ λ` to `λ(nneg) • m`.
  Hence δ corresponds to det(d_N), rather than to an arbitrary nonzero multiple of it.
  Since d_N is bijective, its exterior map preserves the determinant socles, so this
  condition tests every negative determinant vector. Finite-projective tensor-Hom
  duality makes these tests determine δ uniquely.
* `Submodule.span R ({δ} : Set D(N)) = ⊤` gives the generator assertion for that very δ.
* `∀ x, T (Γ (x ⊗ δ)) = x` gives the required inverse triangle. As T is a linear
  equivalence, this also forces insertion of δ into Γ to be T inverse, hence an
  isomorphism. The final universal clause and outer `∃! T` state uniqueness of the inverse.

Dependencies used, read at their recorded declarations:

* `Mathlib.CategoryTheory.Comma.Arrow`: `CategoryTheory.Arrow`, `Arrow.Hom`,
  `Arrow.Hom.left/right`, `Arrow.hom`, `Arrow.w`. These are reused directly; there
  is no second structure defining two-term complexes or commuting squares.
* New definition node `def-trf-two-term-determinant-encoding`, module
  `Sheaf.SecTraceFormula.TwoTermDeterminantEncoding`: `Module.TwoTerm.DegreewiseSurjective`,
  `kernelNeg`, `QuasiIso`, `determinant`, `kernelDifferential`, `kernelDeterminant`.
* `Sheaf.LinearAlgebra.ProjectiveDeterminantExactSequence`:
  `Module.IsDeterminantExactSequenceMap`, `Module.existsUnique_determinantExactSequence`.
* `Sheaf.LinearAlgebra.ProjectiveDeterminantModule`: `Module.determinantModule`.
* `Mathlib.Algebra.Module.Projective`: `Module.Projective`, projective lifting.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` for the abstract
  dependency; the concrete statement uses exactly its two-term cochain specialization.
* Mathlib tensor-product modules: `TensorProduct`, pure tensors, `TensorProduct.lift`,
  `TensorProduct.map`, `TensorProduct.rid`; duals are `Module.Dual`.
* Plain imports retain the stated proof plan: `Mathlib.LinearAlgebra.Contraction`
  (`lTensorHomEquivHomLTensor`), `Mathlib.LinearAlgebra.Dual.Lemmas`,
  `Sheaf.RingTheory.LineModuleDuality`, and
  `WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover`.
  The chart-descent proof dependency has no recorded Lean module, so none is imported.

Sources read: `literature/stacks-project/more-algebra.tex`, section-determinants-complexes
(Tag 0FJI), including the defining triangle preceding Tag 0FJJ, and lemma-det-ses
(Tag 0FJB). These specify the exact tensor ordering and kernel element used above.

Searches for the item retained from the initial packet: LeanFinder query
"kernel normalized determinant isomorphism for a surjective two term quasi-isomorphism
finite projective modules" returned eight projective-resolution/splitting results, no
normalization theorem. Loogle `LinearEquiv determinantModule TensorProduct kernel differential`
returned no result (unknown determinantModule in that index). Indexed grep
`kernelNormalizedDeterminantMap|kernelTwoTermDeterminant|two_term_kernel_normalization`
returned zero hits. Direct project grep found the parent theorem's inline encoding,
whose downstream position is exactly the first return defect; it is no longer imported.
The searches for the new independent encoding are detailed below and recorded verbatim
in its `mathlib_searches`.

Edge cases checked: identity maps; zero modules and empty top wedges; varying local
rank; characteristic two; and the zero ring. No nonzero, rank, free, characteristic or
splitting hypothesis was added. The coefficient universe u and module universe v are
independent, and every variable and universe is bound explicitly with `autoImplicit false`.
In the rank-zero kernel case δ contracts to the identity on det(0)=R, so its scalar is 1,
which excludes the formerly possible arbitrary rescaling of Γ and δ.

No statement correction and no disputed mathematical assertion are needed.

## New nodes

`def-trf-two-term-determinant-encoding` owns the six concrete arrow-category helper
notions in `Sheaf.SecTraceFormula.TwoTermDeterminantEncoding`. Its statement follows
Stacks Tag 0FJI and cites the existing abstract cochain, determinant-module and tensor
nodes. It has no theorem and no `sorry`. The item cites it in `stmt_deps`.

The direct DAG/project search found no independent definition-node owner of the
parent's `Module.TwoTermComplex`/`TwoTermMap` helpers. Importing their owner would close
the cycle identified by the return. Instead of duplicating either structure, the new
module reuses Mathlib's `Arrow (ModuleCat R)` and its morphisms and defines only the
specialized cohomology/kernel/determinant data on them. It imports determinant definitions,
not the parent theorem, exact-sequence theorem, or kernel-normalization theorem.
The parent's module is unchanged; stage 3 can translate its existing inline representation
to an arrow via `Arrow.mk`/`Arrow.homMk` without a proof or import from that parent.

New searches: `msearch.py leansearch` with "Two term cochain complex as an arrow of modules
with commuting square morphisms kernel differential determinant line" returned eight
hits, including `HomologicalComplex.Hom.sqFrom`, `sqTo`, `CochainComplex.mkHom`, `of`, and
`ofHom`; none gives the kernel determinant data. `msearch.py loogle
"CategoryTheory.Arrow, ModuleCat"` returned ten group-cohomology arrow isomorphisms,
confirming the general Arrow interface, which was then read and used directly.
`msearch.py grep "TwoTermComplex|twoTermDeterminant|kernelDifferential"` returned no
indexed hit. Direct `rg` in `dag/nodes`, `lean/WeilConjectures`, `lean/Sheaf` and
Mathlib's homological-algebra sources, plus `blueprint_refs.py search two-term`, found
the parent inline encoding and scheme/derived two-term determinant interfaces, but no
independent module for these kernel data. The raw msearch responses are in the new node.

## Return repairs

1. H2/H3 import cycle: removed the import of
   `Sheaf.SecTraceFormula.SurjectiveTwoTermDeterminantCalculus` and every reference to its
   declarations. Added the independent definition node and module above, cited it in
   `stmt_deps`, and used Mathlib arrows directly. Neither delivered module imports the parent.
2. H3 canonical Γ and δ: replaced `IsKernelNormalizedDeterminantMap a T` with a common
   pair of canonical γ witnesses plus Γ's pure-tensor formula and δ's exterior-map
   contraction formula. Spanning and the inverse triangle remain assertions about
   exactly these pinned objects. This fixes both missing clauses without changing the node.

## Second reading by Q73

Read the repaired files again against the unchanged item and the Stacks triangle.
`Arrow.left/right/hom` encode exactly P^-1/P^0/d_P; `Arrow.w` has the required chain-map
orientation. The two representative cokernel clauses are injectivity and surjectivity
on H^0, and the kernel restriction is H^-1, so no hidden quasi-isomorphism hypothesis
is lost. Both split sections and both finite-projective kernel conclusions are retained.

The earlier report's claim that a predicate on T also constrained the separately
quantified Γ and δ was incorrect. The repaired predicate explicitly constrains Γ by
γzero tensor the inverse dual of γneg, and δ by the exterior differential. Its two
γ witnesses are shared by the exact-sequence and assembly clauses. The contraction
reduces on a pure tensor to λ(nneg) • nzero, as the source requires. The two new formulas
exclude scaling Γ by a unit and compensating in δ. Ordinary tensor symmetry introduces
no sign. The generator and inverse conclusions refer to those same canonical objects.

The new node has exactly the six helper definitions in its declaration record, each
with a source/blueprint docstring and real data. Its Arrow encoding is general in u,v.
Its imports and the item imports were read to ensure neither reaches the parent
calculus theorem. The item's prose, proof, proof dependencies, source and other fields
are unchanged; the only non-lean field change is the authorized new stmt_deps entry.

## Validation

The server compiled both delivered modules cleanly with `scompile.py`. The final
project import-closure check visited 63 modules and found no path to the parent
`SurjectiveTwoTermDeterminantCalculus`. The first repaired-packet dry run requested
the current schema's `import_flags` key on the new definition node; it is supplied
as the empty list. Only `lean` and the authorized added `stmt_deps` entry change
on the item. Lean declaration signatures match their JSON records verbatim, and
all Lean lines satisfy the 100-character limit.
