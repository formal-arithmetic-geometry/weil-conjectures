## Worker report

The module `Sheaf.CategoryTheory.BoundedHeartAmplitude` states
`DerivedCategory.bounded_heart_amplitude`, with its only proof `sorry`.
It introduces no definitions or helper nodes, and changes only the item's `lean` field.
The statement is unchanged. There are no disputed clauses or dependency interface faults.

Hypothesis and conclusion correspondence, read against the complete node statement:

- Abelian categories A and B: `(A : Type uA) [Category.{vA} A] [Abelian A]` and the
  corresponding B binders. All six universes are explicitly declared and independent.
- Their derived categories: `[HasDerivedCategory.{wA} A]` and
  `[HasDerivedCategory.{wB} B]` choose the localization sizes and allow `DerivedCategory A`
  and `DerivedCategory B`. These are the recorded localization definitions, not new data.
- Standard cohomology H^i is `DerivedCategory.homologyFunctor A i` or the B version.
  The name is homologyFunctor because it applies uniformly to complex shapes; for the
  cochain shape `.up ℤ` it is exactly H^i. The standard shift convention is built into
  these functors via their `ShiftSequence ℤ` instance: shifting by r changes degree i
  to degree i+r. This is fixed structure, not an additional assumption.
- The exact triangulated functor with shift comparisons is
  `(T : DerivedCategory A ⥤ DerivedCategory B) [T.CommShift ℤ] [T.IsTriangulated]`.
  Mathlib's `CommShift` includes the comparisons and their coherence. `IsTriangulated`
  preserves distinguished triangles and implies additivity, so no separate additivity
  or product-preservation hypothesis is needed.
- The class of objects is `(S : A → Prop)`. Closure under isomorphism is `_hSiso`:
  `∀ (M N : A), (M ≅ N) → S M → S N`. Its inverse covers the converse direction.
  Containing zero is `_hSzero : S (0 : A)`, using Mathlib's `ZeroObject` scope.
- The integers c <= d are `(c d : ℤ) (_hcd : c ≤ d)`.
- The bound on every M in S, placed in degree zero, is `_hHeart`:
  `∀ (M : A), S M → ∀ (i : ℤ), i < c ∨ d < i →
  IsZero ((homologyFunctor B i).obj (T.obj ((singleFunctor A 0).obj M)))`.
  `singleFunctor A 0` is the recorded canonical embedding, not an arbitrary heart object.
- Every pair a <= b is quantified by `(a b : ℤ) (_hab : a ≤ b)`.
- Every K in D(A) is `(K : DerivedCategory A)`; its vanishing outside [a,b] is `_hK`,
  quantified over all integers r, using `r < a ∨ b < r`.
- All its cohomology objects lie in S by `_hKS : ∀ (r : ℤ), S ((homologyFunctor A r).obj K)`;
  this includes degrees outside [a,b], as required by the node, not just the nonzero degrees.
- The conclusion quantifies every integer i outside [a+c,b+d], expressed by
  `i < a + c ∨ b + d < i`, and asserts `IsZero ((homologyFunctor B i).obj (T.obj K))`.
  `IsZero` is categorical vanishing, independent of any choice of underlying elements.
- No completeness, products, preservation of products, enough injectives or boundedness
  condition on the functor itself is present. Only this input K is bounded.

Dependency declarations read and used:

- `def-sp-abelian` is a Mathlib leaf: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`. Its finite-products/kernels/cokernels/normal
  mono/epi definition gives exactly the node's equivalent abelian axioms.
- `def-weil-abstract-derived-category`: `DerivedCategory` and `HasDerivedCategory`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`; also its `singleFunctor`.
- `def-weil-triangulated-category` is a Mathlib leaf:
  `CategoryTheory.Pretriangulated`, `CategoryTheory.IsTriangulated` and
  `CategoryTheory.Functor.IsTriangulated`, in their recorded Mathlib modules.
  The functor interface is imported publicly. The derived categories already carry
  the standard triangulated structures.
- Cohomology is `DerivedCategory.homologyFunctor`,
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`, imported publicly.
- Proof-plan imports: `Sheaf.CategoryTheory.TruncationDescends`
  (`DerivedCategory.truncation_descends`) and the recorded upstream
  `WeilConjectures.CategoryTheory.TruncationTriangle`
  (`DerivedCategory.truncation_triangle`) are plain imports. The latter source was
  retrieved with `scompile.py --source` because the older local upstream lacks it.
  `DerivedCategory.HomologySequence.exact₂` and `CategoryTheory.Functor.shiftIso`
  are supplied by the public homology-sequence import. The five-step docstring follows
  the node's finite truncation induction, including the shift sign i-q and both endpoint
  quasi-isomorphisms. No proof dependency was silently replaced.

Edge cases checked before writing: a=b is a single cohomology degree and gives the interval
[a+c,a+d]; c=d and negative endpoints require no special restriction. A zero or acyclic K
maps to zero because a triangulated functor is additive. A class consisting only of zero
objects likewise only admits acyclic K. The empty class is excluded explicitly by the
node's zero-membership hypothesis. No extension-closure of S is assumed: the finite
filtration uses the individual cohomology objects. Boundary indices a+c and b+d are
included (strict inequalities describe the complement). The shift of an object in degree
zero by -q contributes in degree q, so the image bound is [q+c,q+d]. Independent universes
allow different source and target object, morphism and localization sizes.

Searches for duplication, using the prescribed `msearch.py` with group Q61 and this item:

- `grep` query `[Aa]mplitude|[Hh]eart|[Bb]ounded.*[Ii]nduction` in `Algebra/Homology/DerivedCategory`: 2 hits; Mathlib/Algebra/Homology/DerivedCategory/SingleTriangle.lean, Mathlib/Algebra/Homology/DerivedCategory/Ext/TStructure.lean.
- `loogle` query `"IsTriangulated", "homologyFunctor"`: 0 hits; no matches.
- `leanfinder` query `An exact triangulated functor bounded from c to d on a class of heart objects sends bounded complexes with cohomology in that class from degrees a to b into degrees a+c to b+d`: 8 hits; CategoryTheory.Functor.IsHomological.mk', CategoryTheory.Functor.IsHomological, DerivedCategory.TStructure.t, CategoryTheory.Functor.IsHomological.exact, DerivedCategory.instIsGEObjSingleFunctor, CategoryTheory.Functor.instIsTriangulatedHomologicalKernel, DerivedCategory.instIsLEObjSingleFunctor, CategoryTheory.Functor.mem_homologicalKernel_trW_iff.
- `leansearch` query `Bounds for an exact triangulated functor on heart objects imply bounds on bounded complexes by truncation induction`: unavailable: service unavailable: {"error":"Rate limit exceeded: 60 per 1 minute"}; no negative-match verdict is inferred.

LeanFinder's homological-functor and t-structure hits do not state a class-relative bound
with the four endpoints. Loogle found no combined match. The grep hits concern the heart
and single triangles, not this estimate. Additional direct rg searches in Mathlib,
WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
`bounded_heart_amplitude|cohomology_bound_of_heart|boundedHeartAmplitude` found no duplicate.
Direct searches for the blueprint id in WeilConjectures and lean/Sheaf found none.
The required three search kinds were attempted; LeanSearch reported a service rate limit,
while LeanFinder, Loogle and local source searches completed.

Validation: `scompile.py Q61 lem-pur-bounded-heart-amplitude` compiled both the sandbox
and final library-path form cleanly (1.2 and 1.3 seconds). The first compile exposed a
missing ZeroObject scope for `(0 : A)`; adding `open scoped ZeroObject` fixed it without
changing the mathematical statement. No error or warning remains. The only theorem
has the expected postponed proof.

## Second reading by Q61

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
