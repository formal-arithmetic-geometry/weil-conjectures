## Worker report

The module `Sheaf.CategoryTheory.DerivedCategory.BifunctorHomHomotopyExact` states
`CochainComplex.bifunctorHomHomotopyFunctor_leftOp_exact`, with its proof left `sorry`.
It uses the existing signed Hom construction and quotient functor. No new notion,
dependency repair, or statement correction is necessary. The node is changed only in `lean`.

Clause-by-clause correspondence:

- Abelian categories A, B, C: the three independent object universes `u₁`, `u₂`, `u₃`,
  category instances with independent morphism universes `v₁`, `v₂`, `v₃`, and
  `[Abelian A] [Abelian B] [Abelian C]`.
- Countable products in C: `[HasCountableProducts C]`.
- The chosen D(C), with its chosen morphism universe: `[HasDerivedCategory.{w} C]`.
  No derived category of A or B is required.
- The contravariant/covariant bifunctor: `(H : Aᵒᵖ ⥤ B ⥤ C)`.
- Separate additivity: `[H.Additive]` and `[∀ X : Aᵒᵖ, (H.obj X).Additive]`.
- An arbitrary complex I: `(I : CochainComplex B ℤ)`, with no injectivity,
  boundedness, or acyclicity-preservation hypothesis.
- The degree-n product and signed differential: the functor in the conclusion uses
  the existing `CochainComplex.bifunctorHomObj H K I`. Its degree-n object is the
  categorical product over `HomComplex.Triplet n`, namely pairs `(p,q)` with `p+n=q`.
  This countable index is equivalent to the integers, via `p ↦ (p,p+n)`.
  `bifunctorHomObj_d_π` specifies precisely `p.negOnePow` times the difference of
  postcomposition by `d_I` and precomposition by `d_K`. The order in Lean is
  projection followed by the relevant map, as the node's prose requires.
- Precomposition and descent to homotopy classes: the existing
  `CochainComplex.bifunctorHomHomotopyFunctor H I` is the quotient lift of
  `bifunctorHomComplexFunctor`, whose map is `bifunctorHomMapLeft`, followed by the
  target homotopy quotient and `DerivedCategory.Qh`. The two existing `_obj` and
  `_map` lemmas give these formulas exactly. The functor is stored covariantly
  with opposite target; `.leftOp` has exactly the node's domain K(A)ᵒᵖ and target D(C).
  The canonical `DerivedCategory.quotientCompQhIso` identifies the displayed
  quotient-then-localization object formula with `DerivedCategory.Q` of the signed
  Hom complex. It changes neither the chosen complex nor the induced map.
- Coherent commutation with every integer shift: the existential
  `∃ (_ : (...).leftOp.CommShift ℤ), ...`. This is Mathlib's structure of natural
  shift isomorphisms with its zero and addition laws, not only a degree-one comparison.
- Triangulated for that same shift structure: the dependent body of the existential
  is `(...).leftOp.IsTriangulated`. The existentially bound class is used in this
  proposition. `Functor.mapTriangle` uses precisely its degree-one shift comparison
  in the third arrow, so preservation is for all three actual triangle maps.
- Opposite source triangulation: `open CategoryTheory.Pretriangulated.Opposite`
  activates Mathlib's opposite triangulation, imported from
  `Mathlib.CategoryTheory.Triangulated.Opposite.Triangulated`. Its shift by `m` is
  the underlying shift by `-m`. Thus the comparison at `m=-r` identifies the
  localized signed Hom of `K[r]` with that of K shifted by `-r`. The proof docstring
  gives the actual chain comparison by reindexing and the sign
  `(-1)^(r*p+r*(r+1)/2)`, including its zero and addition coherence.
- No K-injectivity or acyclicity-preservation condition: none occurs among the binders.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian` in
  `Mathlib.CategoryTheory.Abelian.Basic`; its finite products, kernels, cokernels,
  normal mono/epi definition supplies the node's abelian categories.
- `def-weil-abstract-derived-category`: `HasDerivedCategory`, `DerivedCategory`,
  `DerivedCategory.Q`, `DerivedCategory.Qh`, and `quotientCompQhIso` in
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`. These are publicly imported by
  the upstream BifunctorHom module.
- `def-weil-triangulated-category`: `CategoryTheory.Pretriangulated`,
  `CategoryTheory.IsTriangulated`, and `CategoryTheory.Functor.IsTriangulated` in
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, `.Triangulated`, and `.Functor`.
  `Functor.CommShift` in `Mathlib.CategoryTheory.Shift.CommShift` carries all integer
  isomorphisms and their coherence laws. These are available through the public imports.
- Existing construction used, without duplicating it:
  `CochainComplex.bifunctorHomObj`, `bifunctorHomπ`, `bifunctorHomObj_d_π`,
  `bifunctorHomMapLeft`, and `bifunctorHomMapLeftHomotopy` in
  `WeilConjectures.Algebra.Homology.BifunctorHomComplex`;
  `bifunctorHomComplexFunctor`, `bifunctorHomHomotopyFunctor`, and its `_obj`/`_map`
  lemmas in `WeilConjectures.CategoryTheory.DerivedCategory.BifunctorHom`.
- Proof dependency `lem-pur-homotopy-category-triangulated`: the homotopy-category
  triangulated instance in `Mathlib.Algebra.Homology.HomotopyCategory.Triangulated`
  and the exactness instance for `DerivedCategory.Qh` in the derived-category Basic
  module; these already enter through the upstream public import.
- Proof dependency `lem-sf-signed-bifunctor-cone-iso` currently has no Lean record;
  hence there is no module to import yet. It is needed only for the postponed proof,
  not to type this statement. Its use and the connecting-arrow calculation are
  included in the proof docstring for stage 3.

Source read: `literature/stacks-project/sites-cohomology.tex`,
`lemma-RHom-triangulated` (Tag 08JC), which uses termwise-split sequences and omits
its details. The five-step arbitrary-bifunctor calculation is the node's explicit
agent-written generalization. Also read the exact upstream construction and
Mathlib's reversed-triangle and opposite-shift definitions. The construction has
real data and is already homotopy invariant; this delivery adds no definition.

Edge cases checked before writing: zero complexes and the zero bifunctor (the
product object is zero up to its canonical isomorphism and the same formula applies);
unbounded I and K (only integer-indexed products are used); r=0, r=1, and r=-1
in the shift signs; arbitrary negative integers in b(r)=r(r+1)/2 (always integral);
characteristic two (sign changes become identities, with the same cancellation);
independent category and derived-morphism universes. No exactness of products is
used: the cone comparison involves finite split summands. No issue or disputed
statement was found.

Searches for an existing statement:

- `msearch.py ... leanfinder`: "The signed Hom complex of a separately additive
  bifunctor gives a triangulated functor from the opposite homotopy category to
  the derived category". Eight results: generic homotopy-category exactness,
  localization exactness, derived exact functors, and cohomology; no theorem for
  the signed bifunctor Hom construction.
- `msearch.py ... loogle '"bifunctorHom"'`: twelve results for covariant
  `mapBifunctorHomologicalComplex` constructions; none is this exactness theorem.
- `msearch.py ... grep
  'bifunctorHom.*(CommShift|Triangulated)|homotopy.*[Tt]riangulated'`: eleven hits
  for generic homotopy and derived triangulation modules; no match.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `bifunctorHomHomotopy|bifunctorHom.*(CommShift|Triangulated)|bifunctor-homotopy-exact`
  found the upstream functor and its use in derived Hom, with no exactness theorem.
  The similarly named homotopy shift in `KFlatFixedTensorTriangulated` is a
  covariant tensor construction. Searching the exact item id upstream found none.
- `rg` in `dag/lean_names_upstream.json` for `bifunctorHom` found no additional entry.
  The recorded CompactObject example module is withdrawn; its node now records the
  upstream module, which was read for the current header and documentation conventions.

Validation: all probes and the delivered module use module mode and were compiled
only with the prescribed `scompile.py`. The final module compiled cleanly in both
sandbox and library contexts. It has one named theorem with `sorry`, no other proof
or definition, no auto-implicit parameters, and no line longer than 100 characters.

Additional search: `msearch.py ... leansearch` with "A separately additive
contravariant bifunctor Hom complex is an exact functor from the opposite homotopy
category to the derived category" returned eight generic declarations:
`HomologicalComplex.opFunctor_additive`, `Functor.mapHomotopyCategory`,
`DerivedCategory.Qh`, `HomologicalComplex.unopFunctor`,
`Functor.rightDerivedToHomotopyCategory`, `Functor.map₂HomologicalComplex`,
`HomologicalComplex.opFunctor`, and `Functor.leftDerivedToHomotopyCategory`.
None states this signed-bifunctor exactness result.

## Second reading by Q08

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
