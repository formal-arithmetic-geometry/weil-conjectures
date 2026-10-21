## Worker report

The module `Sheaf.CategoryTheory.DerivedCategory.DegreeZeroAbelianCriterion` states
`DerivedCategory.degreeZero_abelian_criterion`, with one `sorry` and no definitions.
The node is unchanged except for `lean`. Source read: main-20261015,
`sk-lem-int-integral-heart-triangulated.proof.md`, paragraph (2); the node's seven-step
proof is included in the theorem docstring. This is the extracted abstract criterion,
not the source's separate boundedness or essential-smallness assertions.

Hypothesis and clause correspondence:

- The abelian category A is `(A : Type u) [Category.{v} A] [Abelian A]`.
  `[HasDerivedCategory.{w} A]` provides the chosen morphism-size universe for the
  ordinary unbounded `DerivedCategory A`; u, v and w are independent and explicit.
- T is `ObjectProperty (DerivedCategory A)` with `[T.IsTriangulated]` for zero,
  shift and triangle closure, and `[T.IsClosedUnderIsomorphisms]` for strict fullness.
- The hypothesis about every K in T and every integer q is exactly `hcohomology`:
  `T K → T ((singleFunctor A 0).obj ((homologyFunctor A q).obj K))`.
- B is directly Mathlib's `T.inverseImage (singleFunctor A 0)`, hence B(M) means
  precisely T(S(M)). Its full category is this property's `FullSubcategory`.
  There is no duplicate definition of the category or its membership property.
- The canonical restriction S:B→T is `T.lift (B.ι ⋙ singleFunctor A 0)
  (fun M => M.property)`. The first two conjuncts are its `Full` and `Faithful`.
- The essential-image assertion quantifies over every `K : T.FullSubcategory`:
  an M in B and an ambient isomorphism S(M)≅K exist if and only if
  `∀ q : ℤ, q ≠ 0 → IsZero ((homologyFunctor A q).obj K.obj)`.
  Since T is full, ambient isomorphisms between its objects are exactly those in T.
- For every f in B, D and both remaining arrows g,h are arbitrary and the premise
  is exactly that `Triangle.mk (S.map f.hom) g h` is distinguished. Thus this covers
  every ambient cone triangle, rather than selecting one cone construction.
- The kernel and cokernel isomorphisms are `eK : kernel f.hom ≅ H⁻¹(D)` and
  `eC : cokernel f.hom ≅ H⁰(D)`. The equations fix their compatibility with the
  canonical boundary `HomologySequence.δ ... (-1) 0` and with `H⁰(g)`, using
  `singleFunctorCompHomologyFunctorIso A 0` to identify H⁰(S(M)),H⁰(S(N)) with M,N.
  These are the universal-property identifications, not merely unrelated object
  isomorphisms. The next two conjuncts place these ambient kernel and cokernel in B.
- B contains zero via `ContainsZero`. `IsClosedUnderFiniteProducts` says every
  ambient finite product of B-objects remains in B. In the ambient abelian category
  finite products are finite biproducts; their universal properties restrict to B.
  This includes the empty biproduct. This uses the existing full-subcategory API.
- `IsClosedUnderKernels` and `IsClosedUnderCokernels` quantify over all ambient
  kernel/cokernel choices for morphisms between B-objects, including all isomorphic
  choices, as required by the node and its proof.
- `∃ hB : Abelian B.FullSubcategory` asserts abelianness, with
  `hB.toPreadditive = Preadditive.fullSubcategory B` explicitly fixing the inherited
  addition. The following `PreservesLimit (parallelPair f 0) B.ι` and
  `PreservesColimit (parallelPair f 0) B.ι` say that its kernels and cokernels are
  the ambient ones. Full faithfulness of the inclusion reflects these universal
  properties as well, so this is the ambient-kernel/cokernel abelian structure.
- The final `IsClosedUnderExtensions` is precisely Mathlib's quantification over
  ambient `ShortComplex.ShortExact` sequences with both ends in B and conclusion
  that the middle is in B.
- No boundedness condition or t-structure on T is a binder. The proof-only import
  of the ambient derived-category t-structure supplies the concentration lemma,
  not any extra hypothesis on T.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`, Mathlib.CategoryTheory.Abelian.Basic.
- `def-weil-abstract-derived-category`: `HasDerivedCategory`, `DerivedCategory`,
  `DerivedCategory.singleFunctor`, Mathlib.Algebra.Homology.DerivedCategory.Basic;
  `DerivedCategory.homologyFunctor`, Mathlib.Algebra.Homology.DerivedCategory.HomologySequence.
- `def-weil-triangulated-subcategory`: `CategoryTheory.ObjectProperty.IsTriangulated`,
  Mathlib.CategoryTheory.Triangulated.Subcategory. Strict fullness uses the separate
  existing `ObjectProperty.IsClosedUnderIsomorphisms` class.
- `def-weil-pbc-exact-sequence`: `CategoryTheory.ComposableArrows.Exact`,
  Mathlib.Algebra.Homology.ExactSequence; extension closure's `ShortComplex.ShortExact`
  is Mathlib.Algebra.Homology.ShortComplex.ShortExact, available through Extensions.
- `lem-weil-pbc-derived-single-fully-faithful`: the Full/Faithful instances for
  `DerivedCategory.singleFunctor`, Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful.
  That module also provides the canonical `singleFunctorCompHomologyFunctorIso`.
- `lem-sf-derived-concentrated-single`:
  `DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE`,
  Mathlib.Algebra.Homology.DerivedCategory.TStructure (proof-only import).
- `def-weil-triangulated-category`: `CategoryTheory.Pretriangulated`,
  Mathlib.CategoryTheory.Triangulated.Pretriangulated, through Subcategory.
- `lem-sf-derived-homology-long-exact`: `DerivedCategory.HomologySequence.δ`,
  `exact₁`, `exact₂`, `exact₃`, Mathlib.Algebra.Homology.DerivedCategory.HomologySequence.
- `lem-weil-pbc-complex-ses-triangle`: `DerivedCategory.triangleOfSESδ`,
  `triangleOfSES`, `triangleOfSES_distinguished`,
  Mathlib.Algebra.Homology.DerivedCategory.ShortExact (proof-only import).
- `lem-weil-pbc-abelian-full-subcategory-exact`: the Abelian full-subcategory instance,
  Mathlib.CategoryTheory.Abelian.Subcategory, and `ObjectProperty.preservesKernels_ι`,
  `ObjectProperty.preservesCokernels_ι` in Mathlib.CategoryTheory.ObjectProperty.Kernels.

Edge cases checked before writing: T=0 gives the zero category; T=D(A) gives A;
f=id has zero kernel and cokernel; f=0 has kernel M and cokernel N, agreeing with
H⁻¹ and H⁰ of the split cone; multiplication by 2 on Z gives H⁻¹=0 and H⁰=Z/2,
confirming the cohomological indices and orientation. Empty finite biproducts are
included. Arbitrary unbounded K with cohomology concentrated in degree zero are
included, and zero membership is never assumed for an empty subcategory (triangulation
already requires zero). Universal quantification over D,g,h retains dependence on
all cone choices. No suspicious statement or dependency interface was found.

Searches (2026-10-21):

- `msearch.py ... leanfinder`: “A cohomology stable strictly full triangulated
  subcategory of an abelian derived category has an abelian degree zero subcategory
  closed under kernels cokernels and extensions”. Eight results, including
  `DerivedCategory.TStructure.t`, `IsGE`, `IsLE` and `hasExt_of_hasDerivedCategory`;
  none is the criterion.
- `msearch.py ... loogle '"ObjectProperty", "Abelian"'`: two results, the Serre-class
  localization theorem and the Abelian full-subcategory instance. The latter is
  already the proof dependency and assumes the closure conditions this item deduces.
- `msearch.py ... grep 'IsTriangulated.*(homology|singleFunctor)|(homology|singleFunctor).*IsTriangulated'`:
  zero results.
- `rg -n 'degreeZero|degree_zero|cohomology.*[Cc]los|IsTriangulated.*homology|derivedDegreeZero'`
  on both `lean/WeilConjectures` and `lean/Sheaf`: unrelated degree-zero localization,
  geometric cohomology and coproduct-closure results; no abstract criterion.
- `grep -rn 'lem-sfb-derived-degree-zero-abelian-criterion' lean/WeilConjectures`:
  no result. Mathlib source inspection found and reused `ObjectProperty.inverseImage`,
  `lift`, `FullSubcategory`, kernel/cokernel closure, finite-product closure and
  extension closure; none needs another definition node.

Validation: the prescribed `scompile.py` compiled both sandbox and library module
cleanly (first pass: 5.5 s and 9.5 s); final revised signature recompiled cleanly in 8.4 s and 6.7 s.
Every universe and variable is explicitly bound. No local notation, local instance,
let binder, hidden data or added theorem is used.

## Second reading by Q09

I reread the full node and complete Lean signature in this worker session. The brief
forbids starting agents; the maintainer supplies the independent delivery review.
The correspondence above records this worker's own second reading, not a claimed
independent review.

I checked both directions of the essential-image iff, all degrees q≠0, and arbitrary
cone arrows with first arrow exactly S(f). The kernel equation runs from ker(f) through
eK and the boundary to M; the cokernel equation runs from N through H⁰(g) and agrees
with π followed by eC. This fixes the canonical meaning and corrects no node text.
The abelian witness's addition is explicitly equated to `Preadditive.fullSubcategory B`
to avoid any ambiguity from typeclass inference under the existential binder.
Finite products are the ambient finite biproducts because A is abelian; all ambient
choices are covered by the closure predicates. The last predicate exactly matches
ambient extension closure, including nonsplit sequences. No clause was dropped,
no new hypothesis was added, and no dependency repair or statement correction is needed.
