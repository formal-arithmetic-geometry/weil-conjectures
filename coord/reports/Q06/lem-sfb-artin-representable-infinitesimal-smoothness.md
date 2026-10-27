## Worker report

The delivery states `CategoryTheory.artin_representable_infinitesimal_smoothness` in
`Sheaf.AlgebraicGeometry.ArtinRepresentableInfinitesimalSmoothness`, with its sole theorem
proof `sorry`. It adds a general-base limit-preservation definition in
`Sheaf.AlgebraicGeometry.FibredGroupoidLimitPreserving`. Both files have compiled separately
using scompile.py, including module-mode library compilation; no errors or warnings.

Read the item, every statement dependency and its Lean record or Mathlib match, and the
full signatures/docstrings used. Checked the source in artin.tex: Tag 07XL's definition and
following explanation, Tag 07XX and its proof, and equation-smooth. The node is a correct
specialization of 07XX using 07XN. No statement correction or disputed statement.

Hypothesis and clause correspondence:

- A commutative Noetherian ring R: `R : CommRingCat.{u}` and `[IsNoetherianRing R]`.
  The base S is literally `Spec R`, not an arbitrary replacement base.
- Size convention: explicit universes `u v w`; schemes, rings and test algebras are in u,
  while the total category has independent morphism/object universes v and w. The directed
  index type is `Type u`, with a preorder, directedness and nonemptiness.
- A category fibred in groupoids: `F : BasedCategory.{v,w} (Over (Spec R))` with
  `hF : IsFibredInGroupoids F`. This is exactly existence of base lifts and the strong
  cartesian property of every arrow; it retains all fibre automorphisms.
- Limit preservation: `hLimits : FibredGroupoidLimit.IsLimitPreserving F` is the
  conjunction of object descent, arrow descent compatible with the given pullbacks,
  and eventual equality of arrows. These are essential surjectivity, fullness and
  faithfulness of the natural 2-colimit comparison, not just object descent.
- U is finite type: `U : Over (Spec R)` with `[LocallyOfFiniteType U.hom]` and
  `[QuasiCompact U.hom]`, following the dependency record's conjunction convention.
- The object x over U and h_U: `x : BasedFunctor (discreteModuli (yoneda.obj U)) F`.
  The source discrete fibred groupoid is the existing representable groupoid h_U.
  Its value at id_U is the node's x; its value at any a is its pullback. This is the
  total-category Yoneda encoding of an object, without choosing a cleavage.
- Representability: `hrep : IsRepresentableByAlgebraicSpaces x` uses the existing
  definition with an algebraic-space model of every scheme 2-base change and the
  actual projection comparison. No algebraicity or stack condition on F is assumed.
- Every finite type field l over R: `K : Type u`, `[Field K]`, `[Algebra R K]` and
  `[Algebra.FiniteType R K]`. The spectrum and every induced map use Mathlib `algSpec R`,
  so they are actual R-schemes and actual R-morphisms.
- Every alpha: the binder `alpha : (algSpec R).obj (op (CommAlgCat.of R K)) ⟶ U`.
- Every surjection of Artinian local R-algebras: B', B with their four ring/local/Artinian
  instances, R-algebra structures, `q : B' →ₐ[R] B`, and `Function.Surjective q`.
  All surjections are included; there is no square-zero or small-extension restriction.
- Residue fields identified with K: `rho : B →ₐ[R] K`, `Function.Surjective rho`, and
  `RingHom.ker rho.toRingHom = IsLocalRing.maximalIdeal B`. The composite rho.comp q
  is a surjection B' -> K. Its kernel is the unique maximal ideal of B', since K is a
  field; thus it supplies precisely the compatible residue identification for B'.
  Conversely every compatible pair of residue identifications is of this form.
  No embedding of K into either ring, or choice of coefficient field, is assumed.
- Every a restricting to alpha: binder a and
  `(algSpec R).map (CommAlgCat.ofHom rho).op ≫ a = alpha`.
- Every z over B' and every supplied restriction isomorphism: `z : F.obj` and the
  arrow `c : x.obj (CostructuredArrow.mk (yoneda.map a)) ⟶ z`, together with
  `F.p.IsHomLift (Spec q over R) c`. This HomLift also forces z's base to be Spec B'.
  In a fibred groupoid this is exactly the inverse of the specified isomorphism
  z|B ≅ a*x, followed by the cartesian pullback arrow. All such isomorphisms are tested.
- A lift a': the existential a' has domain Spec B' over R. The comma arrow b from the
  h_U-object a to the h_U-object a', with its `IsHomLift (Spec q over R) b`, says exactly
  Spec(q) ≫ a' = a. It is not an arbitrary comparison map.
- An isomorphism extending the supplied one: the arrow d from x(a') to z is over the
  identity of Spec B', hence is invertible by hF. The equality `x.map b ≫ d = c`
  expresses extension of the particular supplied isomorphism. Taking its inverse
  gives precisely the node's z ≅ (a')*x orientation.
- Smoothness for every T,y: `ModuliSpaceTest @Smooth x`. Unfolding the existing predicate
  quantifies over all T and all based maps h_T -> F, provides the algebraic-space
  2-base change with its actual projection, and requires `Smooth` of the composite
  with every representable etale scheme chart. It has exactly the stated scope.
- No stack descent, Rim--Schlessinger, effectivity, or tangent-dimension condition is
  present. None is hidden in BasedCategory, IsFibredInGroupoids, or ModuliSpaceTest.

Declarations reused:

- Mathlib.RingTheory.Noetherian.Defs: `IsNoetherianRing` (all ideals finitely generated).
- Mathlib.AlgebraicGeometry.Scheme: `Scheme`, `Spec`, `Spec.map`.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: `LocallyOfFiniteType`; the same recorded
  dependency also supplies `QuasiCompact`. Finite type means their conjunction.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth` (the recorded smooth predicate).
- Mathlib.AlgebraicGeometry.ResidueField: `Scheme.residueField`, with local residue rings
  represented using `IsLocalRing.maximalIdeal` and the explicit quotient augmentation.
- Mathlib's `Field`, `Algebra.FiniteType`, `IsArtinianRing`, `IsLocalRing`, `AlgHom`,
  `Functor.Fiber`, `Functor.IsHomLift`, and `BasedCategory` are reused directly.
- Mathlib.AlgebraicGeometry.Group.Affine: `algSpec`, the existing spectrum functor from
  commutative R-algebras to schemes over Spec R; no private spectrum-over-base construction.
- Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids: `IsFibredInGroupoids`,
  `discreteModuli`, `IsRepresentableByAlgebraicSpaces`, and its `HasSpaceBaseChange`.
  Its owning definition node is added to stmt_deps.
- Sheaf.AlgebraicGeometry.DmStackMorphismProperties: `ModuliSpaceTest`. This predicate is
  defined for arbitrary based categories, with no DM assumption. Its owning landed
  definition node is added to stmt_deps.
- The new definition's `Object`, `Lift`, `ObjectsDescend`, `ArrowsDescend`,
  `ArrowEqualitiesDescend`, and `IsLimitPreserving` all have actual definitions.

The available proof-dependency modules are plain imports: Mathlib.AlgebraicGeometry.Noetherian,
Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus,
Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties,
Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion, and
WeilConjectures.AlgebraicGeometry.Thickening. Finite-type composition and open immersion
etaleness are supplied by the imported Mathlib interfaces. The other proof-dependency
nodes have no usable declaration yet and are not re-stated or replaced. All seven proof
steps, with their node citations, are in the theorem docstring for stage 3.

Edge cases checked: U empty, F empty, R the zero ring (then no field tests and an empty
scheme base), identity surjections B' -> B, non-small Artinian extensions, unequal
characteristics and mixed characteristic (no coefficient field assumed), nontrivial
fibre automorphisms, arbitrary given deformation isomorphisms, non-affine U, and arbitrary
T,y in the conclusion. Finite type field means finite type as an R-algebra here, exactly
as for Spec K -> Spec R. Directedness excludes only the empty inverse system, as in the
source definition. Preorders, rather than partial orders, allow repeated stages.

Searches actually run using msearch.py: LeanFinder for the full Artinian representable
smoothness criterion returned eight scheme-smoothness hits, none about fibred groupoids;
Loogle `"Fibered", "Smooth"` returned zero hits; Mathlib grep
`(Fibered|Fibred).*(Smooth|LimitPreserv)|(Smooth|LimitPreserv).*(Fibered|Fibred)` returned
zero hits. Searches in WeilConjectures and Sheaf by item id and infinitesimal/limit-preserving
vocabulary found no statement of this theorem. The existing StackInfinitesimalSmoothCriterion
requires an algebraic stack and a different first-order test, so is not an exact match.
For the new notion, LeanSearch, LeanFinder and Mathlib grep were repeated with limit
preservation queries and are recorded verbatim in its mathlib_searches. The search service
hits concern ordinary limits or affine scheme limits, not this predicate. Project grep
finds the existing integer-base ArtinCriterion predicates; they cannot accept arbitrary R.
DAG grep finds inline descriptions in lemma statements, but no definition node for the
arbitrary-base notion. `blueprint_refs.py search 'limit preserving'` returns zero matches.

## New nodes

`def-sfb-fibred-groupoid-limit-preserving` defines directed affine limit preservation for
an arbitrary scheme base, from Stacks Tag 07XL (definition-limit-preserving and its
following explicit explanation), needed in Tag 07XX. Its one module defines the three
real descent predicates and their conjunction, with Mathlib fibre and HomLift helpers.
It cites scheme, universe and fibred-groupoid definition nodes. The project's existing
`AlgebraicGeometry.ArtinCriterion.IsLimitPreserving` is restricted to Spec(ULift Z), and
cannot render the present arbitrary-R hypothesis. The added definition generalizes that
interface without modifying the existing theorem's node or adding its unrelated Artin
hypotheses. There is no new theorem in this definition module and no postponed data.
The ancestor tool reports None; its null ancestor and inherited via chain are preserved
with this item prepended, as required.

## Second reading by Q06

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
