## Worker report

The module `Sheaf.AlgebraicGeometry.LimitTestRepresentableProperty` states
`CategoryTheory.limit_test_representable_property`, with `sorry` as its only proof.
The mathematical node statement and its proof are unchanged. Its `stmt_deps` gains
only the two already landed definition nodes providing the existing general-base
fibred-groupoid and directed-affine object-descent interfaces.

Clause-by-clause correspondence:

- An arbitrary base scheme is `{S : Scheme.{u}}`. The site is `Over S`; no affine,
  Noetherian, quasi-compact or quasi-separated assumption is imposed on S. Scheme
  sizes use u; the two total categories have independent explicit morphism and
  object universes `v₁ w₁ v₂ w₂`, and the statement has `autoImplicit false`.
- The categories and their morphism are `F`, `G`, and `f : BasedFunctor F G`.
  `hF` and `hG : IsFibredInGroupoids ...` express existence of cartesian lifts and
  the cartesian uniqueness property for every arrow, hence groupoid fibres.
- The discrete groupoid h_T is `discreteModuli (yoneda.obj T)`. An object y over T
  is rendered by `t : BasedFunctor (discreteModuli (yoneda.obj T)) G`.
  Fibred 2-Yoneda identifies these functors with fibre objects, retaining all
  isomorphisms. Thus these binders do not require a stack condition or extra data.
- Representability is `hrep : IsRepresentableByAlgebraicSpaces f`.
  `HasSpaceBaseChange f T t Z a` says that the actual 2-fibre product is represented
  by the algebraic space Z, with its specified projection `a` to h_T. It includes
  the equivalence over Sch/S and its comparison with that projection. This avoids
  an arbitrary map standing in for the canonical represented projection.
- Limit preservation **on objects only** is
  `hLimits : FibredGroupoidLimit.ObjectsDescend G`, not `IsLimitPreserving G`.
  The definition quantifies over `I : Type u`, `[Preorder I]`, directedness and
  nonemptiness, affine diagrams in `Over S`, and actual limiting cones. It asks
  for an arrow over a projection from the limit object to a stage object; since
  G is fibred in groupoids, this is exactly an isomorphism with the pullback.
  The affine limit condition is automatic for such directed affine systems.
- `P : ∀ T Z, (Z.obj.obj ⟶ yoneda.obj T) → Prop` is an arbitrary property of maps
  from algebraic spaces over S to S-schemes. It is not restricted to properties
  defined on scheme charts (which would lose the node's generality).
- `hIso` says P is invariant under a commuting square whose source and target
  maps are isomorphisms. The source isomorphism is between the underlying
  presheaves of the algebraic spaces, equivalently an algebraic-space isomorphism
  because these spaces form a full subcategory of sheaves and sheaves embed fully
  faithfully into presheaves. The target isomorphism is in `Over S`.
- `hBase` is stability under every scheme base change `g : T' ⟶ T`.
  `IsPullback b a' a (yoneda.map g)` specifies exactly the base-changed projection;
  every space representing this pullback satisfies P. It assumes neither
  finiteness nor flatness of g.
- `hLocal` is the stated iff for any open cover of T. A cover is a set `𝒰` of
  opens with `∀ x, ∃ U ∈ 𝒰, x ∈ U`. An arbitrary indexed cover is equivalent to
  its set of image opens; multiplicities have no effect. The S-structure of an
  open is `U.ι ≫ T.hom`. Its restriction of Z is any Z' with projection a' in
  the actual pullback square along `Over.homMk U.ι`. All representatives are
  quantified, an equivalent formulation by `hIso` and existence of algebraic-space
  fibre products. No fppf locality or source locality is assumed.
- `hTest` is precisely the given affine test: `IsAffine T.left`,
  `LocallyOfFinitePresentation T.hom`, every t, and every representing pair Z,a
  satisfying `HasSpaceBaseChange`. Its conclusion is `P T Z a`.
- The conclusion removes only the affine and locally-finite-presentation
  requirements: all T,t and all represented fibres Z,a satisfy `P T Z a`.
  The universal formulation over representatives is equivalent to using any
  chosen W_y by representability and isomorphism invariance.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `def-weil-size-convention` is a recorded convention, not a declaration.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`;
  its full-subcategory definition supplies the presheaves and morphisms used here.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsFibredInGroupoids`, `discreteModuli`, `BasedFunctor`,
  `HasSpaceBaseChange`, `IsRepresentableByAlgebraicSpaces`; the latter records
  actual projection-compatible equivalences, not merely nonempty objects.
- `Sheaf.AlgebraicGeometry.FibredGroupoidLimitPreserving`:
  `CategoryTheory.FibredGroupoidLimit.ObjectsDescend`, together with its real
  `Object` and `Lift` definitions. The stronger full limit-preservation predicate
  is deliberately not assumed.

The latter two modules belong to the landed nodes
`def-sfb-stable-pointed-moduli-groupoids` and
`def-sfb-fibred-groupoid-limit-preserving`, added to `stmt_deps`.
Recorded proof-dependency imports are included as ordinary imports:
`AlgebraicSpaceFibreProductsEtaleCovers`, `Mathlib.AlgebraicGeometry.OpenImmersion`,
`Mathlib.CategoryTheory.Limits.HasLimits`, `Mathlib.AlgebraicGeometry.AffineScheme`,
`Mathlib.AlgebraicGeometry.GammaSpecAdjunction`, and
`Mathlib.AlgebraicGeometry.Morphisms.Affine`. The existing finite-presentation
and algebraic-space statement imports also cover their proof-dependency entries.
The proof docstring follows all six DAG steps, including the explicit small
finite-generator/finite-relation presentation and the empty target case.

Edge cases checked before writing:

- Empty T: the empty set of opens is a cover; the right side of `hLocal` is
  vacuous, forcing exactly the required assertion for every map to empty T.
- Empty directed indices are excluded exactly as in the node. Singleton diagrams
  and constant objects are included. The index size is u, the scheme ring size,
  rather than an unrelated universe that could miss the finite-presentation
  approximation used in the proof.
- Empty source spaces and the zero ring cause no exceptions in P or its laws.
- The base S may be empty or non-quasi-separated; only affine neighbourhoods
  of images are used in the proof, never affine intersections or a finite cover.
- Automorphisms of G-objects are retained by based functors and the actual
  fibre-product equivalences. There are no set-of-isomorphism-class replacements.
- Neither F's limit preservation, arrow descent for G, nor any sheaf/stack
  condition on F or G occurs among the hypotheses.

Searches for an existing statement:

- `msearch.py`, LeanFinder: “Testing a base change stable Zariski local property
  of a representable morphism of fibred groupoids on finite presentation affine
  schemes”. Eight hits, including affine-target base-change stability and
  `locallyOfFinitePresentation_isStableUnderBaseChange`; no matching theorem.
- `msearch.py`, Loogle: `"relativelyRepresentable", "IsZariskiLocalAtTarget"`.
  Zero hits.
- `msearch.py`, grep: `Fibred|Fibered|LimitPreserving|limitPreserving` in
  `CategoryTheory`. Twenty-five hits in the fibred-category and general limit
  infrastructure; none states this geometric affine-testing criterion.
- `msearch.py`, LeanSearch: “Property of representable morphisms of fibered
  groupoids tested on affine schemes locally of finite presentation”. Eight
  hits: ordinary relative representability, scheme local representability,
  finite-presentation definitions and affine-local morphism properties; no match.
- `rg` in project `lean/Sheaf/AlgebraicGeometry`: fibred groupoids,
  limit-preservation, representability, and property names. Located the reused
  `StablePointedModuliGroupoids` and `FibredGroupoidLimitPreserving` modules.
  `ModuliSpaceTest` is limited to properties on scheme charts, so is not an
  alternative definition for arbitrary P here. No existing criterion found.
- `rg` in project `lean/WeilConjectures`: `limitPreserv|limit_preserv` and the
  exact item id. General categorical limit results only, no item-id match.
- `rg` in project Sheaf, upstream WeilConjectures and Mathlib for
  `IsLimitTestRepresentable|limit_test_representable|finitePresentation_affine_tests`:
  zero hits.
- Read Stacks `criteria.tex`, Tag 07WI and its proof directly. Its proof uses
  exactly object descent, arbitrary base change and Zariski locality. The stronger
  fppf-local assumption in the original lemma is unnecessary here, as the node's
  accepted stage-1 review already observes. No statement correction is needed.

Validation: `scompile.py` compiled the theorem without errors or warnings
(sandbox and module checks, each under four seconds). The final delivery wrapper
recompiles the final file and runs the server preflight.

## Second reading by Q19

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
