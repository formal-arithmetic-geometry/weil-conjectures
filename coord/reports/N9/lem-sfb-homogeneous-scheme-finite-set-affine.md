## Worker report

The module `Sheaf.AlgebraicGeometry.HomogeneousSchemeFiniteSetAffine` states
`AlgebraicGeometry.exists_isAffineOpen_of_homogeneous_scheme_finite_set`.
It has one theorem with proof `sorry`, no new definitions, and no node correction.
Only the item's `lean` record changes. All variables are explicitly bound;
`set_option autoImplicit false` makes this compiler-enforced.

Source read: Milne, Algebraic Groups (2017), Appendix B, Theorem B.37,
Step 2, printed p.605 (PDF page 617), together with Steps 1 and 3 and
Remark B.38. Step 2 starts with an existing quotient scheme and obtains
an affine neighbourhood of a finite set of closed points. The node gives
an existing scheme with the fppf orbit morphism; the argument uses that
morphism and the action, not quotient existence or quasi-projectivity.
Its recorded closed-specialization reduction extends the conclusion to
arbitrary finite point sets.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The field k is `{k : Type u} [Field k]`.
- A k-group scheme G is `G : Over (Spec (.of k))` with `[GrpObj G]`.
  `GrpObj` is the dependency's existing Mathlib notion, including multiplication,
  identity, inverse, and all group identities. No commutativity is imposed.
- Separatedness of G is `[IsSeparated G.hom]`. Finite type is exactly the pair
  `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, as its recorded dependency
  specifies; this is not merely locally of finite type.
- The given k-scheme Y is `Y : Over (Spec (.of k))`; its separatedness and finite
  type are `[IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]`.
- The given k-morphism a is `(a : G ⊗ Y ⟶ Y)`. Mathlib's cartesian monoidal
  structure on the slice category has fibre product over Spec k as its tensor.
  Being a slice morphism enforces that a is over k.
- The identity law on every test scheme is `hone`, quantifying over every
  `T : Over (Spec (.of k))` and `y : T ⟶ Y`, with
  `lift (1 : T ⟶ G) y ≫ a = y`. Mathlib's existing Hom monoid structure has
  identity the composite from T to the unit of G.
- The left associativity law is `hmul`, quantifying over every such T and
  `g h : T ⟶ G`, `y : T ⟶ Y`, with
  `lift g (lift h y ≫ a) ≫ a = lift (g * h) y ≫ a`.
  The multiplication is the existing Hom monoid multiplication induced by G.
  These are precisely a(g,a(h,y))=a(gh,y), in the stated order.
- The rational point is `(o : 𝟙_ (Over (Spec (.of k))) ⟶ Y)`.
  The slice unit is Spec k with identity structure morphism, so its morphisms
  to Y are sections of Y.hom. This is the rational-point notion documented by
  the recorded `Scheme.Hom.baseChangeFieldPoint` in DensePoints, using a slice
  morphism to express the section equation structurally. No new notion is defined.
- The orbit map is `(q : G ⟶ Y)` with
  `hq : q = lift (𝟙 G) (toUnit G ≫ o) ≫ a`.
  This equality fixes q to g ↦ a(g,o); q is just a name for that canonical
  composite, not an independently chosen cover or an additional hypothesis.
  Every input action and rational point has exactly this orbit map.
- Flat, surjective, and locally finitely presented are respectively
  `[Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]`.
  These properties concern the underlying scheme morphism of the same q.
- Every finite subset of the underlying point set is `(E : Set Y.left)` with
  `(hE : E.Finite)`. It need not consist of closed or rational points.
- The conclusion `∃ U : Y.left.Opens, IsAffineOpen U ∧ E ⊆ (U : Set Y.left)`
  gives one affine open subscheme of this Y containing all of E. IsAffineOpen
  means the induced open subscheme is affine. The conclusion does not introduce
  another scheme or assert quotient existence.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`,
  Mathlib.CategoryTheory.Monoidal.Grp. Its group-object signature and docstring
  were read, together with Mathlib.CategoryTheory.Monoidal.Cartesian.Mon's
  `MonObj.Hom.monoid` and Cartesian.Grp's `GrpObj.Hom.group`.
  The scheme specialization was read in
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs. The existing slice
  tensor/unit structure is Mathlib.AlgebraicGeometry.Pullbacks.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsSeparated`,
  Mathlib.AlgebraicGeometry.Morphisms.Separated, publicly available through
  the recorded Mathlib.AlgebraicGeometry.Morphisms.Proper. The node needs
  separatedness only, so no properness assumption appears.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType, and
  `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  Mathlib.AlgebraicGeometry.Scheme. Affine opens use the existing
  `AlgebraicGeometry.IsAffineOpen`, Mathlib.AlgebraicGeometry.AffineScheme.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat`,
  Mathlib.AlgebraicGeometry.Morphisms.Flat; its docstring identifies it with
  stalkwise flatness, matching the dependency.
- `def-sbc-locally-finite-presentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`,
  Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation.
- `def-pc-rational-point`:
  `AlgebraicGeometry.Scheme.Hom.baseChangeFieldPoint`,
  WeilConjectures.AlgebraicGeometry.DensePoints. Read the full signature and
  docstring: rational points are sections; its scalar-extension operation is
  not needed in this statement. We use the already available slice-category
  representation of exactly those sections, not a private replacement.

Public imports supply the statement's recorded interfaces. Plain imports supply
all recorded, stated proof dependencies: finite-type/Jacobson/Noetherian inputs,
quasi-separatedness, the upstream generic-point affine-neighbourhood theorem,
FiniteClosedSetRationalLifts, PullbackCarrier, UniversallyOpen, ClosedPointField,
Over.DescentDatum, DescentNormAffineShrinking, InvariantOpenImagePullback,
fpqc coverings, and FpqcAffineDescent. The fibre product interface is already
publicly available through scheme pullbacks. The proof dependency
`lem-sfb-finite-scalar-extension-generic-points` has no recorded declaration or
upstream closed audit to import; it remains named in the proof docstring.
The generic-point dependency has no lean field but its closed upstream audit
records `AlgebraicGeometry.exists_isAffineOpen_mem_of_subset_genericPoints`
in WeilConjectures.Mathlib.AlgebraicGeometry.Properties, which is imported.

Edge cases checked before writing:

- E empty is allowed; the empty open is affine (Spec of the zero ring).
- Nonclosed points are included; closed specializations exist in finite-type
  schemes over a field, and opens containing them contain their generalizations.
- Finite and imperfect fields are included; the argument passes to finite
  extensions without requiring separability or infinitely many rational points.
- G need not be reduced, connected, commutative, smooth, affine, or quasi-projective.
- Y need not be assumed quasi-projective; it is the given scheme throughout.
- No redundant Nonempty hypothesis is added: the group has an identity and o
  already gives a point of Y. An empty Y cannot satisfy that existing hypothesis.
- The base field, schemes, and test schemes share arbitrary explicit universe u;
  test schemes include G, Y, and their finite fibre products, so the action
  identities are the usual scheme identities by Yoneda. This is the standard
  group-scheme slice interface, without a smaller independent test universe.

Searches for an existing statement (all through the prescribed tools):

- msearch.py leanfinder: "Every finite subset of a homogeneous scheme with a
  faithfully flat orbit map from an algebraic group lies in an affine open".
  Eight hits: projective standard-open covers, affine cover pieces, and
  affine-transition-limit cover existence. None is this simultaneous
  finite-subset homogeneous-scheme theorem.
- msearch.py loogle: `"GrpObj", "IsAffineOpen"`: zero hits.
- msearch.py grep: `homogeneous|finite.*affine.*neigh`, AlgebraicGeometry:
  25 hits, mainly graded/projective-spectrum homogeneous localization;
  no matching homogeneous-space affine-neighbourhood result.
- msearch.py leansearch: "Every finite collection of points of a homogeneous
  scheme under an algebraic group lies in a single affine open neighbourhood".
  Eight hits, all affine covers/affine opens or the neighbourhood of a single
  point (`exists_isAffineOpen_mem_and_subset`), not the stated finite-set result.
- rg of WeilConjectures and Sheaf for `homogeneous|finite.*affine.*neigh|IsAffineOpen.*Finite`:
  unrelated graded-algebra and projective-coordinate material, generic local
  neighbourhoods, and ample-line-bundle neighbourhood results; no exact statement.
- grep for this node id in WeilConjectures: no hit.
- rg of dag/lean_names_upstream.json and both project roots for the proposed
  declaration name: no existing declaration. Other FiniteSetAffine modules
  concern ample families and are not this hypothesis or result.

Validation: the prescribed scompile.py compiled this module in sandbox and
library module modes cleanly. The complete seven-step natural-language proof
from the node is retained in the theorem docstring, with its DAG dependencies.
No STATEMENT-DISPUTED fault or statement correction was needed.

## Second reading by N9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
