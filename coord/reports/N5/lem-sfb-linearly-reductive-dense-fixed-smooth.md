## Worker report

The module `Sheaf.AlgebraicGeometry.LinearlyReductiveDenseFixedSmooth` states
`AlgebraicGeometry.linearlyReductive_dense_fixed_smooth`, with a single `sorry` proof.
It states Milne, Algebraic Groups (2017), Lemma 13.6, printed p.256, in exactly
the node's affine, algebraically closed specialization. I read printed pp.255--257
of the supplied PDF, including Lemmas 13.3--13.6 and Theorem 13.7.
The seven proof steps in the node are rendered in the theorem docstring.

Hypotheses and conclusion, clause by clause:

- Algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`.
- k-group scheme G: `G : Over (Spec (.of k))` and `[GrpObj G]`.
  These are the recorded group-scheme notion and base, with multiplication,
  identity and inverse satisfying the usual diagrams.
- Smooth affine finite-type G: `[Smooth G.hom]`, `[IsAffine G.left]`,
  `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`.
- Algebraic representations, invariance after every algebra extension, simple
  representations, and linear reductivity: `hG : IsLinearlyReductiveGroupScheme G`.
  This existing definition quantifies over `RationalHom G ι` with `[IsMonHom ρ]`
  for all finite index types ι. Choosing a basis covers every finite-dimensional
  vector space V. Its general linear scheme has A-points the invertible matrices,
  equivalently invertible A-linear endomorphisms of V tensor A. The helper
  `IsInvariantRationalSubspace` preserves the A-span of U in A^ι for EVERY
  commutative k-algebra A, not merely k-valued points. Its simple summands are
  invariant, nonzero, and have no nonzero proper invariant subspace. Independence
  and supremum equal to top express their internal direct sum. Finite dimension
  forces only finitely many nonzero independent summands. The empty sum covers
  dimension zero. This has no characteristic-zero restriction.
- Abstract subgroup Γ of G(k): `Γ : Subgroup (points G k)`.
  `open scoped MonObj` activates the existing group structure on these hom types.
- Zariski density in the underlying space of G:
  `hdense : DenseRange fun g : Γ ↦ g.val.left (IsLocalRing.closedPoint k)`.
  A k-point maps the sole point of Spec k to its underlying point of G. Thus
  density is in the scheme's Zariski topology, not a topology on the abstract group.
- Smooth affine finite-type k-scheme X: `X : Over (Spec (.of k))`,
  `[IsAffine X.left] [Smooth X.hom]`, and
  `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom]`.
- Scheme action a: `[action : ModObj G X]`. Its data is an actual morphism
  from the product in the over category (the fibre product over k) to X.
  The fields `one_smul` and `mul_smul` are the unit and associativity diagrams.
  `CategoryTheory.Hom.smul` evaluates this morphism on pairs of A-points, and
  `Hom.mulAction` gives the stated identities after every algebra extension.
- Closed representing subscheme: `F : Over (Spec (.of k))`, `i : F ⟶ X`,
  and `[IsClosedImmersion i.left]`. No extra smoothness, finiteness,
  reducedness, or affineness hypothesis is imposed on F.
- The displayed functor F(A): `hfixed` quantifies over all `A : Type u`
  with `[CommRing A] [Algebra k A]` and all `x : points X A`.
  Its left side `(∃ z : points F A, z ≫ i = x)` is membership in the
  image of F(A) under i. A closed immersion is a monomorphism, so any such
  z is unique; this is exactly representing the indicated subfunctor.
  The right side quantifies over EVERY `g : Γ` and states
  `points.map G (Algebra.ofId k A) g.val • x = x`.
  The canonical map `Algebra.ofId k A : k →ₐ[k] A` and the existing
  `points.map` give precisely g_A, not a separately supplied family of maps.
  All algebras, including nonreduced and zero algebras, occur. The point
  maps and action are already functorial, so image equality on all A is
  equality of the subfunctors.
- Conclusion: `Smooth F.hom`, exactly smoothness over k. No additional conclusion
  (such as equality with the full G-fixed locus) is included.
- Neither G nor X is assumed connected or irreducible. No such Lean instance
  or hypothesis appears.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`.
- `def-weil-algebraic-closure`: Mathlib `IsAlgClosed`,
  `Mathlib.FieldTheory.IsAlgClosed.Basic`; the dependency's match explicitly
  records this algebraically-closed-field notion as well as `AlgebraicClosure`.
  No choice of an algebraic closure is needed, since k itself is algebraically closed.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, in
  `Mathlib.CategoryTheory.Monoidal.Grp`, on `Over (Spec (.of k))`.
  I read the interface description in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` and the class declaration.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and
  `AlgebraicGeometry.QuasiCompact`, `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`; `IsAffine` is the existing predicate
  in `Mathlib.AlgebraicGeometry.AffineScheme`.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback` and its projections,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`. These are used
  through the existing cartesian monoidal structure on the over category; the
  action is Mathlib `CategoryTheory.ModObj`, in
  `Mathlib.CategoryTheory.Monoidal.Mod`, with its evaluation in
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Mod`.
- Added existing, landed statement dependency
  `def-sfb-linearly-reductive-group-scheme`:
  `AlgebraicGeometry.IsLinearlyReductiveGroupScheme` and
  `AlgebraicGeometry.IsInvariantRationalSubspace`, in
  `Sheaf.AlgebraicGeometry.LinearlyReductiveGroupScheme`.
  This is the exact notion explicitly defined in the item's prose, so it is
  reused unchanged rather than restated. Its record and complete declarations
  were read. Adding this landed node is authorized by brief-stage2 §5.
- The existing `AlgebraicGeometry.points` and `AlgebraicGeometry.points.map`
  are in `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring`, publicly
  imported through the linear-reductivity module. I read their complete definitions.

Proof-plan imports: `Sheaf.AlgebraicGeometry.DenseRestrictionSemisimple`
(`GeneralLinearGroup.RationalHom.dense_restriction_semisimple`),
`WeilConjectures.AlgebraicGeometry.Regular` (`IsRegular.of_smooth`), and
`WeilConjectures.Mathlib.RingTheory.Nullstellensatz`
(`exists_algHom_ker_eq_of_isMaximal` and the other attached Nullstellensatz clauses).
The Mathlib Jacobson and source-local smoothness interfaces are supplied by
FiniteType and Smooth: `LocallyOfFiniteType.jacobsonSpace` and
`IsZariskiLocalAtSource.iff_of_iSup_eq_top`. Their declarations were read.
The remaining proof prerequisites (dense-fixed-local-ideal-jets,
regular-quotient-parameter-approximation, regular-separable-affine-smooth-neighbourhood)
have no recorded declarations on the read base, and are not needed to type
this statement. They remain named in its proof docstring. No unstated notion
is needed to formulate this delivery, and no dependency is replaced by a copy.

Edge cases checked: empty X or F is allowed (there is no nonempty or point binder);
trivial G and Γ recover the identity fixed subfunctor; disconnected G and X
remain allowed; positive characteristic is unrestricted; the zero representation
is included by the reused definition; nonreduced test algebras remain quantified;
there is no finite-generation restriction on Γ. The test algebras, schemes and
field all use universe u, consistent with the existing points and Spec interfaces;
there is no independent smaller test universe making the hypothesis vacuous.

Searches before writing:

- `msearch.py ... leanfinder "The common fixed scheme of a dense subgroup of a
  linearly reductive group acting on a smooth affine scheme is smooth"`:
  8 hits, all general smooth-morphism/smooth-locus results, no matching theorem.
- `msearch.py ... loogle '"fixedPoints", "Smooth"'`: 0 hits.
- `msearch.py ... grep 'linearly.reductive|AlgebraicRepresentation|SchemeAction'
  AlgebraicGeometry`: 0 Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for linear reductivity,
  algebraic representations and invariant subspaces: found and read
  `LinearlyReductiveGroupScheme.lean`, the rational representation interfaces,
  `DenseRestrictionSemisimple.lean`, `SemisimpleGroupSchemePoint.lean`, and
  `TorusFixedSchemeSmooth.lean`. The torus theorem assumes a torus and represents
  the full torus fixed functor, so is not this dense-subgroup theorem.
- `grep -rn 'lem-sfb-linearly-reductive-dense-fixed-smooth'
  lean/WeilConjectures`: no match.
- DAG search found the already landed `def-sfb-linearly-reductive-group-scheme`;
  there is no need for a new definition node. The scheme-action structures
  already exist in Mathlib; the project also uses precisely ModObj in its
  torus-fixed and scheme-action-groupoid modules.

No statement correction or STATEMENT-DISPUTED issue was found. The source statement
and node statement agree. The only node changes are the Lean record and the addition
of the existing landed definition dependency; no proof, statement, or other metadata
was changed. No new nodes or dependency modules are delivered.

## Second reading by N5

A separate in-thread reading was performed with the node and final module open.
This is not claimed to be an independent agent review: the dispatch brief expressly
forbids starting other agents, and the maintainer performs the independent review.

The reading checked each binder against the original prose: algebraically closed k;
smooth affine finite-type G; its group law and exact arbitrary-characteristic
linear reductivity; an abstract dense Γ; smooth affine finite-type X; an actual
scheme action; a closed inclusion of F; and the image-equals-fixed-subfunctor
condition for every algebra. It checked `points.map` against its source definition,
so g_A is canonical, and checked that a closed immersion makes the existential
factorization unique. `DenseRange` concerns the underlying Zariski points.
`Smooth F.hom` is precisely the requested conclusion. No connectedness,
irreducibility, separability, nonemptiness, or characteristic hypothesis slipped in.
The reused linear-reductivity definition tests scheme-theoretic invariance on all
algebras and includes dimension zero, so no characteristic-zero-only upstream
semisimplicity shorthand was substituted. No mathematical mismatch was found.
The first compiler pass required activating Mathlib's scoped group-on-homs
instance with `open scoped MonObj`; the binder g also avoids the reserved action notation gamma in that scope.
