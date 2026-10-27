## Worker report

The delivery states `AlgebraicGeometry.exists_completeLinearFlagScheme` in
`Sheaf.AlgebraicGeometry.CompleteLinearFlagScheme`, with `sorry` as its only proof.
It also defines the algebra-valued embedded flag type and scalar-image submodule in
`Sheaf.AlgebraicGeometry.CompleteLinearFlag`, attached to the new definition node below.
No data is postponed and no theorem is proved.

The inherited ending concerns the stage-1 split gate. The live node is split and
reviewed PASS for Q35, with no Lean record or released repair note. The stage-handoff
paragraph of coord/brief-stage2.md §0 explicitly authorizes continuing stage 2 in this
case. The accepted statement and eight-step proof are preserved; only `lean` and the
addition of the new definition to `stmt_deps` change in the item.

Hypothesis and clause correspondence:

- The field is `(k : Type u) [Field k]`; `(n : ℕ) (hn : 1 ≤ n)` is precisely n≥1.
  There is no algebraic closedness, perfection, characteristic, or smoothness hypothesis.
- A commutative k-algebra is `A : CommAlgCat.{u} k`. Its free module A^n is
  `LinearGroupSchemes.Index.{u} n → A`, where `Index n = ULift (Fin n)` is the recorded
  GL indexing convention, canonically the same n coordinates as `Fin n`.
- `CompleteLinearFlag.step i` retains the actual embedded submodule in Mathlib's
  `Module.Grassmannian A (ULift (Fin n) → A) (n-i.val)`; its quotient is finite projective
  and its rank at every prime is n-i. In a finite free module this means exactly that
  the embedded submodule is locally a free direct summand of rank i: locally split
  the quotient, trivialize its kernel, and use additivity of ranks. Conversely a local
  free direct summand has finite locally free quotient, hence finite projective.
  These are conditions on embedded submodules, not bases or abstract module classes.
- `monotone`, `zero`, and `last` give all inclusions and the endpoints 0 and A^n.
  The index `Fin (n+1)` covers exactly 0 through n.
- Scalar extension is `completeFlagScalarImage f N`, the B-span of coefficientwise
  images of vectors of N. This is exactly the image of B tensor_A N in B^n, including
  non-flat maps. It is defined by real `Submodule.span` data.
- `Fl : Over (Spec (.of k))` is the representing k-scheme. The `e A` are bijections
  from the algebra restriction of `yoneda.obj Fl` to these flags. The clause for
  every `A`, `B`, `f`, `x`, `i` identifies precomposition by Spec(f) with the specified
  scalar-image operation at each level. Thus these are natural classification
  bijections, exactly representability of the stated algebra functor. Functoriality
  is included by this naturality: bijectivity and the identity/composition laws of
  Spec transport those laws to scalar extension, without a separately chosen map.
- `IsProjective Fl.hom`, `IsProper Fl.hom`, and
  `LocallyOfFiniteType Fl.hom ∧ QuasiCompact Fl.hom` are precisely the three geometric
  properties, using the node's recorded H-projective plus quasi-compact convention.
- `a : ModObj (GeneralLinearGroup (Index n) k) Fl` is an internal scheme action in
  `Over (Spec k)`. Its `smul` is a k-scheme morphism from the product. The structure's
  `one_smul` and `mul_smul` fields are exactly the identity and associativity diagrams.
- The action formula quantifies over every algebra and every pair of its points.
  `CartesianMonoidalCategory.lift g x ≫ a.smul` is the point acted on. Its i-th
  submodule equals `Submodule.map` by `mulVecLin` of the invertible matrix supplied by
  the recorded `GeneralLinearGroup.homMulEquiv`. It is exactly `(g F_i)_i`, not just
  preservation or existence of an unspecified point action.
- Finally, for every family of k-subspaces, the displayed iff says that monotonicity,
  endpoints, and `Module.finrank k (F i) = i.val` hold exactly when it comes from one
  unique k-point. This explicitly renders the last sentence about complete linear flags.

Dependency declarations read and used:

- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs.
- def-pc-scheme: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  Mathlib.AlgebraicGeometry.Scheme, used through `Over (Spec k)` and its morphisms.
- def-pc-representable-functor: `CategoryTheory.yoneda`,
  Mathlib.CategoryTheory.Yoneda. The statement uses its natural-bijection description
  on affine tests, rather than claiming this covariant algebra functor itself is
  represented by an algebra.
- def-pc-projective-morphism: `AlgebraicGeometry.IsProjective`,
  WeilConjectures.AlgebraicGeometry.Morphisms.Projective.
- def-weil-proper-morphism: `AlgebraicGeometry.IsProper`,
  Mathlib.AlgebraicGeometry.Morphisms.Proper.
- def-weil-finite-type-morphism: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType
  and .QuasiCompact; finite type is their recorded conjunction.
- def-sc-general-linear-group: Sheaf.AlgebraicGeometry.LinearGroupSchemes, including
  `AlgebraicGeometry.LinearGroupSchemes.Index`; its public upstream dependency
  WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear supplies the actual
  `AlgebraicGeometry.GeneralLinearGroup`, its `GrpObj` instance and `homMulEquiv`.
  No general linear group, coordinates or action axioms are redefined.
- The new definition uses Mathlib's `Module.Grassmannian`, `Module.Finite`,
  `Module.Projective`, `Module.rankAtStalk` and `Submodule.span`. The latter two module
  properties and span are the exact declarations of its recorded dependency nodes.

All stated proof-dependency modules are imported as plain `import`, while statement
and definition dependencies are `public import`. The theorem's docstring records all
eight accepted proof steps and their supporting nodes. Every variable and universe is
explicit; auto-implicit binding is disabled in both modules.

Edge cases checked before writing:

- n=1: a single flag 0⊆A; the representing scheme is Spec k and the GL_1 action is
  trivial. The incidence equations in the accepted proof are empty.
- A=0: no nontriviality condition is imposed on test algebras. Its spectrum is empty,
  the locally constant rank requirements are vacuous, and its embedded flag is unique.
- Nonreduced algebras and non-flat coefficient maps are covered by the literal image
  span, not an assumption that tensor products preserve arbitrary injections.
  The flag inclusions are locally split, which explains why their base changes work.
- Every characteristic and arbitrary base fields are included. The lifted coordinate
  indices have cardinal n and do not change the matrix or module dimension.
- The definition itself extends to n=0, with one zero submodule; the theorem retains
  the requested n≥1 hypothesis.
- Over k, the rank condition becomes the usual dimension condition, and the final
  unique-point iff imposes no choice of basis or flag splitting.
- Tests live in the common universe of the scheme and base field, as in the recorded
  general-linear-group interface. No smaller independent test universe makes the
  quantification vacuous.

Searches for reuse (full successful search records are also in the new node):

- msearch.py leanfinder: “The functor of complete flags of locally direct summand
  submodules of A^n is represented by a projective scheme with the natural GL_n action”.
  Eight hits: Module.Grassmannian.projective_quotient, AffineSpace, Proj,
  Rep.diagonal_succ_projective, Projectivization.mk''_submodule, ProjectiveSpectrum,
  ProjectiveSpectrum.top and projIsoSpec. None states representability of flags.
- msearch.py loogle: `"Flag", "Scheme"`; zero hits.
- msearch.py leansearch: “Complete flags of submodules of a finite free module which
  are locally direct summands of specified ranks”. Eight hits including
  Module.Grassmannian, Module.Basis.flag, Module.Basis.toFlag and Submodule.IsLattice.
  A Grassmannian is one quotient; basis flags require a global basis and do not give
  arbitrary locally split flags over rings. Grassmannian's source lists its own
  representability as TODO. Its existing quotient notion is reused directly.
- msearch.py grep: `flagScheme|FlagScheme|flagVariety|completeFlag|CompleteFlag`;
  zero Mathlib hits. A second grep in RingTheory for flag definitions also gave zero.
- rg in lean/WeilConjectures found invariant complete flags over algebraically closed
  fields for endomorphisms, not the algebra-valued flag functor or flag scheme.
  Searching for this item's blueprint id there gave no match.
- rg in lean/Sheaf found CompleteFlagBundle's recursive sheaf construction and its
  consumers. It does not define the algebra-valued embedded submodule type or its
  classification. The existing construction is not copied.
- DAG searches for flag definition ids/titles found def-pur-complete-flag-bundle,
  weighted monomial flags, and unrelated ordered cohomology products or coordinate
  flags. tools/blueprint_refs.py search 'complete flag' returned zero blueprint nodes.
  tools/blueprint_refs.py ancestor reported inherited blueprint.from.node = None;
  that value and the full existing via chain are preserved for the new node.

No statement correction, dispute or dependency-record repair is needed.

## New nodes

`def-sfb-complete-linear-flag` defines the complete flag of embedded submodules in a
finite free module, using finite projective quotients of ranks n-i, and the scalar-image
submodule operation by span of coefficientwise images. The source is Milne's flag
functor immediately before Proposition 7.29, printed p.146, with the quotient
Grassmannian convention from Stacks Tag 089R. The module defines its actual data and
contains no `sorry`. The existing Mathlib Grassmannian is reused for each step; neither
basis flags nor the project's recursive geometric flag bundle supplies this type.
The searches and their raw result names are recorded in `mathlib_searches`. The item
adds this definition node to its statement dependencies; its original statement and
proof are unchanged.

Validation: scompile.py compiled each of the two delivered modules separately in
dependency order against the live published library, with no errors or warnings.
The definition module has zero `sorry`; the scheme module has exactly the named
item theorem's `sorry`. Signatures in both node records are verbatim from their
modules. The item differs from the read base only in `lean` and the added definition
in `stmt_deps`; neither the accepted statement nor proof was changed.

## Second reading by NQ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
