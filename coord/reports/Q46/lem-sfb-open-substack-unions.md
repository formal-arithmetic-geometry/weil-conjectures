## Worker report

The module `Sheaf.AlgebraicGeometry.OpenSubstackUnions` states
`CategoryTheory.openModuliSubstack_unions`, with its proof exactly `sorry`.
Its helper `OpenModuliSubstack.HasPullbackOpen` is a fully written Prop-valued
abbreviation of the existing open-pullback presentation, specialized to the
specified open subset of the test scheme. It asserts an actual equivalence with
the existing 2-fibre product, together with a 2-isomorphism identifying the
projection with the actual open-subscheme inclusion. It introduces no replacement
stack, fibre product, or representability notion, and chooses no data from a sorry.

Sources read: Stacks `stacks-properties.tex`, `lemma-open-substacks` (06FJ),
`lemma-union-open-substacks` (05UQ), and `lemma-substacks-presentation` (0507).
The six-step proof docstring records the accepted DAG proof: invariant atlas opens,
set-sizedness, invariant union, algebraicity, factorization and containment,
surjective scheme-pullback comparison, relative covering, and the empty fibre.
The item statement and proof are unchanged. The two already landed definition
nodes `def-sfb-algebraic-moduli-stack` and `def-sfb-open-moduli-substack` were added
to `stmt_deps` because they give exactly the notions used in this statement.
There are no new nodes, dependency repairs, or statement corrections.

Hypothesis and clause correspondence:

- The base scheme is `{S : Scheme.{u}}`. The algebraic stack is
  `F : BasedCategory.{v, w} (Over S)` with `hF : IsAlgebraicModuliStack F`.
  This predicate is the existing conjunction of etale stack descent,
  algebraic-space diagonal, and a smooth surjective scheme atlas. No DM,
  finite-type, quasi-compactness, or nonemptiness hypothesis is added.
- An open substack is the existing `OpenModuliSubstack F`. It specifies a
  full object predicate stable under all arrows (cartesian in this CFG), hence
  under isomorphism, and actual open-immersion scheme-pullback presentations.
  Algebraicity of the source is the usual consequence when F is algebraic.
- A set of representatives up to equivalence over F is rendered as
  `Small.{u} (OpenModuliSubstack F)`. Strictly full subcategories equivalent
  over F have equal object predicates: an object in one is isomorphic in F
  to an object in the other, and closure under isomorphism gives membership.
  Conversely equal predicates give the same substack. All other structure
  fields are proofs. Thus smallness of this type is exactly smallness of the
  equivalence classes, rather than a claim about arbitrary presentations of
  the same substack. A scheme atlas has opens in Type u, giving this bound.
- Every set and family is covered by `(I : Type z)` and
  `(U : I → OpenModuliSubstack F)`, with z independent of all stack universes.
- The union is `W : OpenModuliSubstack F`, and its algebraicity is the first
  conjunct `IsAlgebraicModuliStack W.category`.
- Each input is contained in it by `∀ i, (U i).IsContainedIn W`.
  The next conjunct says that every common upper bound Z contains W.
  `IsContainedIn` is the dependency's actual object-predicate implication.
- For every scheme T over S and every `t : h_T → F`, the next conjunct supplies
  `V : I → T.left.Opens`. For each i, `HasPullbackOpen` presents
  `h_T ×_F U_i` by the open subscheme `V i` with its projection. The same
  predicate presents `h_T ×_F W` by `⨆ i, V i`. Hence these are equal open
  subschemes over T, not just abstractly isomorphic schemes. Uniqueness of
  the representing open over T makes the formulation independent of these
  existentially chosen presentations.
- The inputs as open substacks of W are supplied by
  `A : I → OpenModuliSubstack W.category` and the explicit equality of object
  predicates `(A i).property x ↔ (U i).property x.obj`. Fullness makes their
  inclusions the actual inclusions of the specified inputs into W.
- For every scheme test into W, each `A i` has the displayed open pullback
  and `⨆ i, V i = ⊤`. This states precisely that these open immersions cover
  each such scheme; no index-size or quasi-compactness restriction is used.
- The empty-family clause is `IsEmpty I → ∀ x, W.property x ↔
  IsEmpty (F.p.obj x).left`. This includes all ambient objects over the empty
  scheme, as required by empty-cover descent, and no object over a nonempty
  scheme. It does not incorrectly define the empty stack by the constantly
  false object predicate.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsFibredInGroupoids`, `IsModuliStack`,
  `HasAlgebraicSpaceDiagonal`, `moduliTwoFiberProduct`, `moduliTwoFiberFst`,
  `ModuliTwoIso`, `discreteModuli`, `discreteModuliMap`, `HasSpaceBaseChange`,
  `SpaceMapIsSurjective` (the latter predicates occur in the existing stack API).
  Their full signatures and docstrings were read in the dependency source.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack`, `IsSmoothModuliAtlas`,
  `SpaceMapIsSmooth`; the recorded diagonal and atlas interface is retained.
- `Sheaf.AlgebraicGeometry.OpenModuliSubstack`:
  `CategoryTheory.OpenModuliSubstack`, `fullModuliInclusion`,
  `OpenModuliSubstack.category`, `OpenModuliSubstack.IsContainedIn`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`:
  `AlgebraicGeometry.Smooth`, used by the recorded smooth-atlas predicate.
  Its affine-local signature and docstring were read at lines 59--66.
- `def-weil-size-convention` is a convention node with no Lean declaration;
  explicit universes u, v, w, z implement it. Smallness is relative to the
  scheme universe u; index sets are allowed in the independent universe z.
- The proof dependency `lem-sfb-invariant-open-substack-descent` has no Lean
  record in the inspected DAG, so no unstated module is imported. Its exact
  statement was read and the proof docstring identifies all its uses. It is
  not needed to type this theorem, and is not duplicated in this delivery.

Edge cases checked before drafting: empty family; empty ambient stack;
empty test scheme (the open union is both bottom and top there); singleton;
repeated inputs; an input equal to the whole stack; infinite families with
no finite subcover; disjoint inputs whose union contains an object locally
but not in any single input globally; and stacks with nontrivial stabilizers.
In particular the union is not the pointwise existential disjunction of the
input object predicates. The relative A_i preserve all arrows, and every
comparison uses equivalences of fibred categories rather than sets of
isomorphism classes. No STATEMENT-DISPUTED issue remains.

Searches actually run:

- `msearch.py ... leanfinder`: “Open substacks of an algebraic stack form a set
  and arbitrary unions commute with scheme pullback”. Eight hits, including
  `Scheme.Opens`, scheme image-supremum lemmas and ordinary scheme covers;
  none states the algebraic-stack theorem.
- `msearch.py ... loogle`: `OpenModuliSubstack, Small, IsAlgebraicModuliStack`.
  Zero hits, with unknown identifier OpenModuliSubstack in the search service;
  this is not evidence about the local project's declarations.
- `msearch.py ... grep`: `OpenSubstack|openSubstack|AlgebraicStack|substack.*union`
  in Mathlib AlgebraicGeometry. Zero hits.
- `msearch.py ... leansearch`: “Arbitrary unions of open substacks of an
  algebraic stack commute with scheme base change”. Eight scheme-only hits,
  including `Scheme.Hom.preimage_iSup`, `image_iSup` and ordinary covers.
- `rg` of `lean/WeilConjectures` for OpenSubstack, openSubstack,
  OpenModuliSubstack and open-substack unions, and the item id: no hits.
- `rg` of `lean/Sheaf` for open substack, algebraic stack, and union/pullback
  helper names: located and reused `OpenModuliSubstack` and
  `IsAlgebraicModuliStack`. The existing `StackTopologyOpenSubstacks` theorem
  concerns DM stacks and their point topology; it does not state the present
  general algebraic-stack union and covering result. No union theorem or
  `HasPullbackOpen` helper was found. The DAG's recorded definitions were
  read before importing them. The upstream-name index search found no
  corresponding declaration.

Validation: the delivered module compiled through the prescribed `scompile.py`
against the published live library with no errors or non-sorry warnings.

## Second reading by Q46

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
