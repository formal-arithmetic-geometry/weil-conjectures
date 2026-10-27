## Worker report

Delivered module: `Sheaf.AlgebraicGeometry.GenericMatrixLocusSubgroupClosure`.
Main declaration: `AlgebraicGeometry.GenericMatrixLocus.isClosedSubgroupScheme_closure`.
Stage 2 only: its proof is `sorry`; all four auxiliary definitions have actual data.
The statement, dependencies, proof and all other existing DAG fields are unchanged;
only the item's `lean` field is added. No new nodes or dependency repairs are needed.

The clause-by-clause rendering is as follows.

- The field F is `{F : Type u} [Field F]`. The finite-dimensional F-vector space E
  is `(E : Type u) [AddCommGroup E] [Module F E] [FiniteDimensional F E]`.
  The matrix model of GL(E) is the existing `GeneralLinearGroup` indexed by
  `LinearGroupSchemes.Index.{u} (Module.finrank F E)`. Choosing a basis identifies
  this with GL(E); no special dimension or chosen extra structure is required.
- The F-group scheme is `G : Over (Spec (.of F))` with `[GrpObj G]`. Affineness is
  `[IsAffine G.left]`, and finite type is `[LocallyOfFiniteType G.hom]`: the
  affine source and affine point base supply quasi-compactness, so this is the
  finite-type condition. The specified closed subgroup embedding into GL(E) is
  `embedding`, with `[IsClosedSubgroupScheme embedding]`; the existing class
  supplies the group homomorphism and closed immersion.
- C is literally `Spec (.of A)` with `[CommRing A] [Algebra F A]` and
  `[Algebra.FiniteType F A]`. Its structure morphism is the canonical algebra map,
  bundled by `.asOver (Spec (.of F))`.
- Geometric integrality is exactly `hgeom : ∀ (L : Type u) [Field L]
  [Algebra F L], IsDomain (A ⊗[F] L)`. `IsDomain` includes nontriviality, so the
  explicit nonzero clause is retained. Test extensions occupy the same universe
  as F and A, rather than a potentially smaller independent universe. This is
  the ordinary common-universe scheme convention and includes Frac(A).
- The F-morphism `j` is the displayed morphism in `Over`; `[IsImmersion j.left]`
  renders the closed-then-open factorization, by Mathlib's
  `isImmersion_iff_exists`. `[QuasiCompact j.left]` retains the explicit
  quasi-compactness requirement.
- The rational point is `c₀ : 𝟙_ (Over (Spec (.of F))) ⟶ C`, and
  `hc₀ : c₀ ≫ j = η[G]` says its image is the identity. The terminal object of
  the over category is the F-point base itself.
- `V` is an open of the underlying scheme of `C ⊗ C`, the categorical product in
  the over category, hence C ×_F C. `W` is an open of C. `hV : Nonempty V` and
  `hW : Nonempty W` are exactly the two nonempty-open hypotheses.
- The partial operations have their actual domains:
  `m₀ : V.toScheme ⟶ Spec (.of A)` and `i₀ : W.toScheme ⟶ Spec (.of A)`.
  `hm` is `m₀ ≫ j.left = V.ι ≫ (j ⊗ₘ j).left ≫ μ[G].left`, and
  `hi` is `i₀ ≫ j.left = W.ι ≫ j.left ≫ ι[G].left`.
  These are precisely the two prescribed equalities. The maps are automatically
  F-morphisms from these equalities and the fact that j is over F, so no extra
  hypotheses or arbitrary comparison maps are introduced.
- B is `Γ(G.left, ⊤)`. The actual coordinate map `coordinates j` is
  `j.left.appTop ≫ (Scheme.ΓSpecIso (.of A)).hom`; the second factor is the
  canonical identification of Γ(Spec A) with A. Its ring kernel is exactly I.
  `closure j` is literally `Spec (.of (B ⧸ RingHom.ker (coordinates j).hom))`.
  `inclusion j` is Spec of the quotient map followed by `G.left.isoSpec.inv`.
  `closureOver j` supplies the F-structure by composition with `G.hom`.
  These helpers are components of the construction explicitly required by this
  node, not new independent notions or a second definition of scheme image.
- The first conclusion existentially supplies `GrpObj (closureOver j)` and
  `IsClosedSubgroupScheme (Over.homMk (inclusion j))`. The existing subgroup
  class entails compatibility with multiplication and identity; inverse
  compatibility is the group-object identity `GrpObj.inv_hom`. Thus all three
  specified operations of G restrict, with the inherited group identities.
  It is the closed-subgroup-scheme notion on all test algebras, including
  nonreduced ones, and not merely a subgroup of F-points.
- The second conclusion supplies `e : closure j ≅ j.left.image` with
  `e.hom ≫ j.left.imageι = inclusion j`. It identifies the explicit quotient
  closed subscheme with the existing scheme-theoretic image over G, retaining
  the coordinate quotient and the image clause together.
- There is no group structure on C and no smoothness assumption anywhere.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs, line 180.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`,
  Mathlib.CategoryTheory.Monoidal.Grp, lines 43–47; `MonObj.one`, `MonObj.mul`,
  `GrpObj.inv`, rendered by the standard η, μ, ι notation.
- `def-sc-group-scheme-subgroup`: `AlgebraicGeometry.IsSubgroupScheme` and
  `AlgebraicGeometry.IsClosedSubgroupScheme`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs, lines 76–101.
- `def-sc-general-linear-group`: imported its recorded
  Sheaf.AlgebraicGeometry.LinearGroupSchemes module and used its `Index`;
  the recorded module itself explicitly delegates GL to
  `AlgebraicGeometry.GeneralLinearGroup` in
  WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear. Read its full
  definition, group instance, finite-type instance and natural `homMulEquiv`.
  The node record covers SL as well, but this item uses only its existing GL.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion; its immersion clause is
  `AlgebraicGeometry.IsImmersion` and `isImmersion_iff_exists`,
  Mathlib.AlgebraicGeometry.Morphisms.Immersion, lines 45 and 155.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion`,
  Mathlib.AlgebraicGeometry.OpenImmersion, line 38; used through the existing
  immersion notion and the canonical open inclusions `V.ι` and `W.ι`.
- `def-nagata-scheme-theoretic-image`: `Scheme.Hom.image`,
  `Scheme.Hom.imageι`, Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme, lines
  662–665; read also the factor map `toImage` and its factorization identity.

The private proof-plan imports include Mathlib.AlgebraicGeometry.FunctionField
(germ injectivity), Mathlib.AlgebraicGeometry.Pullbacks (pullbackSpecIso),
Mathlib.RingTheory.Flat.Basic (lTensor_preserves_injective_linearMap),
Mathlib.LinearAlgebra.Basis.VectorSpace (vector spaces free), and
WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
(ker_le_ker_iff_existsUnique_fac). The public imports provide the quotient,
affine spectrum, integral-scheme and Hopf-algebra interfaces already in their
transitive imports. The theorem docstring reproduces all seven DAG proof steps
with their dependency node ids, including the nonreduced-test-algebra argument.

Edge cases checked before writing and again against the final signature:

- E = 0: finrank is zero and `Index 0` is empty, which the upstream coordinate
  construction supports. No positivity or nonempty-index hypothesis is present.
- C = Spec F and G the trivial group: all hypotheses and conclusions specialize
  as expected. The zero algebra A is excluded by hgeom at L = F and by c₀.
- Nonempty V and W need not contain the identity or have F-rational points;
  the two hypotheses require only scheme points. No density of rational points
  or algebraic closedness of F has been inserted.
- Arbitrary characteristic and imperfect F are allowed. No smoothness,
  reducedness or geometric reducedness of G is assumed.
- G and test algebras can be nonreduced. The conclusion uses the existing full
  closed-subgroup class, not rational-point containment.
- A proper dense open C in its closure is allowed, since no global group law on
  C is requested. The partial laws are restricted to precisely V and W.

Searches actually run (2026-10-24):

1. `msearch.py ... leanfinder`: "The scheme theoretic closure of an integral
   affine locus with generic multiplication and inversion inside a matrix group
   is a closed subgroup scheme". Eight hits; top hits concern topological SL
   embeddings, abstract subgroup adjoinNegOne, zero loci and integral morphisms.
   None states the scheme-theoretic generic-law assertion.
2. `msearch.py ... loogle`: `AlgebraicGeometry.IsClosedSubgroupScheme`.
   Zero hits, unknown identifier in the Mathlib search index. The project
   declaration was found and read directly in GroupScheme.Defs.
3. `msearch.py ... grep`: `generic.*(group|mul)|closure.*[Ss]ubgroup|[Ss]ubgroup.*closure`
   in Mathlib/AlgebraicGeometry: zero hits.
4. `msearch.py ... leansearch`: "A geometrically integral affine locus with
   generic group multiplication and inverse has subgroup scheme theoretic
   image". Eight hits; integral-scheme criteria, germ injectivity, and imageι,
   but no theorem extending generic laws to the closed image.
5. `rg -n` with the same closure/generic pattern in the project's
   WeilConjectures and Sheaf trees. The image result in
   WeilConjectures.AlgebraicGeometry.GroupScheme.Image assumes a proper source
   that is already a group scheme and a homomorphism. It does not apply here.
   Topological and abstract subgroup closures also do not supply this statement.
6. Searched the exact node id in WeilConjectures and Sheaf: no declaration.
   Searched `genericMatrixLocus|GenericMatrixLocus` in both trees, Mathlib and
   dag/lean_names_upstream.json: no preexisting declarations with these names.

Source read: local Milne PDF pages 30–32 (printed pp.18–20), including Lemma
1.40 and Theorem 1.45. Those statements concern actual subgroups of rational
points. The node explicitly records the agent generalization, whose proof is
its coordinate-kernel argument, not an attribution of the stronger statement
to Milne. No source-based correction or STATEMENT-DISPUTED flag is needed.

Validation: scompile.py compiled the final sandbox probe and actual module
separately against the live published library, both clean, at 20.8 s and 6.5 s.
Maximum source line length is 89 characters. All universes and variables are
explicitly bound. The only postponed proof is the main named theorem.

## Second reading by Q41

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
