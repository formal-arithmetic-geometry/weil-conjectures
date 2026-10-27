## Worker report

The module `Sheaf.AlgebraicGeometry.StackDiagonalSpaceSourceRepresentability` states
`CategoryTheory.stack_diagonal_space_source_representability`, with one `sorry` and no
new definitions. The natural-language statement, dependencies and proof are unchanged.
The source is `literature/stacks-project/algebraic.tex`, Tag 045G,
`lemma-representable-diagonal`, implication (1) => (7), read with its proof and Tag 0300.
The current blueprint direct-images proof paragraph (3) was also read to check the
inherited context. There is no statement dispute or correction.

Hypothesis and clause correspondence:

- A scheme S is `{S : Scheme.{u}}`, using the recorded Mathlib scheme definition.
- The category over S-schemes is `F : BasedCategory.{v, w} (Over S)`; its projection
  to `Over S` is part of this Mathlib structure. `hF : IsFibredInGroupoids F`
  supplies the base-arrow lifting and strong cartesian uniqueness condition.
- The diagonal hypothesis is `hdiag : HasAlgebraicSpaceDiagonal F`, from the recorded
  moduli-groupoids module. Its interface tests the 2-fibre products of every pair of
  scheme maps, the equivalent diagonal criterion of Tag 045G (1) <=> (4).
  It keeps an equivalence over `Over S`, not just a bijection of isomorphism classes.
- Every algebraic space A over S is the unrestricted binder `A : AlgebraicSpace S`.
  This is the recorded full subcategory of fppf sheaves with representable diagonal
  and a surjective etale scheme atlas.
- Every morphism a is `a : BasedFunctor (discreteModuli A.obj.obj) F`.
  `discreteModuli` is the recorded total category of the presheaf of A. A based functor
  is exactly a functor commuting with the projections to S-schemes. As all arrows
  in a CFG are cartesian, no extra cartesian-preservation assumption is needed.
- The conclusion is `IsRepresentableByAlgebraicSpaces a`. Its full definition is
  `∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) F),
  ∃ (Z : AlgebraicSpace S) (p : Z.obj.obj ⟶ yoneda.obj T),
  HasSpaceBaseChange a T t Z p`. Thus it includes the node's explicit clause for
  every test scheme T and every map t. `HasSpaceBaseChange` gives a based equivalence
  from Z to `moduliTwoFiberProduct t a`, with a `ModuliTwoIso` identifying its first
  projection with `discreteModuliMap p`. This represents T ×_F A over T, equivalently
  A ×_F T over T by exchanging the factors and inverting the comparison isomorphism.
  Accordingly the projection to T is part of the assertion, not an arbitrary map.
- There is no `IsModuliStack`, atlas, smoothness or surjectivity hypothesis on F.
  No descent for objects of F has been assumed.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsFibredInGroupoids`, `BasedCategory`/`BasedFunctor` via its public
  Mathlib imports, `discreteModuli`, `moduliTwoFiberProduct`, `ModuliTwoIso`,
  `moduliTwoFiberFst`, `discreteModuliMap`, `HasSpaceBaseChange`,
  `IsRepresentableByAlgebraicSpaces`, and `HasAlgebraicSpaceDiagonal`.
  The full signatures and docstrings of the vocabulary in lines 364--541 were read.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpace`; their definitions were read.
- Proof-only import `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, and `pullback.lift`,
  for `def-pc-fibre-product` in proof step 1. Their signatures/docstrings were read.
- `lem-sfb-representable-pullback-over-space` has no Lean record or Mathlib match
  in the read repository. It is a proof dependency, not a statement dependency;
  its future module cannot yet be imported. It is cited in the theorem's full
  natural-language proof, following the recorded three-step proof and Tag 0300.
  No missing notion or dependency-interface repair is required to state this item.

Edge cases checked before writing:

- Empty A or T is permitted: neither any inhabited-point condition nor any atlas
  condition on the map a or t is introduced. Their fibre product can be empty.
- If F is a scheme, the result specializes to the usual algebraic-space fibre product.
- For F = BG, the automorphism information is retained in the iso-comma construction;
  it is not replaced by equality of object classes. The diagonal hypothesis is still
  substantive and controls the resulting isomorphism spaces.
- A CFG lacking effective descent is allowed: only `IsFibredInGroupoids` and the
  diagonal hypothesis occur, as required by Tag 045G.
- The universe u is shared by schemes and space presheaf values exactly as in the
  recorded algebraic-space definition. The hom and object universes v and w of F
  remain independent; no equality with u and no smallness hypothesis were imposed.
- Over T means the actual projection supplied by `HasSpaceBaseChange`, including
  compatibility through a 2-isomorphism, rather than existence of an unrelated map.

Searches for an existing statement, all run through `msearch.py` where indicated:

- LeanFinder: "A category fibred in groupoids with diagonal representable by algebraic
  spaces has every map from an algebraic space representable". Eight results, including
  `Functor.relativelyRepresentable.of_diag`, `diag_iff`, and scheme representability.
  None concerns CFGs, 2-fibre products or algebraic-space sources.
- Loogle: `"relativelyRepresentable", "of_diag"`. One result,
  `CategoryTheory.Functor.relativelyRepresentable.of_diag`. Its actual Mathlib source
  was opened: it concerns ordinary categorical pullbacks for a full functor preserving
  products, not this groupoid statement, so it is not an exact existing declaration.
- Mathlib grep: `AlgebraicStack|AlgebraicSpace|representable.*diagonal` in
  `CategoryTheory`. One hit, the ordinary-category diagonal discussion in
  `Mathlib/CategoryTheory/MorphismProperty/Representable.lean`.
- LeanSearch: "Every map from an algebraic space to a category fibred in groupoids
  with representable diagonal is representable by algebraic spaces". Eight results,
  again ordinary-category relative representability, scheme representability and
  scheme diagonals; no exact match.
- `rg` in both project roots `lean/WeilConjectures` and `lean/Sheaf` for
  `HasAlgebraicSpaceDiagonal|space_source_represent|representable.*diagonal|diagonal.*representable`,
  followed by all uses of `IsRepresentableByAlgebraicSpaces|HasAlgebraicSpaceDiagonal`.
  The Sheaf root has the reusable definitions and statements with stack/atlas or
  different morphism hypotheses, but no theorem giving this unrestricted CFG result.
  The upstream root has no matching definition or theorem.
- Search for the item id in `lean/WeilConjectures` found no declaration. A final name
  search for `stack_diagonal_space_source_representability` in Mathlib, both project
  roots and `dag/lean_names_upstream.json` found no existing declaration.

Validation: the prescribed `scompile.py Q54` server wrapper compiled the delivered
module in sandbox and library mode, with no errors or warnings (3.7 and 3.5 seconds).
The theorem's only proof is `sorry`; all variables and universes are explicitly bound
and `autoImplicit` is disabled. Delivery preflight is run separately before pushing.

## Second reading by Q54

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
