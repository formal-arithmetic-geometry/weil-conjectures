## Worker report

The module `Sheaf.AlgebraicGeometry.FaithfulStackMapRepresentable` states
`CategoryTheory.isRepresentableByAlgebraicSpaces_iff_injective_mapIso` with
`sorry` as its entire proof. It introduces no definitions. The natural-language
proof in its docstring follows all five steps of the node. The source read was
`literature/stacks-project/algebraic.tex`, label
`lemma-characterize-representable-by-algebraic-spaces`, Tag 04Y5 (1) and (3),
including its proof. No statement correction or disputed statement is needed.
There is no repair note for this item.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`. Every test is an actual `S`-scheme
  `T : Over S`, with no affine, nonempty, characteristic, or finiteness restriction.
- The size convention is expressed by explicitly declared universes
  `u v₁ v₂ w₁ w₂`. The two based categories have independent object and morphism
  universes, `BasedCategory.{v₁, w₁} (Over S)` and
  `BasedCategory.{v₂, w₂} (Over S)`; no equality between these universes is imposed.
- The algebraic stacks are `X` and `Y`, with the two hypotheses
  `hX : IsAlgebraicModuliStack X` and `hY : IsAlgebraicModuliStack Y`.
  These recorded predicates include the fibred-in-groupoids and stack conditions,
  the algebraic-space diagonal, and a smooth surjective scheme atlas.
- The morphism over S is `F : BasedFunctor X Y`, whose projection equation is
  part of the existing structure. No separate arbitrary fibre functor is assumed.
- The left side is precisely `IsRepresentableByAlgebraicSpaces F`. Its recorded
  definition quantifies over every `T` and every based map `h_T → Y`, and asks for
  an algebraic space `Z`, a map to `h_T`, and `HasSpaceBaseChange`.
  That last predicate requires a based equivalence to the actual 2-fibre product
  and a vertical natural isomorphism comparing its first projection with the
  specified map to `h_T`. Thus it expresses equivalence over T, as in the node.
- The right side quantifies over every `T : Over S` and every pair
  `x x' : Functor.Fiber X.p T`. The type `x ≅ x'` is exactly the set of
  isomorphisms in the fibre, retaining automorphisms. Its image is
  `(moduliFiberMap F T).mapIso α`, using the actual induced functor recorded
  by the dependency node. `Function.Injective` says precisely that this map
  on isomorphisms is injective; it does not require fullness or surjectivity.
- `↔` supplies both implications with the node's orientation.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  with its fppf sheaf, representable diagonal, and surjective etale atlas predicate.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.moduliFiberMap`, `CategoryTheory.IsRepresentableByAlgebraicSpaces`,
  `CategoryTheory.HasSpaceBaseChange`, `CategoryTheory.ModuliTwoIso`,
  `CategoryTheory.discreteModuli`, `CategoryTheory.discreteModuliMap`,
  `CategoryTheory.moduliTwoFiberProduct`, `CategoryTheory.moduliTwoFiberFst`,
  `CategoryTheory.IsModuliStack`, and `CategoryTheory.IsFibredInGroupoids`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack` and its smooth-atlas predicate.
- The size-convention node is explicitly marked a metatheoretic convention with
  no declaration or module; it is rendered by the universe binders above.
- Mathlib's `CategoryTheory.BasedCategory`, `CategoryTheory.BasedFunctor`, and
  `CategoryTheory.Functor.Fiber` are reused through those public imports.

Proof-only imports follow all presently recorded proof dependencies:
`Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`
(`AlgebraicGeometry.AlgebraicSpace.schemeSpace`),
`Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts`
(`CategoryTheory.algebraicStack_twoFiberProduct`), and
`Sheaf.AlgebraicGeometry.AlgebraicSetoidSpace`
(`CategoryTheory.exists_algebraicSpace_of_trivial_moduli_automorphisms`).
Their source declarations and docstrings were read. The proof dependency
`lem-sfb-fibred-groupoid-representable-smooth-calculus` currently has neither
`lean`, `mathlib_match`, nor a closed upstream audit, so it has no recorded
module to import. It supplies no notion missing from this statement.

Edge cases checked before writing: the empty base/test scheme is included;
if a fibre has no objects its pair quantifier is vacuous; an empty isomorphism
set gives ordinary injectivity; `x = x'` explicitly tests automorphisms rather
than only distinct objects or isomorphism classes. Identity morphisms give
injective identity maps and representable identity base changes. A structure
map of a stack with nontrivial stabilizers to its base scheme fails injectivity
on an automorphism fibre, as it should. Independent category universes are
retained, while the scheme and algebraic-space universes follow the existing
recorded definitions. These were mathematical edge checks, not added theorems.

Searches actually run using the prescribed wrapper:

- `leanfinder`: "A morphism of algebraic stacks is representable by algebraic
  spaces if and only if the functor on every fibre groupoid is faithful".
  Eight hits, including ordinary scheme forgetful functors, relative ordinary
  representability, and faithful fibre inclusions; none states this criterion.
- `loogle`: `"Faithful", "AlgebraicSpace"`. Zero hits.
- `grep`: `representable.*faithful|faithful.*representable|algebraic.stack`
  in Mathlib `CategoryTheory`. Eight hits in ordinary representability and
  monoidal Day convolution; none states this criterion.
- `rg` of the same concepts and `IsRepresentableByAlgebraicSpaces|moduliFiberMap`
  in the project's `lean/WeilConjectures` and `lean/Sheaf` found the existing
  definitions and consumers listed above, but no theorem stating the criterion.
  A further search for the proposed theorem name and representability/faithfulness
  in Mathlib and both source roots found no collision. Search by the node ID in
  `lean/WeilConjectures` and `dag/lean_names_upstream.json` found no binding.

Validation: the delivered module is compiled separately with the prescribed
`scompile.py`; the required `deliver2.py --no-push` preflight and compile are run
before the push. The only postponed proof is the main theorem named above.

## Second reading by Q32

The worker reread the node, Tag 04Y5, the delivered signature, and the recorded
representability definition after writing the module. This is a self-check;
the maintainer provides the independent review described in the assignment.
Both algebraic-stack hypotheses are present. The test schemes range over all
of `Over S`, and the pair quantifier uses the actual fibre category.
`mapIso` has exactly the requested source and target isomorphism sets.
The existing representability predicate includes compatibility with the test
scheme projection, so no projection condition was lost. Neither fullness nor
an arbitrary chosen equivalence or atlas was added to the theorem hypotheses.
The statement has no let binders, local notation, private helpers, or implicit
undeclared universes. No mismatch was found and no node statement changed.
