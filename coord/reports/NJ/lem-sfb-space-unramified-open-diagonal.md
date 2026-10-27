## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceUnramifiedOpenDiagonal` states
`AlgebraicGeometry.AlgebraicSpace.unramified_of_open_diagonal`, with its proof
postponed by `sorry`. It introduces no definitions. The node's mathematical
statement, proof, and proof dependencies are unchanged. The already landed node
`def-sfb-space-morphism-properties` is added to `stmt_deps` to reuse its chart test.

Hypothesis and clause correspondence:

- The arbitrary base scheme is `{S : Scheme.{u}}`. The arbitrary algebraic spaces
  are `{X Y : AlgebraicSpace S}`, and their morphism is `(f : X ⟶ Y)`.
- Local finite type is `hft : MapIsLocally (@LocallyOfFiniteType) f`. Expanding
  `MapIsLocally` quantifies over every pair `U V : Over S`, representable etale
  maps `a : yoneda.obj U ⟶ X.obj.obj`, `b : yoneda.obj V ⟶ Y.obj.obj`, and map
  `h : U ⟶ V` satisfying `a ≫ f.hom.hom = yoneda.map h ≫ b`. It requires precisely
  `LocallyOfFiniteType h.left`, with no surjectivity imposed on a or b.
- The relative diagonal is `pullback.diagonal f.hom.hom`. This is the canonical
  diagonal into the presheaf fibre product of the underlying sheaf map, not the
  absolute product over the original base. Limits of sheaves are computed on
  presheaves, so this represents the same sheaf fibre product as in the node.
- Its open-immersion hypothesis is
  `IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left)
  (pullback.diagonal f.hom.hom)`. For every scheme mapping into the target,
  the existing predicate supplies a scheme representing its pullback and an
  open-immersion projection to the test scheme. The property is invariant under
  changing the representing scheme, so the existential representation is exactly
  the requirement on every scheme base change.
- Unramifiedness is `MapIsLocally (@AlgebraicGeometry.IsUnramified) f`.
  It uses precisely the same universal compatible-chart quantifiers as the local
  finite type hypothesis, now concluding the recorded scheme notion
  `LocallyOfFiniteType h.left ∧ IsOpenImmersion (pullback.diagonal h.left)`.

Dependency interfaces read and used:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, and `AlgebraicSpace.IsEtale`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicSpace.MapIsLocally` (already landed definition node added to stmt_deps).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `AlgebraicGeometry.IsUnramified`.
- Proof imports retain the available DAG plan:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`
  (`fibreProduct_isAlgebraicSpace`),
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests`
  (`representable_etale_scheme_tests`),
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`
  (`Etale`, `Etale.etale_comp`, `Etale.of_comp`, and the open-immersion instance),
  and `Mathlib.AlgebraicGeometry.Morphisms.FlatMono`
  (`IsOpenImmersion.of_flat_of_mono`).

Source checked: `literature/stacks-project/spaces-morphisms.tex`,
`lemma-diagonal-unramified-morphism`, Tag 05W1(2), including its proof. The
five-step proof docstring follows the DAG, including its expanded cartesian
identifications and etale-monomorphism argument. The scheme diagonal criterion
is used only on chart maps; it is not substituted for the space assertion.

Edge cases checked: no nonempty-source or nonempty-base restriction, hence empty
spaces and the empty base remain covered. The chart quantifier includes empty
schemes and etale charts that are not surjective. There is no flatness,
Noetherian, separatedness, quasi-compactness, or local finite presentation
hypothesis on f. The property is genuinely local finite type, not finite type.
The single universe u follows the recorded algebraic-space framework, whose
schemes and presheaf values both use u; chart schemes are not put in a smaller
independent universe. Identity morphisms satisfy the criterion. Arbitrary
characteristics are included.

Searches (2026-10-24):

- `msearch.py ... leanfinder` with query "A locally finite type morphism of
  algebraic spaces whose diagonal is an open immersion is unramified": eight
  hits, all scheme/ring assertions, notably
  `FormallyUnramified.isOpenImmersion_diagonal` and the converse scheme instance;
  none states this algebraic-space assertion.
- `msearch.py ... leansearch` with query "A locally finite type morphism of
  algebraic spaces with open immersion diagonal is unramified": eight hits,
  again scheme assertions, no exact space result.
- `msearch.py ... loogle` with query
  `AlgebraicGeometry.AlgebraicSpace, IsUnramified`: zero hits (the service does
  not know the project's AlgebraicSpace identifier).
- `msearch.py ... grep 'unramified.*diagonal|diagonal.*unramified'
  AlgebraicGeometry`: four hits in Mathlib's FormallyUnramified.lean, all for
  schemes or rings.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the unramified/diagonal names, chart tests, and the item id found no exact
  existing theorem. It located the reusable `MapIsLocally` definition and the
  scheme `IsUnramified` definition. `SpaceChartwiseUnramified` in
  `SpaceUniversalConormal.lean` is the same chart-test application expanded;
  this delivery introduces no competing predicate, using the shared generic
  chart test directly. `SpaceMapIsUnramified` in `OpenModuliSubstack.lean` has
  scheme target and cannot express this arbitrary algebraic-space target.

No statement correction or disputed assertion is needed. No new node or
unusable dependency interface was required.

Validation: every delivered Lean file is checked through scompile.py, followed
by deliver2.py --no-push and the prescribed delivery wrapper.

## Second reading by NJ

Author's final consistency reread (not an independent reviewer): the base,
space morphism, chartwise local finite type, representable open relative
diagonal, and chartwise unramified conclusion match the node clause by clause
as detailed above. In particular the pullback is over Y, neither chart is
required to be surjective, and no scheme-target restriction was introduced.
The only dependency addition reuses the previously landed chart-test notion;
there are no new definitions to review. The maintainer's independent review
remains the independent reading specified in this dispatch brief.
