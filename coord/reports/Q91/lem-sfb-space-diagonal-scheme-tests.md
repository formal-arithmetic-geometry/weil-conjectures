## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceDiagonalSchemeTests` states
`AlgebraicGeometry.AlgebraicSpace.diagonal_scheme_tests`, with its proof postponed by
`sorry`. It introduces no definitions and changes only the item's `lean` record.
The source statement and proof were read in `literature/stacks-project/spaces-morphisms.tex`,
`lemma-properties-diagonal`, Tag 03HK, and the scheme-test convention in `spaces.tex`,
`definition-relative-representable-property`, Tag 025V. No node correction is needed.

Hypothesis and clause correspondence:

- The base scheme is `{B : Scheme.{u}}`. The arbitrary spaces and their morphism are
  `(U V : AlgebraicSpace B) (g : U ⟶ V)`. There are no finiteness, Noetherian,
  separation, quasi-compactness, or nonemptiness assumptions.
- The size convention is implemented by the explicit universe `u` and the recorded
  algebraic-space encoding: sheaves valued in `Type u` on `(Over B)ᵒᵖ`.
  Every scheme test has that same universe, so no smaller independent test universe
  makes the assertion vacuous.
- `W = U ×_V U` is the fppf-sheaf pullback `pullback g.hom g.hom`.
  `pullback.diagonal g.hom` is the canonical diagonal into exactly that sheaf pullback;
  `.hom` passes to its underlying natural transformation.
- The recorded predicate `IsRepresentableWith` quantifies over **every** `T : Over B`
  and `a : yoneda.obj T ⟶ W.obj`. It supplies a scheme `D : Over B`, a projection
  `p : D ⟶ T`, and a map `q : yoneda.obj D ⟶ U.obj.obj`, together with
  `IsPullback q (yoneda.map p) (pullback.diagonal g.hom).hom a`.
  This is an actual representing square for `D_T = U ×_W T`, including its projection.
  The pullback in presheaves represents the sheaf fibre product because sheaf limits
  are preserved by the inclusion into presheaves.
- The property's first conjunct `LocallyOfFiniteType p.left` renders local finite type
  of the same scheme projection `d_T`.
- Its second conjunct `Mono p.left` renders exactly the stated cancellation criterion:
  for every scheme `Z`, and maps `a,b : Z ⟶ D.left`, equality
  `a ≫ p.left = b ≫ p.left` implies `a = b`. This uses the category of schemes,
  rather than merely the category `Over B`.
- These two properties occur inside one `IsRepresentableWith`, so they hold for the
  same representing scheme and map. Representability is part of that existing
  predicate, rather than a separately chosen or arbitrary map.

Dependency declarations used (their signatures and docstrings were read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, and its representable-diagonal and atlas
  predicate `AlgebraicSpace.IsAlgebraicSpace`. No private replacement is introduced.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicSpace.fibreProduct_isAlgebraicSpace` supplies the algebraic-space
  interpretation of the chosen sheaf fibre product. Its module is publicly imported.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType` is the exact recorded scheme property.
- `Mathlib.CategoryTheory.Limits.Shapes.Diagonal`: `pullback.diagonal` is the
  canonical morphism, defined by the two identity maps into the pullback.
- `Mathlib.CategoryTheory.Category.Basic`: `CategoryTheory.Mono` is literally
  right cancellation against maps from arbitrary objects of the ambient category.
- `def-weil-size-convention` is a metatheoretic convention with no Lean declaration;
  its explicit universe convention is used above.

The module also imports all already stated proof dependencies, without `public`:
`Mathlib.AlgebraicGeometry.Pullbacks` for scheme fibre products;
`Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence` for atlas permanence;
`Mathlib.AlgebraicGeometry.Morphisms.Etale` and
`Sheaf.AlgebraicGeometry.UnramifiedMorphism` for the etale/unramified step;
`Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties` for descent.
The local-finite-type cancellation and base-change proof dependencies are both in
the already imported `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
The theorem docstring follows all six DAG proof steps, naming their inputs.

Edge cases checked before writing:

- Empty base, empty spaces, and the empty test scheme are permitted by all binders;
  the equality-locus representation and cancellation criterion still apply.
- For the identity morphism, the diagonal is an isomorphism and its scheme tests
  are isomorphisms, hence locally of finite type and monic.
- Arbitrarily large or non-quasi-compact atlases and spaces are not excluded.
  The conclusion is local finite type, not finite type or quasi-compactness.
- A scheme `Z` in the cancellation test need not arrive with a base structure:
  `Mono p.left` tests all scheme morphisms. The common projection supplies the base
  structure in the natural-language proof.

Searches for an existing statement:

- `msearch.py ... leanfinder`: “Every scheme base change of the diagonal of a
  morphism of algebraic spaces is a locally finite type monomorphism”. Eight hits,
  including `IsImmersion.instDiagonalScheme`, local-finite-type base-change,
  `FormallyUnramified.isOpenImmersion_diagonal`, and affine-target constructors.
  Their returned signatures concern schemes, not arbitrary algebraic spaces, and
  do not state this scheme-test assertion.
- `msearch.py ... loogle`: `"diagonal", "LocallyOfFiniteType"`: no hits.
- `msearch.py ... grep` in `AlgebraicGeometry`:
  `AlgebraicSpace|locallyOfFiniteType.*diagonal|diagonal.*locallyOfFiniteType`:
  one hit, `FormallyUnramified.isOpenImmersion_diagonal`, requiring a scheme morphism
  already formally unramified and locally of finite type. No match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for diagonal scheme tests,
  representable diagonal properties, and local-finite-type monomorphisms:
  the existing `SpaceMonicDiagonalTests` concerns a different comparison and
  `SpaceFibreProductComparison` cites the present node as a proof input.
  `AlgebraicSpaceLftDiagonalLfp` assumes a locally finite type morphism and concludes
  local finite presentation; it is not the unrestricted diagonal assertion.
  No existing exact statement was found.
- `grep -rn 'lem-sfb-space-diagonal-scheme-tests' lean/WeilConjectures`: no hits.
- `rg` for `diagonal_scheme_tests`, `SpaceDiagonalSchemeTests`, and
  `LocallyOfFiniteType p.left ∧ Mono p.left` in `dag/lean_names_upstream.json`,
  `lean/Sheaf`, and `lean/WeilConjectures`: no existing declaration/name collision.

Validation: `scompile.py Q91 lem-sfb-space-diagonal-scheme-tests` compiled the single
delivered module both as a sandbox file and with its library module name, cleanly.
No new nodes, dependency repairs, or statement disputes.

## Second reading by Q91

Author's separate second pass; the maintainer supplies the independent review, as
required by the dispatcher brief. Reopened the node and module and checked the base
and arbitrary morphism binders, the actual sheaf diagonal, every scheme test through
`IsRepresentableWith`, and its two properties on the same projection. In particular,
`Mono p.left` is in `Scheme`, so the explicit all-schemes cancellation clause is
preserved. The universe of the tests matches the universe of the base. No assumptions
on `g`, `U`, `V`, or `B` beyond the node's scheme/algebraic-space data were introduced.
The one postponed theorem matches the one DAG statement; all six proof paragraphs
are documented. No mismatch or further change was found in this pass.
