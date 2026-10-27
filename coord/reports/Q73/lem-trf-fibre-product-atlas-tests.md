## Worker report

The module `Sheaf.AlgebraicGeometry.FibreProductAtlasTests` supplies the real canonical
map `AlgebraicGeometry.AlgebraicSpace.fibreProductAtlasMap` and the statement
`AlgebraicGeometry.AlgebraicSpace.fibreProduct_atlas_tests`. Its sole theorem proof
is `sorry`. No source, statement, proof-plan or dependency correction was needed.
Q07's existing review is the stage-1 split review; the base item had no Lean record.

Hypothesis and clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; `Over S` is the category of S-schemes.
  `F G H : Sheaf (Scheme.fppfTopology.over S) (Type u)` imposes precisely the
  big-fppf sheaf hypothesis. The coefficient and scheme morphism universe is u,
  as in the recorded algebraic-space interface; no unrelated universe makes scheme
  tests vacuous. There are no algebraic-space or diagonal assumptions on F or G.
- `f : F.obj ⟶ H.obj`, `g : G.obj ⟶ H.obj` are the two sheaf maps;
  `hH : IsRepresentable (prod.lift (𝟙 H.obj) (𝟙 H.obj))` is the diagonal condition.
- `U V : Over S`, `a : yoneda.obj U ⟶ F.obj`, `b : yoneda.obj V ⟶ G.obj`
  give the atlases. `hae`, `has`, `hbe`, `hbs` use the dependency's `IsEtale`
  and `IsSurjective`; each includes representability by scheme tests, so separate
  representability binders would be redundant.
- P is `Limits.pullback f g` and W is `Limits.pullback (a ≫ f) (b ≫ g)` in
  the presheaf category. Presheaf limits are pointwise: their sections are exactly
  compatible pairs up to the standard projection-preserving identification. We
  retain Mathlib's chosen pullback instead of defining a second fibre-product notion.
- The first existential provides D, `e : h_D ≅ W`, and `p : D ⟶ prod U V`.
  The product in Over S is the scheme U ×_S V. Two equations identify the maps
  to U and V. `IsPullback` states that h_D is the pullback of the diagonal of H
  along the specified natural transformation h_(U ×_S V) → H × H. Thus D is the
  scheme supplied by that very diagonal test, not merely an unrelated representing
  scheme. The H-map is forced by f a on the U component, exactly as in proof step 2.
- The canonical map w is the actual `Limits.pullback.map` with components a, b
  and identity on H; its data contain no postponed proof or arbitrary choice.
  The three following conjuncts state `IsRepresentable w`, `IsEtale w`,
  `IsSurjective w` using the recorded scheme-test definitions.
- `∀ T t A B α β qA qB` and the two `IsPullback` premises range over every
  test t : h_T → P and every choice of representing A, B, including their maps
  to T and their lifts to U, V. Their bottom maps are exactly t followed by the
  F and G projections; no extra properties of these representing choices are assumed.
- The final existential gives the inverse orientation of the node's isomorphism:
  `h_(A ×_T B) ≅ h_T ×_P W`. Inversion gives the displayed orientation in the
  node. The first equation says it lies over h_T with projection pr_B followed
  by β. The next two say that its U and V components are exactly the chosen
  lifts qA and qB after the two fibre-product projections. Those equations specify
  the canonical pair-of-lifts comparison, not an arbitrary natural isomorphism.
- `Etale (Limits.pullback.snd α β).left`, `Surjective` of that arrow, and the
  corresponding two clauses for β.left assert exactly the two surjective étale
  arrows A ×_T B → B → T. The composite is the scheme projection by the first
  equation. Composition permanence supplies its properties, as stated in the proof.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, `.map`; for the scheme and
  presheaf fibre products and the atlas map. `Mathlib.AlgebraicGeometry.Pullbacks`
  provides scheme pullbacks, with slice products giving U ×_S V.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  the actual locally ringed-space scheme and morphism structures.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`,
  `Scheme.fppfTopology`; `GrothendieckTopology.over` from
  `Mathlib.CategoryTheory.Sites.Over` gives the big slice site. These are publicly
  exposed by the imported algebraic-space module.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`:
  `AlgebraicGeometry.AlgebraicSpace.IsRepresentableWith`, `IsRepresentable`,
  `IsEtale`, `IsSurjective`. Their full signatures and docstrings were read;
  they encode actual scheme-valued presheaf pullback squares.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`, together with the same
  module's Mathlib Sheaf imports; the site/sheaf component is used here and no
  cohomology clause is needed. This module is publicly imported by AlgebraicSpace.
- Proof imports: `CategoryTheory.Yoneda.fullyFaithful` in
  `Mathlib.CategoryTheory.Yoneda`; the base-change and composition precoverage
  instances in `Mathlib.AlgebraicGeometry.Sites.MorphismProperty`; the Etale
  permanence instances in `Mathlib.AlgebraicGeometry.Morphisms.Etale` and
  surjective pullback instances in `Mathlib.AlgebraicGeometry.PullbackCarrier`.
  These are the recorded Mathlib matches of all three proof-only dependency nodes.

Source and edge cases: read Stacks spaces.tex, Tag 04T9, the whole lemma and its
last atlas paragraph. Empty T is included; a representing A or B over empty T is
empty, so both projections have the asserted properties. Empty F or G imposes no
nonemptiness assumption; tests exist only when a compatible map t exists. Identity
atlases give the usual identity comparison. Distinct lifts are not identified,
so neither mono nor injectivity is tacitly imposed. There are no separatedness,
quasi-compactness, finite-type or finite-index assumptions. Arbitrary representing
choices A, B are retained, and all isomorphism projection equations preserve them.
No STATEMENT-DISPUTED issue was found.

Searches for an existing statement (all through the authorized search wrapper):

- LeanFinder: "For representable surjective etale atlases U to F and V to G and
  a sheaf H with representable diagonal, U fibre product over H V is a scheme
  atlas of F fibre product over H G with scheme tests A times over T B".
  Eight hits: Scheme etale pullbacks, scheme HasPullback/HasPullbacks,
  openCoverOfLeftRight, Surjective.instFstScheme, forget comparison surjectivity,
  and left_affine_comp_pullback_hasPullback. None states this sheaf atlas test.
- Loogle: `"AlgebraicSpace", "pullback"`: zero hits.
- Mathlib grep: `atlas.*pullback|pullback.*atlas|fibreProductAtlas|fiberProductAtlas`:
  one unrelated fibre-bundle trivialization-atlas hit.
- Project rg in lean/WeilConjectures and lean/Sheaf for the item id,
  fibre/fiber product atlas names, representable diagonal and atlas scheme tests:
  no exact statement. Read AlgebraicSpaceFibreProductsEtaleCovers.lean: its
  `fibreProduct_isAlgebraicSpace` requires F, G, H to be algebraic spaces and
  does not state these scheme-test identifications. It is also the parent node
  whose proof uses this item, so cannot substitute for this statement.
  No duplicate declaration names for either new declaration were found.

Validation: prescribed scompile.py checked the file in module mode, both as a
sandbox and under its public module path, cleanly. The initial namespace collision
with AlgebraicSpace.pullback was repaired by spelling every categorical pullback
`Limits.pullback`. No instance, universe or mathematical hypothesis was changed.

## Second reading by Q73

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
