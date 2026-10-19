## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineAtlasOpenCover` states
`AlgebraicGeometry.AlgebraicSpace.exists_affine_atlas_open_cover`, with its sole proof
`by sorry`. It follows Stacks Project, Properties of Spaces, Tag 03FY,
`lemma-union-of-quasi-compact`, including the last affine-base clause. I read the
source lemma and proof, together with the preceding Tag 03FX affine-chart construction.
No definition, new node, dependency repair, or statement correction is needed.

Hypotheses and clauses, in the order of the node:

- A scheme S: the explicitly universe-bound binder `{S : Scheme.{u}}`.
- An algebraic space X over S: `(X : AlgebraicSpace S)`, using the existing full
  subcategory of fppf sheaves with representable diagonal and a surjective etale atlas.
  There is no Noetherian, separated, quasi-compact, or nonempty hypothesis.
- The size convention: explicit `universe u`, `Scheme.{u}`, `I : Type u`, and
  algebraic spaces on the existing big site with values in `Type u`. An atlas has
  its point set in `Type u`, so that universe suffices for the cover index. The
  field-valued coverage predicate quantifies over fields in that same universe.
- A set-indexed family of algebraic-space open subspaces: the witnesses
  `(I : Type u) (Xi : I → AlgebraicSpace S) (j : ∀ i : I, Xi i ⟶ X)` and
  `IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) (j i).hom.hom`.
  This is exactly representability and an open immersion after every scheme base
  change. Such a map is a monomorphism, so this presents the open subfunctor by its
  inclusion rather than making a separate copy of the subfunctor notion.
- Their field-valued point classes cover X:
  `IsJointlySurjective (fun i : I ↦ (j i).hom.hom)`.
  Its existing definition says that every K-valued representative lifts to some
  member after an extension K → L. This is precisely the node's common-extension
  equivalence: extend a representative of a class in the source to the common
  extension; conversely an extension lift witnesses equality of classes. No
  restriction to rational points, fixed fields, or algebraically closed fields is made.
- An affine S-scheme U_i and a map h_(U_i) → X_i: the witnesses `(U : I → Over S)`
  and `(a : ∀ i : I, yoneda.obj (U i) ⟶ (Xi i).obj.obj)`, and the clause
  `IsAffine (U i).left`.
- Each atlas map is representable, surjective, and etale:
  `IsEtale (a i) ∧ IsSurjective (a i)`. Each of these existing predicates includes
  representability and tests its stated property on all scheme base changes;
  no separate assumption of representability is necessary.
- Each X_i maps into an affine open of S:
  `∃ W : S.Opens, IsAffine W.toScheme ∧
    Nonempty ((Xi i).obj.obj ⟶ yoneda.obj (Over.mk W.ι))`.
  Here W.ι is the actual open-subscheme inclusion. A natural transformation to h_W
  supplies compatible scheme-test factorizations into that open. Since h_S is the
  terminal presheaf on Sch/S, composition with h_W → h_S is necessarily the
  structural map. Thus the required factorization equation is automatic in this
  over-category encoding. The witness is a map to the specified representable h_W,
  not an arbitrary target or an unspecified comparison map.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
  I read their full structure signatures and docstrings in the pinned Mathlib.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `AlgebraicSpace.IsEtale`, and
  `AlgebraicSpace.IsSurjective`; their full definitions were read. The module is
  publicly available through the joint-surjectivity module's public import.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffine`; its
  `Scheme.isBasis_affineOpens` supplies the first proof step.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`:
  `AlgebraicGeometry.AlgebraicSpace.IsJointlySurjective`. I read its full definition,
  docstring, and the node `def-trf-algebraic-space-jointly-surjective-family`, which
  already has a landed Lean record. That existing definition node is added to
  stmt_deps under the rule permitting added landed dependencies. It supplies exactly
  the covering notion already described in the item's statement.
- `def-weil-size-convention` is a metatheoretic convention; the explicit universes
  above implement it rather than introducing a fictitious declaration.

Proof dependencies: the Mathlib affine-basis theorem, `IsOpenImmersion.lift`,
`lift_fac`, `lift_uniq`, `Etale.etale_comp`, `Etale.of_comp`, the open-immersion etale
instance, and `isOpenImmersion_stableUnderBaseChange` were read in source. Their modules
are already public transitive dependencies of the statement imports. The remaining
proof-only node `lem-a1-etale-scheme-map-open-image` has no recorded Lean module in the
repository snapshot, so there is no module for it to import. Its entire role is recorded
in step 3 of the theorem docstring, matching the item's proof; it is not needed to type
the statement. No new postponed theorem was introduced for that proof-only dependency.

Edge cases checked before writing:

- Empty X or an empty atlas: I may be empty; neither `Nonempty I` nor a chart is
  required. The point coverage condition is vacuous exactly when there are no
  field-valued points. Every per-chart condition is then vacuous.
- Empty base S: an algebraic space over the empty base is handled by the same empty
  family; there is no requirement to choose an affine open of S without a chart.
- An empty U_i is allowed (the zero ring's spectrum is affine). Surjectivity then
  forces the corresponding X_i empty, exactly as scheme-test surjectivity should.
- X a scheme: the statement recovers an ordinary cover by affine neighbourhoods,
  possibly with general affine etale atlases for the pieces.
- No restriction on characteristic or the chosen field-valued representative is
  present; extension fields remain in the universe of the big site.
- For a nonaffine base the last clause chooses W separately for each chart. It
  does not require the whole space to map into a single affine open.

Searches for an existing statement (all run for NK and this item):

- `msearch.py leanfinder`, query "Every algebraic space has a Zariski open covering
  by open subspaces admitting affine surjective etale atlases": eight hits, including
  `Scheme.affineCover`, `Scheme.affineBasisCover`, `Scheme.AffineOpenCover`, and
  `Scheme.OpenCover.affineRefinement`. They concern schemes, not algebraic spaces.
- `msearch.py loogle`, query `"AlgebraicSpace", "Cover"`: zero hits.
- `msearch.py leansearch`, query "Every algebraic space is covered by open subspaces
  with affine surjective etale atlases": eight scheme-cover hits, including
  `Scheme.isBasis_affineOpens`; no algebraic-space statement.
- `msearch.py grep`, regex `AlgebraicSpace|affine.*etale.*atlas|etale.*atlas`:
  zero Mathlib hits. A direct rg over Mathlib/AlgebraicGeometry with the same regex
  also found no match.
- Direct rg over the upstream `WeilConjectures` source for that regex and for the
  exact item id: no hits. A full-name search for `exists_affine_atlas_open_cover`
  across Mathlib, upstream, the side library and `dag/lean_names_upstream.json`
  found no existing declaration.
- Direct rg over `lean/Sheaf/AlgebraicGeometry/AlgebraicSpace*.lean` found the
  scheme-test definitions, open-gluing theorem, and existing `IsJointlySurjective`.
  The gluing theorem starts with a supplied open cover and proves algebraicity;
  it does not construct the affine-atlas cover of this item. I reused the coverage
  definition rather than duplicating it.
- DAG search for open subspaces/open subfunctors found this item, the open-image
  lemma, and other open-subspace lemmas, but no separate open-subspace definition
  that needs to replace the existing scheme-test predicate.

Validation: prescribed `scompile.py NK lem-a1-space-affine-atlas-open-cover` compiled
both sandbox and library forms of the delivered file cleanly (1.9 s and 2.0 s,
respectively), with no errors or warnings. All variables and universe levels are
explicitly bound. The single theorem is intentionally unproved at stage 2.
No STATEMENT-DISPUTED issue was found.

## Second reading by NK

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
