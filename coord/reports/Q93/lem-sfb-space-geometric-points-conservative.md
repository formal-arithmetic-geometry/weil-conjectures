## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceGeometricPointsConservative` states every
clause of lem-sfb-space-geometric-points-conservative. All five theorem proofs are
`sorry`; every definition contains actual data. No natural-language statement is
changed. No new node or dependency-module repair is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; the spaces are `X Y : AlgebraicSpace S`.
  These are exactly the recorded scheme and algebraic-space definitions, with no
  scheme, quasi-compactness, separation or Noetherian restriction on a space.
- Universes are explicitly `u w`. Schemes and algebraically closed fields are in
  the geometric universe `u`. Set sheaves and colimits are in
  `Type (max (u + 1) w)`, which contains the neighbourhood category's objects.
  This is the size convention, with no equality of independent universes imposed.
- A geometric point is `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]`, its base morphism
  `b : Spec (.of Ω) ⟶ S`, and `x : yoneda.obj (Over.mk b) ⟶ X.obj.obj`.
  The natural transformation is precisely a map from that spectrum to X as a
  sheaf, retaining the compatible base structure.
- Pointed neighbourhoods and their arrows are the existing `X.PointedEtale x`,
  a `StructuredArrow` category of lifts to representable étale scheme charts.
  `X.pointedEtaleForget x` is the published forgetful functor; no second category
  is defined. `pointedSetStalk` composes restriction to its opposite with `colim`.
  On morphisms it uses the colimit functor's map. `pointedSetGerm` is `colimit.ι`.
- `pointedSetStalk_isPoint` states existence of a right adjoint D and the actual
  adjunction `Nonempty (X.pointedSetStalk x ⊣ D)`, together with
  `PreservesFiniteLimits (X.pointedSetStalk x)`. This is exactly a topos point with
  this inverse image, with the ring structures omitted as instructed in the node.
  It does not assume the point or its exactness as extra input.
- `geometricStalk_mono_epi_iso_iff` states all three iff clauses, using `Mono`,
  `Epi`, `IsIso` and respectively `Function.Injective`, `Function.Surjective`,
  `Function.Bijective` of the actual stalk map. Surjective means locally
  surjective sheaves (epimorphisms), not sectionwise surjectivity.
- A general space morphism is `f : X ⟶ Y`. `smallEtaleMorphism f` uses
  `enlargedSmallDirectImage_geometric`: its direct image is the actual published
  evaluation-on-fibre-products functor, transported by `enlargedSetEquivalence`.
  Its inverse image is determined by this right adjoint and the adjunction, up to
  the unique adjunction-compatible isomorphism. This choice is consequently a
  universal-property choice, not a choice of an unconstrained functor or map.
- `geometricStalk_inverseImage` states the natural isomorphism of the two functors
  `(smallEtaleMorphism f).inverse ⋙ X.pointedSetStalk x` and
  `Y.pointedSetStalk (x ≫ f.hom.hom)`. It is specified uniquely by
  `IsGeometricStalkComparison`: every germ of the local unit maps to the original
  target germ. The local unit is constructed in `inverseImageChartSection` using
  the published adjunction, enlarged chart lift, and restriction counit. Thus the
  theorem asserts the canonical comparison, not just existence of an arbitrary
  natural isomorphism. This identifies the inverse images of the composed points;
  the right adjoints then agree by adjunction uniqueness.
- The finite-product equation in that theorem uses `piComparison` and
  `Limits.Pi.map` for every `F : Fin n → Sheaf ...`, including different sorts.
  Combined with the naturality already carried by the natural isomorphism, it
  commutes with each operation `∏ᶜ F ⟶ G`. Hence it states compatibility with
  algebraic operations, including the empty product for constants and mixed
  products for scalar actions, not only addition or operations on one sort.
- `geometricStructureSets` has exactly the original regular functions as its
  presheaf, with the forgetful functor and coefficient `ULift`. The named theorem
  `geometricStructureSets_isSheaf` is its sole postponed proof obligation. Its
  docstring gives the matching-family proof. No ring or functor data are sorry.
- `IsGeometricStructuralMap` specifies the structure map on every commuting pair
  of scheme charts: it sends the local inverse-image section of r to the ordinary
  `Scheme.Γ.map a.left.op` applied to r. `geometricStalk_structureMap` asserts
  existence and uniqueness of this map, plus the explicit formula for its stalk
  map after the inverse of the canonical stalk comparison. This is the canonical
  ring-stalk map. Its compatibility with ring operations follows from the
  preceding finite-product/naturality formula and its prescribed chart formula,
  since ordinary pullbacks of regular functions preserve 0, 1, + and multiplication.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  actual locally ringed-space schemes and their morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `etaleTopology`, `structurePresheaf`, `structureSheaf`; definitions and full
  signatures read. The structure presheaf really is `etaleForget.op ⋙ Scheme.Γ`
  followed by forgetting commutativity.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbelianStalk`: `PointedEtale` and
  `pointedEtaleForget`; full declaration/docstring read. Its abelian stalk has
  different coefficients; only its existing neighbourhood category is reused.
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`: `GeometricMorphism`; its four
  fields are inverse, direct, adjunction and finite-limit preservation.
- `Sheaf.AlgebraicGeometry.AtlasEtaleRestriction`, publicly importing
  `SmallEnlargedEtaleModules` and `EnlargedEtaleRingedSite`:
  `enlargedSmallDirectImage_geometric`, `enlargedSmallDirectImage`,
  `enlargedSetEquivalence`, `enlargedChartLift`. Read their full signatures and
  docstrings, including the arbitrary coefficient universe. This interface is
  the canonical general space morphism rather than a scheme-only restriction.
- `Sheaf.CategoryTheory.RingedToposMorphism`: its full definition and docstring
  were read. The point clause uses exactly its adjunction/left-exactness part,
  omitting ring structures as the node requests. The separate published
  `GeometricMorphism` is the interface for that part at the required universes.
- The size convention has no declaration: the explicit universe choices render
  it. The available proof input `Scheme.exists_fac_of_etale_of_isSepClosed`
  (`Mathlib.AlgebraicGeometry.Sites.EtalePoint`) is imported privately.
  Three further proof prerequisites have no Lean record in the read DAG:
  lem-sfb-space-etale-conservative-geometric-points,
  lem-sfb-space-etale-pullback-chart-comparison, and
  lem-sfb-space-change-base-to-integers. They are proof dependencies only; no
  statement object needs them. Their roles are explained in the theorem
  docstrings, including the direct double-colimit argument available for 04K2.

Statement dependencies gain only three already-landed nodes: the pointed
neighbourhood definition, the unringed geometric-morphism definition, and the
published enlarged ringed-site model. Original dependencies and proof dependencies
are retained. The item owns the helper declarations for its own stalk, inverse-image
comparison and structure-map clauses, all listed in `lean.declarations`.

Sources read: `spaces-properties.tex`, definition-stalk and the discussion before
04K0; 04K0 (lemma-stalk-gives-point); 04K2(4) and its double-colimit proof; 04K5 and
its atlas reduction. The last sentence of 04K5 prints S where X is intended; the
node already explicitly handles that typo. The current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
was checked; this supporting stalk result is not its unit statement.

Edge cases checked before writing:

- Empty space: the conservative iff clauses quantify over an empty geometric
  point family and assert all maps are mono/epi/iso, as in its terminal sheaf topos.
  No existence of a geometric point is imposed on the conservative theorem.
- Empty lift sets in the point's right adjoint: their function sets are singleton,
  and the gluing/adjunction construction still applies.
- Empty finite product (`n = 0`) is included, giving compatibility with constants.
- Arbitrary base S, arbitrary f, identity f, and arbitrary algebraically closed
  Ω in the scheme universe are included. No field extension or separability
  restriction is silently imposed. The comparison always uses the same Ω.
- Mixed products, zero rings and zero module structures introduce no exclusion;
  the comparison depends on finite products, not nonzero coefficients.
- The local compatibility conditions require both the triangle over Y and the
  equality of geometric lifts. They are actual pointed-chart conditions and are
  not an arbitrary map substituted for the canonical comparison.

Searches (all performed using the prescribed msearch wrapper and read-only rg):

- LeanFinder: "Geometric stalks on an algebraic space small etale topos define
  points detect monomorphisms epimorphisms and commute with inverse image".
  Eight hits: ordinary SheafedSpace mono/epi/ext lemmas, `stalkwise`, scheme
  `Scheme.Etale`, its forgetful functor, and `Scheme.smallEtaleTopology`.
  None states the algebraic-space result.
- Loogle: `CategoryTheory.GrothendieckTopology.Point`. Twelve hits: abstract site
  point, fiber, finite-limit preservation and presheaf-fiber constructions. They
  do not construct this geometric point or its canonical space comparison.
- LeanSearch: "Geometric stalk functor of small etale site algebraic space is
  left exact conservative and commutes with inverse image". Eight hits: ordinary
  topological stalk facts, scheme small étale topology and scheme stalk maps.
  No match for the complete statement.
- Mathlib grep through msearch: `AlgebraicSpace` on all Mathlib: zero hits.
  `AlgebraicSpace|geometricPoint|sheafFiber` in CategoryTheory/Sites: 25 hits,
  generic skyscraper, site-point conservativity, comap, monoidal and presheaf-fiber
  APIs; not the algebraic-space realization.
- rg in `lean/WeilConjectures` and in its AlgebraicGeometry directory for
  `AlgebraicSpace`, `PointedEtale`, geometric-stalk names and the item id:
  only scheme geometric-stalk constructions; no declaration for this item.
- rg in `lean/Sheaf`: the existing pointed neighbourhood category and abelian
  stalk were found and reused. `SpacePointedStalkData` packages normalized ring
  and module stalk presentations, and `SingleComplex.StalkModel` uses the affine
  basis and module coefficients; neither is a set-sheaf point or the current
  comparison theorem. Exact proposed declaration names are absent.
- Checked `dag/lean_names_upstream.json` and the recorded dependency modules;
  no exact existing declaration was found. The example CompactObject Sheaf
  module is withdrawn; its node points to the upstream identical definition.

Validation: scompile.py compiled the delivered file in both sandbox and actual
library-module mode without errors or warnings. An initial nested sheafCompose
attempt exposed unresolved size constraints in the ring-forgetful sheaf instance;
this was repaired by the explicit regular-function presheaf and its named sheaf
condition, preserving the original ring data and the general coefficient universe.
No local or global library build was run. There is no statement dispute or source
correction. The mandatory dry run and delivery follow this report.

## Second reading by Q93

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
