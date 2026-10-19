## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleToposPointsGeometric` states
`AlgebraicGeometry.Scheme.etaleToposPoint_isGeometric`, with its proof `sorry`.
It uses the node's explicitly equivalent formulation by a natural isomorphism of
inverse-image functors. No definition, helper, dependency repair, or statement correction
is needed. The source was read in `literature/stacks-project/etale-cohomology.tex`,
the entire lemma `lemma-points-small-etale-site` (Tag 04HU) and
`lemma-stalk-gives-point` (Tag 04FM), together with `definition-stalk`.

Hypotheses and clauses:

- An arbitrary scheme S is `(S : Scheme.{u})`, with no finiteness, separation,
  nonemptiness, connectedness, characteristic, or affine hypothesis.
- Its small etale topos is `Sheaf S.smallEtaleTopology (Type (u + 1))`.
  The topology is the recorded Mathlib small etale topology on `S.Etale`, including
  arbitrary jointly surjective covers, not a finite-cover topology.
- A point from sets is
  `(p : GeometricMorphism (Type (u + 1))
    (Sheaf S.smallEtaleTopology (Type (u + 1))))`.
  The recorded structure supplies both functors, their adjunction, and preservation
  of finite limits by `p.inverse`. It is an arbitrary topos point, not merely one
  already constructed from a site fibre functor or a geometric point.
- Existence of a geometric point is
  `∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω) (s : Spec (.of Ω) ⟶ S), ...`.
  Thus the field and all its structure are existential, not extra assumptions.
  `IsAlgClosed` is precisely the recorded algebraically closed field condition.
- The equivalently stated natural identification of inverse images is
  `Nonempty (p.inverse ≅ (pointSmallEtale s).sheafFiber (A := Type (u + 1)))`.
  This is one natural isomorphism on the entire sheaf category, not merely a family
  of bijections with no naturality. No canonical choice of the geometric point or
  of this isomorphism is asserted.
- The displayed stalk colimit is exactly the existing `sheafFiber`: in
  `Mathlib.CategoryTheory.Sites.Point.Basic`, `sheafFiber` is
  `sheafToPresheaf ⋙ presheafFiber`, and `presheafFiber` is whiskering by
  `(CategoryOfElements.π Φ.fiber).op`, followed by `colim`.
  For `Φ = pointSmallEtale s`, `Φ.fiber` is
  `Etale.forget S ⋙ coyoneda.obj (op (Over.mk s))`. Its category of elements consists
  of exactly the etale objects with a lift of s, and its arrows are exactly the
  lift-preserving S-morphisms. The opposite is therefore the required index, and
  its diagram is F evaluated on those etale objects, with restriction maps.
- The first formulation, isomorphism of points, is equivalent: by
  `geometricStalkToposPoint` the geometric stalk has the prescribed right adjoint;
  the invertible adjoint mate of the asserted inverse-image isomorphism identifies
  that right adjoint with `p.direct`. This uses the adjunctions, with the direction
  of 2-morphisms fixed by `GeometricMorphism.inverseIso` and `conjugateIsoEquiv`.
- The size convention is explicit: schemes and residue-field algebraic closures
  use u, the etale site's objects use u+1 and its morphisms u, and all coefficient
  sets and stalk colimits use u+1. The neighbourhood category has object universe
  u+1, so its colimit fits in the stated enlarged universe. Choosing the representing
  field in u does not omit a point: the source proof takes an algebraic closure of
  the residue field of the recovered point. No equality of object and morphism
  universes is assumed and no smallness class is added as a hypothesis.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`, declaration
  `AlgebraicGeometry.Scheme.smallEtaleTopology`, and
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`, declaration
  `AlgebraicGeometry.Scheme.Etale`. The category and topology are reexported by
  the public import of `Mathlib.AlgebraicGeometry.Sites.EtalePoint`.
- `def-weil-size-convention`: the node is explicitly a metatheoretic convention,
  with no module or declaration. Its role is supplied by the universe assignments
  explained above, rather than a replacement definition.
- `def-trf-geometric-morphism`: `Sheaf.CategoryTheory.Sites.GeometricMorphism`,
  declaration `CategoryTheory.GeometricMorphism` and its fields `inverse`, `direct`,
  `adj`, and `leftExact`; the full structure and the mate declarations were read.
- `def-weil-geometric-point`: `Mathlib.FieldTheory.IsAlgClosed.Basic`, `IsAlgClosed`,
  with the recorded inline field and scheme-morphism encoding; also read
  `AlgebraicGeometry.Scheme.SpecToEquivOfField` in
  `Mathlib.AlgebraicGeometry.ResidueField` for its residue-field interpretation.
- `def-weil-pbc-pointed-etale-neighbourhoods`: its usable `mathlib_match` is
  `CategoryTheory.Functor.Elements`/`categoryOfElements` in
  `Mathlib.CategoryTheory.Elements` applied to the fibre of
  `AlgebraicGeometry.Scheme.pointSmallEtale` in
  `Mathlib.AlgebraicGeometry.Sites.EtalePoint`. These are used inside `sheafFiber`;
  no second pointed-neighbourhood notion is introduced.
- `def-weil-pbc-category-colimit`: `Mathlib.CategoryTheory.Limits.HasLimits`,
  `CategoryTheory.Limits.colimit`, used by `presheafFiber`/`colim`.

The statement dependencies are public imports, directly or through the public Mathlib
etale-point module. Proof-only imports supply the available recorded sober-scheme,
open-image, algebraic-closure, cofiltered-finite-system and actual geometric-stalk-point
results. In particular the existing `geometricStalkToposPoint` in
`Sheaf.AlgebraicGeometry.GeometricStalkToposPoint` is a proof dependency only.
`lem-trf-site-point-reconstruction-sets` and `lem-trf-affine-etale-split-neighbourhood`
have neither a Lean record nor a Mathlib match at the time of reading; their proof-only
imports cannot yet be added. The module's nine proof paragraphs reproduce the node's
nine steps with their named prerequisites, including the affine-base restriction,
coherent compatible choice, independence of refinements, and the nonaffine overlap
argument. No step is silently treated as proved.

Edge cases checked before writing: the empty scheme admits no such point because
its sheaf topos is degenerate and an inverse image preserving both the initial and
terminal objects cannot land in sets; the theorem thus needs no nonempty-S assumption.
Empty geometric fibres occur among etale objects and give empty stalks of their
representables, as permitted. Over an algebraically closed field the usual point is
included, as are separably closed representatives after passage to an algebraic closure.
No nonzero stalk, finite stalk, finite site, or surjective neighbourhood-transition
assumption appears. The empty finite limit is included by the structure's
`PreservesFiniteLimits` field. All characteristics and non-quasi-compact schemes are
included. No node fault or `STATEMENT-DISPUTED` issue was found.

Searches for an existing statement (all through the prescribed `msearch.py` wrapper,
plus source reads and direct repository searches):

- LeanFinder, “Every point of a small etale topos is naturally isomorphic to the
  geometric stalk functor of an algebraically closed field valued point”: eight
  hits about scheme stalks, residue-field maps, and the etale forgetful functor;
  no classification of arbitrary topos points.
- LeanFinder, “Every point of the small etale topos is isomorphic to a geometric
  stalk”: eight hits, including `smallEtaleTopology`, `Etale`, `Etale.forget`, and
  `TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso`; no exact match.
- Loogle, `"pointSmallEtale"`: seven hits constructing the geometric site point,
  describing its fibres and proving conservativity. The full source was read;
  none classifies an arbitrary geometric morphism from sets.
- LeanSearch, “Every abstract point of the small etale topos is represented by a
  geometric point”: eight hits including `smallEtaleTopology`, `etaleTopology`,
  `GrothendieckTopology.Point` and its constructors; no exact match.
- Mathlib grep, `04HU|points.small.etale|pointSmallEtale` under AlgebraicGeometry:
  five hits in `Sites/EtalePoint.lean`, all concerning the constructed point and
  its fibre description, not essential surjectivity onto abstract topos points.
- `rg` in upstream `WeilConjectures` and side `lean/Sheaf` for geometric-point,
  etale-point and `GeometricMorphism` names found the general geometric morphism
  structure, the geometric-stalk-point theorem and existing stalk/coefficient
  applications; none states this classification. Upstream recursive search for
  the exact node id found nothing. The candidate declaration name was searched in
  `dag/lean_names_upstream.json`, Mathlib, upstream and side Lean: no collision.

Validation uses `scompile.py` for the single delivered file, then the prescribed
`deliver2.py --no-push` preflight and per-file compilation before delivery.

## Second reading by Q60

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
