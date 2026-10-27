## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleGeometricPointSpecifiedLift` states
`AlgebraicGeometry.AlgebraicSpace.exists_etale_geometricPoint_specified_lift`.
Its only theorem proof is `sorry`. No definitions or additional theorems are introduced.
The source is Stacks Project, Properties of Spaces, Tag 05VN,
`lemma-geometric-lift-to-usual`, with the common-field point construction of Tag 03H4,
`lemma-points-cartesian`. I read these passages and the point-class definition and
relation preceding Tag 03BU in `literature/stacks-project/spaces-properties.tex`.

Hypothesis and conclusion correspondence:

- The base scheme is `{S : Scheme.{u}}`. The arbitrary algebraic spaces over it are
  `{X U : AlgebraicSpace S}`. These are the recorded fppf sheaves with representable
  diagonal and an étale surjective atlas, rather than schemes substituted for spaces.
- The map is `(e : U ⟶ X)`. Its underlying natural transformation is `e.hom.hom`.
  `(he : IsEtale e.hom.hom)` is precisely the recorded representable-étale property:
  every scheme test has a scheme representing its pullback, with étale projection.
  No surjectivity, quasi-compactness, separation or finiteness hypothesis is added.
- The algebraically closed field is `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`.
  `(s : Spec (.of Ω) ⟶ S)` records the geometric point's structural map to the base.
  It is arbitrary; this is data already implicit in a geometric point of an S-space.
- `(xbar : yoneda.obj (Over.mk s) ⟶ X.obj.obj)` is the geometric point as a
  natural transformation from the representable S-scheme. By Yoneda it is the
  same object as a map `Spec Ω → X`. Its image x is written directly as
  `Quot.mk _ ⟨Ω, s, yonedaEquiv xbar⟩`, without a redundant binder for x.
- `(u : Point U.obj.obj)` is the specified source point class, using the existing
  quotient by common field extension. The hypothesis
  `hu : mapPoint e.hom.hom u = Quot.mk _ ⟨Ω, s, yonedaEquiv xbar⟩`
  says exactly e(u) = x. `mapPoint` is the already implemented quotient map induced
  by applying the natural transformation to representatives.
- `∃ ubar : yoneda.obj (Over.mk s) ⟶ U.obj.obj` gives the required geometric
  point with the same Ω and the same structural map s. Its first conjunct,
  `Quot.mk _ ⟨Ω, s, yonedaEquiv ubar⟩ = u`, requires its image to be the
  specified source class. Its second conjunct, `ubar ≫ e.hom.hom = xbar`, is
  precisely e composed with ubar equals xbar (Lean writes composition left to right).
- The same-field conclusion is built into the existential type. There is no
  existential replacement field or extension in the conclusion. All variables and
  the universe are explicitly bound, with `autoImplicit false`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (def-pc-scheme); inherited publicly through the imports.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace.IsEtale` and `IsRepresentableWith`
  (def-trf-algebraic-space). I read their full signatures and docstrings.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`
  (def-weil-etale-morphism), used by the definition of `IsEtale`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`:
  `PointRepresentative`, `PointRepresentative.Rel`, `Point`
  (def-a1-algebraic-space-point-classes). Their construction exactly supplies the
  field-valued equivalence classes specified in the item's text.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`:
  `AlgebraicGeometry.AlgebraicSpace.mapPoint` (def-sfb-proper-curve-moduli).
  I read its full signature, docstring and quotient implementation; it uses the
  existing `PointRepresentative.map` from `AlgebraicSpacePointTopology`.
  The theorem uses only this canonical map, without any proper-curve hypotheses.
- Proof-only import `Mathlib.AlgebraicGeometry.Sites.EtalePoint`:
  `AlgebraicGeometry.Scheme.exists_fac_of_etale_of_isSepClosed`
  (lem-weil-pbc-etale-cover-geometric-point-lift, recorded Mathlib match). I read
  its complete prescribed-point signature, including both factorization and
  `l default = x`, and its proof. The declaration has no separate docstring.
  The four-step proof in the new theorem's docstring follows the DAG proof and
  explains the representing scheme, common extension, prescribed-point scheme
  lift and final composite.

The item's original mathematical statement, proof and proof dependencies are
unchanged. Its statement dependencies gain the already landed definition nodes
`def-a1-algebraic-space-point-classes` and `def-sfb-proper-curve-moduli`, to cite
exactly the existing quotient and its induced map. This is the standing
STMT_DEPS MAY GAIN LANDED NODES rule. There are no new nodes, dependency repairs,
statement corrections or disputed statements.

Edge cases checked before writing: if U is empty there is no u, so no impossible
lift is required; if X is empty there is no geometric point. Identity maps admit
xbar itself and its point class. A disjoint union of copies of Spec Ω allows any
specified component and does not force uniqueness. Non-surjective étale maps
are covered whenever u exists above x; non-quasi-compact maps are not excluded.
Positive characteristic and arbitrary algebraically closed fields are allowed.
The field and test schemes use the same arbitrary universe u as the recorded
big-site algebraic-space and point-class definitions; no independent smaller
universe or additional equality of universes is imposed. Naturality over S forces
the lift to have the original s, as the source statement requires.

Searches for an exact existing statement, all made with the prescribed tools:

- `msearch.py ... leanfinder`: "For an etale morphism of algebraic spaces every
  geometric point lifts over a specified point with the same algebraically closed
  field". Eight hits, all scheme étale definitions, instances or forgetful functors;
  no algebraic-space prescribed-point lift.
- `msearch.py ... loogle`: `AlgebraicGeometry.AlgebraicSpace, IsAlgClosed`.
  Zero hits; service does not know the project's AlgebraicSpace identifier.
- `msearch.py ... leansearch`: "An etale morphism of algebraic spaces lifts a
  geometric point over a specified underlying point without extending its
  algebraically closed field". Eight hits concerning scheme or ring étaleness;
  no exact match.
- `msearch.py ... grep`: `geometric.*lift|lift.*geometric`, subdirectory
  `AlgebraicGeometry`. Zero hits in that search.
- Direct `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and specifically the
  algebraic-space modules for geometric lifts and specified lifts found references
  to the current node in consumer proof docstrings, but no declaration for it.
  `grep -rn` for the item id in `lean/WeilConjectures` returned no match.
- Direct searches for `PointRepresentative`, `Point`, quotient maps and `mapPoint`
  found the existing point-class, point-topology and proper-curve modules, which
  are reused. Searches in `dag/nodes` identified their owning definition nodes.
  The proposed theorem name and module name have no match in Mathlib,
  `lean/WeilConjectures`, `lean/Sheaf` or `dag/lean_names_upstream.json`.

Validation: `scompile.py Q125 lem-sfb-etale-geometric-point-specified-lift` compiled
this module against the live server library in both sandbox and library modes,
1.6 seconds each, with no errors or warnings. The delivery dry run and final push
are performed after this report is written.

## Second reading by Q125

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
