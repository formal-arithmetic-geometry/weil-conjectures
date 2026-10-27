## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleGeometricStalksConservative` states
`AlgebraicGeometry.AlgebraicSpace.etaleGeometricStalks_conservative`, with one
`sorry`. The H2 repair uses the independently landed set-stalk definition module. The mathematical statement of the item is unchanged.
The published construction `pointedSetStalk` now belongs to its own landed definition node. The existing
`geometricStalk_mono_epi_iso_iff` is only the three detection tests; it does not state
all-small-colimit preservation, equality detection, or the explicit empty-space
clause. Thus it is not an exact existing declaration for the whole item.

Clause-by-clause correspondence:

- Size convention: explicit `universe u w`; schemes and fields have universe `u`,
  while set coefficients have universe `max (u + 1) w`. The pointed category has
  objects in `Type (u + 1)` and arrows in `Type u`, so its colimits exist in this
  containing universe. No equality between site object and arrow universes is assumed.
- Base and algebraic space: `{S : Scheme.{u}} (X : AlgebraicSpace S)` uses the
  recorded fppf-sheaf definition with representable diagonal and an étale
  surjective scheme atlas. No separatedness, finiteness, or nonemptiness is assumed.
- Every geometric point: each test binds `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]`,
  `(b : Spec (.of Ω) ⟶ S)` and
  `(x : yoneda.obj (Over.mk b) ⟶ X.obj.obj)`. By Yoneda this is precisely a
  morphism Spec Ω → X over S. Both b and x are quantified, so no geometric point
  or structural map is fixed or omitted.
- Colimit construction: `X.pointedSetStalk x` is the existing definition in
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceSetStalk`: forget the sheaf,
  precompose with `(X.pointedEtaleForget x).op`, and apply `colim` in sets.
  `PointedEtale` has actual étale scheme charts and lift-preserving arrows.
  Thus its value is the specified colimit of F(U), and its map is the colimit map
  induced by the sheaf morphism. `pointedSetGerm` is the existing colimit cocone.
- Finite limits: the first conjunct asserts
  `PreservesFiniteLimits (X.pointedSetStalk.{u, w} x)` for every geometric point.
  This includes the empty limit diagram.
- All small colimits: the same conjunct asserts
  `PreservesColimitsOfSize.{max (u + 1) w, max (u + 1) w}` of that functor.
  This concerns colimit cocones in the sheaf category, not objectwise presheaf
  colimits. Both shape universes range over the fixed containing universe.
- Monomorphisms: for every F, G and α, `Mono α ↔ ∀ Ω ... b x,
  Function.Injective ((X.pointedSetStalk x).map α)`.
- Epimorphisms: the next equivalence uses `Epi α` and `Function.Surjective` on
  the same stalk map. It does not demand surjectivity on section sets.
- Isomorphisms: the third equivalence uses `IsIso α` and `Function.Bijective`
  on the same stalk map. Both implications of all three tests are present.
- Equality detection: for every pair `α β : F ⟶ G`, equality of their mapped
  morphisms for every geometric point implies `α = β`.
- Empty space: the final conjunct uses
  `∀ U : X.EtaleSite, IsEmpty ((X.etaleForget).obj U)` and concludes
  `∀ F G, Nonempty (F ≅ G)`. This is precisely the empty-space case:
  every chart over the empty space is empty; conversely the surjective scheme
  atlas is itself such a chart, so if all charts are empty the space is empty.
  The sheaf category is already nonempty (it has its terminal singleton sheaf).
  The equality and isomorphism tests above also apply without any nonemptiness
  assumption. In particular all parallel maps agree in this case.

Dependency declarations read and used:

- `def-weil-size-convention` has a convention-only Lean record: its universes
  are expressed explicitly as above, not as an invented Lean object.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace`, `EtaleSite`, `etaleForget`,
  `etalePrecoverage`, `etaleTopology`. Their full definitions were read.
- The landed definition node, rather than the item directly, cites
  `def-sfb-space-pointed-etale-abelian-stalk`, module
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbelianStalk`: `PointedEtale` and
  `pointedEtaleForget`. The abelian coefficient stalk is not used as a set stalk.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSetStalk`:
  `pointedSetStalk` and `pointedSetGerm`, owned by the independently landed definition node.
  The item no longer imports the downstream conservative-points module.
- Proof imports follow the recorded nodes: `ChartwiseEtalePermanence`
  (`chartwise_etale_permanence`), Mathlib pullback and colimit interfaces,
  `SiteCoveringAxioms`, `AlgebraicClosure`, the geometric lifting result
  `Scheme.exists_fac_of_etale_of_isSepClosed`, `Types.FilteredColimit`,
  `filtered_colim_preservesFiniteLimits`,
  `Adjunction.leftAdjoint_preservesColimits`,
  `Sheaf.isLocallySurjective_iff_epi`, and `Sheaf.createsLimitsOfShape`.
  `lem-sfb-space-pointed-etale-neighbourhoods-cofiltered` has no Lean record at
  the read snapshot, so it contributes no proof import. Its full proof remains
  cited in the theorem docstring. No new proof obligation is needed to form
  the existing colimit functor.

Import graph after H2 repair: AlgebraicSpaceAbelianStalk → AlgebraicSpaceSetStalk
→ EtaleGeometricStalksConservative. The downstream SpaceGeometricPointsConservative
publicly imports the set-stalk definition module and has this item as a proof dependency.
The item imports no downstream theorem module, and the DAG remains acyclic.

Edge cases checked before writing: empty X (empty covers force singleton sections),
empty scheme charts, empty finite-limit diagrams, empty colimit diagrams,
non-surjectivity of section maps for an epimorphism, arbitrary characteristic,
and arbitrary coefficient universe w. No terminal chart of X is assumed: X itself
need not be a scheme. Fields and their algebraic closures can both be taken in
universe u. No hollow data, arbitrary point functor, right adjoint, or canonical map
is introduced as an assumption. No statement correction or dispute is necessary.

Searches made for an exact existing statement and construction:

- `msearch.py`, leanfinder:
  "Geometric stalks on the small etale site of an algebraic space detect
  monomorphisms epimorphisms and isomorphisms". Eight hits about ordinary
  scheme/sheafed-space stalks, including `SheafedSpace.mono_of_base_injective_of_stalk_epi`
  and `isIso_iff_stalk_iso`; none is this étale-topos assertion.
- `msearch.py`, leansearch:
  "Geometric stalk functor on algebraic spaces preserves finite limits and colimits".
  Eight hits including topological `TopCat.Presheaf.stalkFunctor` and generic
  sheaf pullback preservation, none the algebraic-space assertion.
- `msearch.py`, loogle:
  "CategoryTheory.GrothendieckTopology.Point, CategoryTheory.Functor.PreservesFiniteLimits".
  No hits; the latter suggested identifier is unknown. Corrected query
  "CategoryTheory.Limits.PreservesFiniteLimits" returned the finite-limit class
  and its generic consequences, not a geometric-stalk theorem.
- `msearch.py`, grep:
  "pointedSetStalk|PointedEtale|Point.stalkFunctor" under CategoryTheory/Sites.
  No Mathlib hits for that regular expression.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  geometric-point, pointed étale and geometric-stalk names. Found the existing
  `AlgebraicSpaceAbelianStalk` and newly landed `SpaceGeometricPointsConservative`
  modules; read both in full and reused their constructions. The exact item id
  does not occur in the upstream WeilConjectures source. Exact new declaration
  name `etaleGeometricStalks_conservative` occurs in none of Mathlib,
  WeilConjectures or Sheaf at the read snapshot.

Source checked locally: spaces-properties.tex, definition-stalk (04JY),
lemma-stalk-gives-point (04K0), and theorem-exactness-stalks (04K5), including
its scheme-atlas reduction. The proof docstring preserves all ten accepted
proof steps, including the skyscraper adjunction and empty covering argument.

## Return repair H2

The returned head was aea8c34a8f27. The item formerly imported the downstream
SpaceGeometricPointsConservative to access two plain definitions. Its proof depends
on this item, so that ownership was invalid. The repaired item imports
Sheaf.AlgebraicGeometry.AlgebraicSpaceSetStalk and adds only
`def-sfb-space-pointed-set-stalk` to its original stmt_deps. The former direct
addition of `def-sfb-space-pointed-etale-abelian-stalk` is removed; it enters through
the set-stalk definition node. The theorem signature and all ten proof steps remain
unchanged. No statement correction or dispute is necessary.

Read the current server modules with scompile.py --source and the live definition
and consumer node records. The independent definition owns pointedSetStalk and
pointedSetGerm; the consumer no longer declares them and cites the definition node.
Their signatures and bodies remain identical to the former Q93 definitions.

## Maintenance resolution, 2026-10-24


The repeated downstream-ownership refusal was resolved on server sheaf-dag in
commit 6e7012a34c11da3d54605a9b5eeade06e600de0e. Maintenance committed the independent
set-stalk definition node/module and the downstream consumer extraction directly,
under the merge lock, without changing delivery or landing gates. The two moved
definitions retain exactly their former signatures and bodies; only their blueprint
ownership changed. The consumer's node now cites the definition and no longer
claims the moved declarations. Its private proof import of this still-undelivered
item is left to the normal maintainer proof-import cycle after this delivery lands.

Validation of that maintenance commit: tools/lean_file.sh, one file at a time,
60 s limit: AlgebraicSpaceSetStalk 12.8 s; SpaceGeometricPointsConservative 9.4 s,
no warnings or errors. Incremental DAG checks of both nodes passed. Registered
interface landing 20261024T124509-L-316186-766 for normal global-build verification.

The four now-landed definition/consumer files are retained as .maint-NV-1792844966.bak
files and removed from the pending delivery globs. This pending packet contains
only the repaired item module/node and this report. Earlier report sections describe
the former combined packet and historical refusals; they are superseded by this
resolution. Rebase on current main, run the dry run, then deliver the item normally.

## Final worker validation

The pending delivery contains only the item module, its node copy and this report.
There are no new nodes or dependency modules in this packet: the independent
set-stalk definition and consumer adaptation have landed in the maintenance commit.
The earlier gate ownership refusal therefore no longer applies. The sole module
is checked using scompile.py, followed by the prescribed deliver2.py dry run and
delivery. The module retains explicit universes and autoImplicit false, a single
named theorem with sorry, and no definition with postponed data.

The sole delivered module passed scompile.py with no errors or unexpected warnings.
The final dry run passed server preflight and compilation (reviewable dry-run commit
e54ecb5ea9f). The checked signature matches lean.statement verbatim; maximum line
width is at most 100; only the named theorem uses sorry. The packet contains three
files: the item module, item node and this report.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
