## Worker report

Bind `def-sfb-coefficient-map` to the existing declaration
`AlgebraicGeometry.ProEtale.coefficientMap` in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`.
No module is delivered and no theorem or definition is duplicated. Only the item's
`lean` field changes. The source is the current blueprint
`main-20261015/blueprint/sec-proetale-coefficients/sk-prop-sfb-cartesian-coefficients/def-sfb-coefficient-map.md`.
The source names precisely this existing declaration.

Clause-by-clause reading:

- A condensed ring is a ring object in condensed abelian groups. The source section
  binds `{Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}` with
  `[MonObj Λ] [MonObj Λ']`. These are arbitrary ring objects, including
  noncommutative rings; no `IsCommMonObj` hypothesis is used.
- A morphism of condensed rings is `(a : Λ ⟶ Λ') [IsMonHom a]`.
  The abbreviation itself computes the underlying arrow for any sheaf morphism;
  for the ring-object morphism in the node, the supplied structures and
  `Functor.map.instIsMonHom` give precisely the required ring morphism.
- An arbitrary scheme is `(X : Scheme.{u})`. There are no geometric, nonemptiness,
  or finiteness hypotheses.
- The defining equation `a_X := p_X^* a` is the actual body
  `(upperStarFromPoint X).map a`, rather than an arbitrary chosen morphism.
  The recorded `sfbPullbackFromPoint X` is an abbreviation of that same functor.
- The source and target are `condensedRingObj Λ X` and `condensedRingObj Λ' X`.
  In `Basic`, these are `(upperStarFromPoint X).obj Λ` and its primed version,
  definitionally the underlying objects of
  `coefficientRing X (Mon.mk Λ)` and `coefficientRing X (Mon.mk Λ')`.
- It is a ring-object morphism in `Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}`:
  `Functor.map.instIsMonHom` synthesizes `IsMonHom (coefficientMap a X)`.
  Reading Mathlib's `Functor.mapMon` shows its morphism assignment is
  `.mk (F.map f.hom)`, so this is precisely the underlying map of the functor on
  ring objects used in the node's proof paragraph.

Dependency declarations read:

- `sk-def-sfb-condensed-ring` has no `lean` record, but its slopmaster2 audit is
  `closed`. Its recorded declarations in
  `WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap` are
  `Profinite.continuousMapRingSheaf`, `continuousMapRingObj`, and
  `continuousMapRingSheafMap`; the corresponding `Condensed.EllAdic` declarations
  are `padicIntCondensedRing`, `padicCondensedRing`,
  `padicSubfieldCondensedRing`, and `padicIntegersCondensedRing`.
  Their signatures and docstrings were read in the shared framework. They give
  the sheaf/ring-object interpretation; this item allows arbitrary ring objects,
  and requires no additional topological-ring or prime hypothesis.
- `sk-def-sfb-pullback-from-point` records
  `Sheaf.AlgebraicGeometry.ProEtalePointPullback`,
  `AlgebraicGeometry.ProEtale.sfbPullbackFromPoint`. Its body is
  `upperStarFromPoint X`. The right-adjoint alias and full specification were read.
- `sk-def-sfb-pulled-back-coefficients` records
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.coefficientRing`, with `coefficientRing_X`,
  `condensedRingObj`, and `isCommMonObj_condensedRingObj`.
  The object is `(upperStarFromPoint X).mapMon.obj Λ`; Mathlib's
  `Functor.monObjObj` gives unit `ε F ≫ F.map η` and multiplication
  `LaxMonoidal.μ F Λ Λ ≫ F.map μ`.
- The ring-map guarantee is the existing Mathlib declaration
  `CategoryTheory.Functor.map.instIsMonHom` in
  `Mathlib.CategoryTheory.Monoidal.Mon`; the bundled version is
  `CategoryTheory.Functor.mapMon` in that same module.

Edge cases: the universe `u` is arbitrary, with precisely the established site and
`Ab.{u + 1}` convention. Empty schemes and zero ring objects are allowed, since
nothing assumes nonemptiness or a nonzero ring. Identity and arbitrary ring
morphisms use the same functor map. Noncommutative rings are included, because
`MonObj` and `IsMonHom` suffice. No statement correction, new node, dependency
repair, hollow construction, or disputed statement was found.

Searches (2026-10-18; exact wrapper results are also in `searches.jsonl`):

- `msearch.py leanfinder`: “The inverse image of a morphism of condensed rings on
  a scheme pro-etale site is the coefficient change map p_X star a”. Eight hits
  concern structure sheaves and `Spec`, not this coefficient construction.
- `msearch.py loogle`: `CategoryTheory.Functor.mapMon`. Twelve hits include
  `Functor.mapMon`, `mapMon_obj_X`, and generic monoidal constructions. The generic
  functor is the needed mechanism, but does not itself name this pro-etale map.
- `msearch.py leansearch`: “inverse image of a morphism of condensed rings
  coefficient change on a pro-etale scheme”. Eight hits concern scheme maps,
  etale base change, `Subring.comap`, and `CondensedMod.hom_naturality_apply`;
  none is the named construction.
- `msearch.py grep`: `coefficientMap|mapMon_map_hom` in `CategoryTheory`: zero hits.
  Direct reading of Mathlib `CategoryTheory/Monoidal/Mon.lean` found
  `Functor.map.instIsMonHom` and `mapMon`, with the explicit map construction.
- `rg` on the older slopmaster2 `WeilConjectures` tree and on
  `dag/lean_names_upstream.json` found no `coefficientMap`; that checkout predates
  the published framework. Following `coord/pefw-upstream-framework.md`, the exact
  declaration and its section binders were read from the shared
  `lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/ChangeOfCoefficients.lean`.
  `scompile.py --source` confirmed that same published source and definition.
- `rg` on `lean/Sheaf` found other namespaces' ordinary or constant-ring
  coefficient maps and consumers of this upstream map (for example condensed
  Tate twists); these do not require a second definition. The item's blueprint
  source and existing upstream audit both name the exact construction above.

Validation: a scratch consumer, excluded from the delivery, imports the existing
map and the recorded point-pullback module with `autoImplicit false` and explicit
universe and variable binders. It checks both coefficient-ring endpoints,
synthesizes `IsMonHom (coefficientMap a X)`, and checks the defining equality with
`(sfbPullbackFromPoint X).map a` by definitional reduction. An additional check
expanding the entire bundled `mapMon` equality reached Lean's heartbeat limit;
it was removed after reading the explicit `mapMon` body, without changing any
source or increasing any resource limit. The reduced consumer passed both sandbox and library checks through the required
`scompile.py` wrapper (2.8 s and 2.9 s), with no errors or warnings. The delivery tool also compiles a
fresh probe for every declaration in the existing binding.

## Second reading by N8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
