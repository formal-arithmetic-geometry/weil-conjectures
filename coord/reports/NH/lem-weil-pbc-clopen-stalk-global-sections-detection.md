## Worker report

The module `lean/Sheaf/EtaleCohomology/ClopenStalkGlobalSectionsDetection.lean`
introduces the clopen-neighbourhood subtype, its associated étale site objects and
restriction arrows, the contravariant diagram of sections, the factorisation of a
geometric point through a clopen, and the canonical global germ map.  The theorem
`AlgebraicGeometry.Scheme.clopenStalkGlobalSectionsDetection` has a `sorry` proof
and states the node verbatim at the level of hypotheses and clauses.

The field `K` is a `Field` and `IsSepClosed`, `C` is a commutative ring with
`Algebra K C`, and `hlocal` is bijectivity of the structural map
`algebraMap K (Localization.AtPrime z.1)` for every prime.  The `hclopen`
hypothesis is the stated clopen basis condition.  `G` is
`Sheaf (Spec (.of C)).smallEtaleTopology AddCommGrpCat.{u + 1}`.  A geometric
point over `z` is represented by `zbar` together with the explicit equality of
its underlying continuous map to the constant map at `z`; this renders “over
`z`” without changing the object or adding a mathematical restriction.

The first conclusion is the canonical isomorphism from
`colimit (clopenSectionDiagram (Spec (.of C)) z G)` to
`(pointSmallEtale zbar).sheafFiber.obj G`, with the component equation for each
clopen `W` given by `toPresheafFiber` and `clopenPointMarking`.  The second conclusion
is `Function.Surjective (geometricGerm zbar G)`.  The third implication renders
`G(E)=0` as `Subsingleton` of the global sections group's carrier and renders each
stalk's vanishing in the same way.  The final conclusion quantifies every sheaf
`F` on `Spec K` and every algebraically closed geometric point `tbar`, asserting
`IsIso (geometricGerm tbar F)`.

The helper declarations use only Mathlib constructions: `Scheme.Opens.toScheme`
and `Opens.ι`, `Scheme.Etale.mk`, `MorphismProperty.Over.homMk`, the opposite
section diagram, and `GrothendieckTopology.Point.toPresheafFiber`.  The functor laws are verified inside the diagram construction using Mathlib's
identity and composition lemmas for inclusions. `clopenPointLift` uses the
open-immersion lifting property; `clopenPointMarking` packages that lift with
Mathlib's factorisation equality. The main theorem is the only theorem declaration
and its proof is `sorry`; all definitions have real data.

Dependency declarations used:

* `IsSepClosed` from `Mathlib.FieldTheory.IsSepClosed` for
  `def-pc-separably-closed`.
* `AlgebraicGeometry.Spec` from `Mathlib.AlgebraicGeometry.Scheme` for
  `def-weil-affine-spectrum`.
* `IsAlgClosed` and `Scheme.SpecToEquivOfField` from Mathlib for
  `def-weil-geometric-point`; the statement uses the explicit map-over-point form.
* `CategoryTheory.Sheaf` and `Scheme.smallEtaleTopology` from
  `Mathlib.CategoryTheory.Sites.Sheaf` and `Mathlib.AlgebraicGeometry.Sites.Etale`
  for `def-weil-pbc-abelian-etale-sheaves`.
* `pointSmallEtale` and `Point.sheafFiber` from
  `Mathlib.AlgebraicGeometry.Sites.EtalePoint` and
  `Mathlib.CategoryTheory.Sites.Point.Basic` for
  `def-weil-pbc-geometric-stalks`.

The proof dependency `lem-weil-pbc-clopen-etale-neighbourhood-cofinality` now has
`AlgebraicGeometry.clopen_etale_neighbourhood_cofinality` in
`Sheaf.AlgebraicGeometry.ClopenEtaleNeighbourhoodCofinality`, imported without
`public`. The other proof dependencies use their recorded Mathlib interfaces:
`Functor.initial_of_exists_of_isCofiltered`, `IsCofiltered.over`,
`IsCofiltered.of_initial`, `Functor.final_op_of_initial`, and
`Functor.Final.colimitIso` from `Mathlib.CategoryTheory.Filtered.Final` and its
imports, and `Etale.instOfIsOpenImmersion`, `Scheme.smallEtaleTopology`, and
`CategoryTheory.Sheaf` from the étale-site imports.  The theorem's
docstring records all four proof steps and the cited source tags.

Edge cases checked: an empty spectrum (all point-indexed clauses are vacuous),
the empty clopen and the whole-spectrum clopens, intersections of clopens,
`C = K` with its one-point spectrum, a separably closed but non-algebraically
closed `K`, arbitrary algebraically closed extensions `Omega`, and zero global
sections.  No nonemptiness of the index category or of the scheme was added.
The index universe is the scheme universe `u`, and no universe equality is imposed.

Searches made:

* `msearch.py ... leanfinder "affine scheme clopen basis geometric etale stalk
  colimit clopen sections global germ surjective"`: only affine-open basis,
  étale-site and germ-injectivity results; no exact declaration.
* `msearch.py ... loogle "pointSmallEtale sheafFiber colimit clopen"`: zero hits
  (`pointSmallEtale` is not a Loogle identifier in isolation).
* `msearch.py ... grep "clopen.*stalk|stalk.*clopen|global.*sections.*stalk"
  AlgebraicGeometry`: no hits.
* `rg -n "clopen.*stalk|stalk.*clopen|global.*stalk|clopenStalkGlobalSectionsDetection"
  WeilConjectures lean/Sheaf`: no declaration of this statement; only unrelated
  global-section/stalk lemmas and prose.
* The DAG search found no existing node declaration for this item.  The recorded
  dependency nodes were opened and their Mathlib matches checked by signature.

No new definition nodes or dependency modules were needed.  No statement correction
or `STATEMENT-DISPUTED` flag was needed.

## Second reading by NH

I reread the node and module together.  The `K`, `C`, localization-isomorphism and
clopen-basis hypotheses are all present.  The sheaf is the abelian-group-valued
small étale sheaf on `Spec C`; geometric points use an algebraically closed field
and the explicit “over `z`” equality.  The clopen colimit uses exactly restriction
maps to smaller neighbourhoods, and the component equation identifies its map with
the canonical germ component.  Surjectivity, the zero-global-sections implication,
and the separate `Spec K` isomorphism clause are all retained.  The source tags and
proof route in the docstring match the node.  `scompile.py` compiled the module
cleanly (the only postponed proof is the theorem's expected `sorry`).

## Saved-packet repair

The initial dry runs rejected the scratch files `Checks.lean` and `Test.lean`;
these have been removed. The first full preflight confirmed compilation but
rejected the three proved helper lemmas and the trailing `:=` in `lean.statement`.
The inclusion identity/composition checks now belong to the functor construction;
the lift factorisation is supplied by Mathlib inside `clopenPointMarking`.
The redundant lemma declarations were removed. Every remaining declaration has
a source/blueprint docstring. The signature record omits its delimiter as the
preflight requires, and the date follows the machine's UTC date.
The saved main statement and all four mathematical conclusions are retained.
