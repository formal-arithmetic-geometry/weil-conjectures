## Worker report

`Sheaf.AlgebraicGeometry.ProEtaleClassicalStalk` states
`AlgebraicGeometry.Scheme.proEtale_classical_stalk` with a single `sorry`.
No definition is introduced and no proof is attempted.
Source read: Stacks `proetale.tex`, the geometric-stalk paragraph preceding
`lemma-classical-point` and that lemma and proof (Tags 0991, 0993).
The current 51-module framework and `coord/pefw-upstream-framework.md` were read;
this classical set/abelian stalk statement uses the existing small pro-etale site,
not the condensed coefficient module-object category.

Hypotheses and clauses, in order:

- A scheme T: `{T : Scheme.{u}}`. A geometric point:
  `{Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)`.
  These are exactly the recorded inline geometric-point encoding.
- Strict localization: `strictHenselizationScheme t`, the spectrum of the
  existing small affine pointed-etale coordinate-ring colimit
  `strictHenselizationRing t`. No arbitrary strict local scheme replaces it.
- Its canonical structural map is `strictHenselizationStructuralMap t`.
  The existential `h : WeaklyEtale (strictHenselizationStructuralMap t)` states
  that this specific map is an object of `T.ProEt`; `@ProEt.mk ... h` constructs
  that object. The existential lift `l` and equation `hl` make it a pointed
  neighbourhood via `StructuredArrow.mk (Over.homMk l hl)`. These are witnesses
  in the conclusion, not extra assumptions on T or t.
- Sheaves of sets: the first `IsIso` is a natural transformation on
  `Sheaf (ProEt.topology T) (Type (u + 1))`.
  It is the transformation `colim.ι` at the opposite of this pointed strict
  localization, precomposed first with restriction to pointed neighbourhoods
  and then with `sheafToPresheaf`. Its component at H is exactly the canonical
  coprojection `H(strictHenselizationScheme t) ⟶ proEtaleGeometricStalk t H`.
- Sheaves of abelian groups: the second `IsIso` is the same canonical
  transformation with target `AddCommGrpCat.{u + 1}`. Thus both categories in
  the node are stated, not merely the fixed-module special case.
- Naturality in H: `IsIso` is asserted for the natural transformations themselves,
  not just for unrelated objectwise isomorphisms. The components and naturality
  are those of `colim.ι` and `Functor.whiskerLeft`.
- Exactness: `PreservesFiniteLimits` and `PreservesFiniteColimits` are both
  asserted for the same abelian stalk functor. Its displayed composite is
  `sheafToPresheaf` followed by precomposition along
  `(proEtaleGeometricNeighbourhoodForget t).op` followed by `colim`.
  Its object value unfolds to the recorded `proEtaleGeometricStalk t H`, and
  its maps are the colimit maps of the restrictions of sheaf morphisms.
- Universes and site: `T.ProEt`/`ProEt.topology T` are the recorded site's
  bounded weakly-etale objects and fpqc topology. The neighbourhood category is
  the recorded `ProEtaleGeometricNeighbourhood t`; it is essentially small in
  `u+1` and the chosen colimits live in that universe, as in the dependency.
  No independent lower universe restricts test schemes or colimits.

Dependency declarations read and used:

- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; geometric points are
  inline, as the node's record specifies. The corresponding interpretation
  `Scheme.SpecToEquivOfField` is in `Mathlib.AlgebraicGeometry.ResidueField`.
- `Sheaf.AlgebraicGeometry.StrictHenselization`:
  `AlgebraicGeometry.Scheme.strictHenselizationRing`,
  `strictHenselizationScheme`, `strictHenselization_properties`.
- `Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`:
  `AlgebraicGeometry.Scheme.strictHenselizationStructuralMap`; the current landed
  dependency record already names this declaration. Its defining existence theorem characterizes the same common
  composite with every affine pointed-neighbourhood leg.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: exposes
  `AlgebraicGeometry.Scheme.ProEt`, `ProEt.topology`, `ProEt.mk`, `ProEt.forget`
  from `Mathlib.AlgebraicGeometry.Sites.Proetale`. The derived-category
  abbreviation in the recorded dependency is not needed for this statement.
- `Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk`:
  `AlgebraicGeometry.Scheme.ProEtaleGeometricNeighbourhood`,
  `proEtaleGeometricNeighbourhoodForget`, `proEtaleGeometricStalkDiagram`,
  `proEtaleGeometricStalk`, and its colimit-existence instance.
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic` and its public site
  imports supply the recorded `CategoryTheory.Sheaf` encoding for sets and
  abelian groups. Cohomology H' is not used: this node only needs the site,
  sheaf and exactness clauses of that broad dependency.
- `CategoryTheory.Functor.whiskeringLeft`, `Functor.whiskerLeft` and
  `CategoryTheory.Limits.colim.ι` state the canonical comparison as a natural
  transformation without defining a second stalk functor. `IsIso` includes
  the inverse of that specific comparison, not an arbitrary equivalence.

All available recorded proof-dependency modules are imported (proof-only imports
are non-public). Mathlib leaves additionally use their recorded source modules:
EpiMono, Sheafification, Etale, WeaklyEtale, Pullback.HasPullback, Scheme and
OpenImmersion. The attached localization/Olivier results come from the existing
`WeilConjectures.Mathlib.RingTheory.Etale.Weakly` and
`WeilConjectures.RingTheory.ProEtale.HenselianLocalRing` imports.
`def-weil-pbc-site-comparison-morphism` has no recorded module to import.
The theorem docstring carries the six proof steps and their node dependencies.

Edge cases checked: the empty scheme admits no geometric point, so the bound
on t handles it without an extra nonemptiness assumption. No characteristic,
Noetherian, separatedness or finiteness assumption occurs. The zero abelian
sheaf and singleton set sheaf are included. Finite-limit and finite-colimit
preservation includes empty finite diagrams (terminal and initial objects).
For T the spectrum of an algebraically closed field this is evaluation at T,
consistent with the Stacks example following 0993: this statement asserts no
conservativity of geometric stalks. Universes match the stalk dependency's
`Type (u+1)` and `AddCommGrpCat.{u+1}` encodings.

Searches for an existing statement:

- `msearch.py ... leanfinder "The proetale geometric stalk is evaluation at the
  strict henselization and is exact"`: eight hits, all etale-locus/standard-etale
  algebra declarations; none states this comparison or exactness.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.ProEt, CategoryTheory.IsIso"`:
  zero hits.
- `msearch.py ... grep "strictHensel.*stalk|stalk.*strictHensel|proEtale.*Stalk"`:
  zero Mathlib hits.
- `rg` of `lean/Sheaf`, the side `lean/WeilConjectures` framework and the pinned
  source for classical stalk/proEtale stalk/strictLocalizationToBase found the
  existing geometric-stalk definition, but no classical comparison theorem.
- `grep -rn "lem-cbc-proetale-classical-stalk"` in pinned `WeilConjectures`:
  zero hits.
- Inspection of the existing project StrictHenselizationStructuralMap module
  found the usable canonical structural map; searches of pinned upstream and
  the side framework found no `strictLocalizationToBase` declaration.

Validation: dependency import/#check probe passed on the server; the theorem
compiled on the server using scompile.py, nice 19, two threads, 60 seconds per
file. Final clean compile and delivery dry-run results are recorded below.
No STATEMENT-DISPUTED and no statement correction.

## Dependency modules

None in this repaired delivery. The landed dependency record now names exactly
`Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap` and
`Scheme.strictHenselizationStructuralMap`, together with its characterizing
`exists_strictHenselizationStructuralMap` theorem. The dependency is consumed
through its published record without a lean-only replacement.

## Returned-delivery repair

Return L on immutable head `3d96f9fd551e`: the dependency's `lean` changed on
newtargets-dag after that delivery's base. I read the current dependency record
and obtained its current server module with `scompile.py --source`. Its definition
and full characterization have the same source, target and canonical compatible
limit composites that this theorem requires. The now-landed NA record is usable.
I removed the stale dependency-node copy from this delivery, so this item cannot
overwrite that record. The item still cites the dependency in `stmt_deps`, imports
its recorded module and uses its canonical map. The Lean theorem and its signature
are unchanged. This is a delivery-content repair, rather than an unchanged rebase.

The second-reading text below is retained as the historical review of the
returned head; its discussion of a dependency-record repair is superseded by
this section. A second reader must review this repaired delivery before pushing.

## Earlier second reading (a previous round; superseded)

Independent second reader: I read the node and its six proof steps, the Stacks
`proetale.tex` geometric-neighbourhood and stalk paragraphs through
`lemma-classical-point` (Tags 0991 and 0993), and the delivered Lean signature.
The source assumes only a scheme and an algebraically closed geometric point;
there is no ambient Noetherian, separatedness, or characteristic hypothesis.

Object/hypothesis/conclusion checklist (each verdict: matches):

- Scheme T: `{T : Scheme.{u}}`; geometric point: `{Ω : Type u} [Field Ω]
  [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)`. This is the dependency node's inline
  encoding, including the actual field-valued morphism, not just its image.
- Strict localization: `strictHenselizationScheme t`. I opened its definition:
  it is `Spec (strictHenselizationRing t)`, the coordinate-ring colimit of a small
  model of all affine pointed etale neighbourhoods. Its diagram, representative
  equivalence and cone signatures agree with the strict-localization node.
- Canonical map and site membership: `strictHenselizationStructuralMap t` and
  the conclusion witness `h : WeaklyEtale (...)`. The existing structural-map
  definition chooses the common composite characterized by
  `exists_strictHenselizationStructuralMap`, not an arbitrary map. `ProEt.mk`
  packages precisely this weakly etale map. I read Mathlib's `Scheme.ProEt`,
  `ProEt.forget`, `ProEt.precoverage` and `ProEt.topology`: these are the bounded
  weakly etale objects and the fpqc pro-etale topology of the dependency node.
- Pointing needed for the canonical comparison: witnesses `l` and `hl` are in
  the conclusion. `Over.homMk l hl` gives the lift in the same structured-arrow
  category as `ProEtaleGeometricNeighbourhood t`. No lift is assumed as input.
- Sets: the first `IsIso` uses `Type (u + 1)`. Its natural transformation is
  `colim.ι` at the opposite of that pointed strict localization, whiskered by
  neighbourhood restriction and `sheafToPresheaf`. I read `colim.ι` and both
  whiskering definitions: its component is exactly the canonical coprojection
  from H evaluated on the strict localization to the recorded stalk colimit.
- Abelian groups: the second `IsIso` repeats that same map in
  `AddCommGrpCat.{u + 1}`; it covers arbitrary abelian sheaves, with no coefficient
  or constructibility restriction.
- Naturality: both comparisons are natural transformations on the entire sheaf
  category; `IsIso` makes these specific transformations invertible. The
  witnesses h, l and hl precede both comparisons, so they are shared for every H.
- Exactness: `PreservesFiniteLimits` and `PreservesFiniteColimits` apply to the
  identical abelian functor. Its objects unfold, via the opened
  `proEtaleGeometricStalkDiagram` and `proEtaleGeometricStalk` definitions, to
  the node's stalk; its maps are the induced colimit maps. Neither preservation
  clause is lost, strengthened to infinite diagrams, or made an assumption.

Dependency repair checked independently: the structural-map dependency copy
changes only `lean`. Its previously recorded upstream module/declaration is
absent from both the pinned source and the read-only framework. The reused
project declaration has the same scheme, point, source, target and compatible
limit-leg characterization as the dependency node and Stacks Tag 03Q9. It is
already present, so no sibling module or new definition node is appropriate.
The sheaf/site dependency's `Sheaf` and the geometric-point dependency's inline
encoding are used directly; neither the unrelated cohomology nor derived-category
part of those broad nodes is substituted for the required notions.

Edge cases: empty T has no such t and is not excluded by an extra assumption;
zero abelian and singleton set sheaves are allowed. Empty finite diagrams are
included in both preservation predicates, hence initial and terminal objects
are covered. There is no degree n or prime parameter. All characteristics are
allowed. The arbitrary universe u and the u+1-valued sheaves/colimits match the
site and stalk dependencies' chosen bound; no smaller independent test universe
is introduced. For T an algebraically closed field's spectrum this says
 evaluation computes the stalk, and does not assert geometric conservativity.

Independent searches with different wording: `msearch.py ... leanfinder
"Evaluation on a strictly henselian localization computes a pro-etale sheaf
stalk"` returned eight etale-locus algebra results, none this statement.
Loogle on `AlgebraicGeometry.Scheme.proEtaleGeometricStalk` reports an unknown
identifier (so that search alone supplies no evidence); the follow-up Loogle
query `CategoryTheory.Limits.colim.ι` returned the canonical natural transformation
and its component formula, inspected above. The Mathlib grep query
`pro[Ee]tale.*[Ss]talk|[Ss]talk.*pro[Ee]tale` returned no hits. Independent `rg`
across Mathlib, pinned `WeilConjectures`, framework `lean/WeilConjectures` and
project `lean/Sheaf`, using pro-etale/stalk, classical-point and
strictLocalizationToBase alternatives, found the existing stalk construction,
ring-locality results and specialized adic/Weil-sheaf stalk references; none is
this general set/abelian comparison. In particular the trace-formula and perfect
complex hits concern Frobenius or finite constructible stalks. No duplicate
statement or new notion was found. The framework note was read.

No mathematical mismatch was found; no Lean or node change was needed in the
second reading. The one theorem has only `sorry`, no definition or proof was
added, and the source/blueprint docstring carries all six proof steps. The node's
`lean.statement` was checked verbatim against the file signature and matches.
Every variable and universe is bound; no local notation, private copy, hollow
definition or extra instance binder occurs. Server `scompile.py` compiled the
only delivered module cleanly (1.6 seconds, nice 19, two threads, 60-second limit),
including required side-only imports in its private overlay.

## Second reading by NR

Independent review of the returned-delivery repair, 2026-10-15. I read the node's
statement and all six proof steps, the delivered module, the current recorded
statement dependencies and their relevant declarations. I read Stacks
`proetale.tex`, section-points, from the definition of pointed neighbourhoods
through lemma-classical-point and its proof (Tags 0991, 0993). The ambient
hypotheses are a scheme and a geometric point; no finiteness or separation
hypothesis is assumed. The source's stalk paragraph states exactness, and the
lemma states strict-local evaluation and functoriality. Its `X_proetale` is the
same base site's typographical variable, not another base scheme.

Node checklist, with the Lean rendering and verdict for each item:

- Scheme T: `{T : Scheme.{u}}`; matches, with arbitrary universe u.
- Geometric point: `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]` and
  `(t : Spec (.of Ω) ⟶ T)`; matches the recorded inline field-valued encoding.
  The actual morphism, not merely its image, is retained.
- Strict localization: `strictHenselizationScheme t`; matches. I opened
  `strictHenselizationNeighbourhoods`, its affine representative inclusion,
  coordinate-ring diagram, small-model diagram, `strictHenselizationRing` and
  `strictHenselizationScheme`: this is the spectrum of the stated affine
  pointed-etale coordinate-ring colimit, not another strict-local object.
- Canonical structural map: `strictHenselizationStructuralMap t`; matches.
  The current dependency records precisely this declaration. I opened its
  definition and `exists_strictHenselizationStructuralMap`: the chosen map is
  characterized by all the representative limit-leg composites. Its choice
  is determined, rather than arbitrary data supplied by the theorem's caller.
- Membership in the small pro-etale site: conclusion witness
  `h : WeaklyEtale (strictHenselizationStructuralMap t)`, packaged by
  `@ProEt.mk T _ ... h`; matches. I opened Mathlib's `ProEt`, `ProEt.mk`,
  `ProEt.forget`, `ProEt.precoverage` and `ProEt.topology`: objects and fpqc
  coverings are those in the dependency node.
- Pointing the site object: conclusion witnesses `l` and `hl` supply the lift
  and its equation over T. `StructuredArrow.mk (Over.homMk l hl)` has exactly
  the type of the recorded `ProEtaleGeometricNeighbourhood t`. These witnesses
  precede all sheaf conclusions, so the same pointing works for every sheaf;
  no additional input hypothesis occurs.
- Set-valued comparison: the first `IsIso`, on `Type (u + 1)` sheaves, is the
  canonical `colim.ι` at the opposite of that pointed object, whiskered by
  neighbourhood restriction and `sheafToPresheaf`. Its component is precisely
  H(L) to the recorded colimit stalk. Matches, including the arrow direction.
- Abelian-valued comparison: the second `IsIso` is the identical construction
  for `AddCommGrpCat.{u + 1}`. Matches all abelian sheaves, with no coefficient
  or constructibility specialization.
- Naturality in H: both `IsIso` assertions concern natural transformations
  on whole sheaf categories. Matches the natural canonical comparison, not
  merely unrelated isomorphisms of each pair of objects.
- Exactness: the two final clauses are `PreservesFiniteLimits` and
  `PreservesFiniteColimits` for the same composite of sheaf inclusion,
  neighbourhood restriction and `colim`. I opened the stalk diagram and stalk
  definitions: this composite gives their object values and induced maps.
  Matches exactly both finite preservation clauses.

Edge cases: the empty scheme has no such geometric point, so is handled by the
binder without a nonemptiness assumption. The zero abelian sheaf and terminal
set sheaf are included. Empty finite diagrams are included in both preservation
predicates. There is no degree or characteristic parameter; every characteristic
is allowed. The site's object universe u+1 and morphism universe u, the bounded
geometric point, and u+1-valued colimits agree with the dependency interfaces;
no equality of distinct site universes or independent smaller bound is imposed.
The example over an algebraically closed field agrees with evaluation at its
spectrum and adds no assertion of conservativity.

Independent searches: msearch LeanFinder with "A sheaf on the pro etale site
evaluated at a strict localization computes its geometric fiber and preserves
cokernels" returned generic site-point fiber functors and their colimit
properties, not this strict-localization comparison. Loogle `"ProEt"` returned
12 site declarations (opened the relevant definitions above), no comparison.
Mathlib grep `pro[Ee]tale.*[Ss]talk|[Ss]talk.*pro[Ee]tale` returned zero hits.
Independent rg of project Sheaf, pinned upstream WeilConjectures, the exact
51-module side framework and Mathlib, using classicalStalk/classical_stalk,
strict/stalk and strictLocalizationToBase alternatives, found the existing
stalk construction and unrelated structural or module stalks, no duplicate
of this theorem. I read `coord/pefw-upstream-framework.md`; its condensed
module-object constructions do not replace this set/abelian assertion.

No mathematical mismatch was found, so I changed neither Lean nor node. There
are no new nodes or dependency modules to audit in this repaired delivery and
no statement_change. The old stale dependency copy remains removed; the current
published canonical-map interface is used directly. The only repair in this
second reading is this required current review section, which was absent
(the earlier review is explicitly superseded). The module has one theorem with
`by sorry`, no new definition, no proof, no unbound binder, no local notation,
and no line over 100 characters. Its source/blueprint docstring carries all six
proof steps. I mechanically compared lean.statement with the complete source
signature: verbatim equal. Server scompile compiled every delivered file cleanly,
including the side-only import overlay, nice 19, two threads, 60 seconds per
file; the main module took 1.5 seconds. No local compiler or build was run.
