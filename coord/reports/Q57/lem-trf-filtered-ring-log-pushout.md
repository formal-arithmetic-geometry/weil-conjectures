## Worker report

The delivery states `RingTheory.filteredRing_logPushout` in
`Sheaf.RingTheory.FilteredRingLogPushout`. It also supplies the quotient class map,
induced quotient maps, their identity/composition statements, the resulting diagram,
and the canonical filtered set-colimit monoid and stage maps. Every theorem proof is
`sorry`; all definitions have concrete data. The three helper theorem statements are
exactly the well-definedness and functor-law clauses of this node's fourth proof step,
not additional mathematical assumptions on the main theorem.

The statement is unchanged. Its statement dependencies gain the already landed
`def-trf-log-regular-pair`, whose public declarations include the required explicit
quotient. No new notion is defined and no dependency record is repaired.

Hypothesis and clause correspondence:

- The small filtered category is `{I : Type u} [SmallCategory I] [IsFiltered I]`.
  `IsFiltered` includes nonemptiness, common targets, and equalization of parallel
  arrows. All coefficient objects and the index lie in the common size universe `u`.
  There is no poset, directed-set, or unique-arrow assumption.
- The commutative unital ring diagram is `B : I ⥤ CommRingCat.{u}`. Its maps are
  bundled unital ring homomorphisms. The ring colimit is
  `(colimit B : CommRingCat.{u})` with maps `colimit.ι B i`; existence is provided by
  Mathlib, without a redundant `HasColimit` hypothesis.
- The arbitrary fixed monoid is `{R : Type u} [CommMonoid R]`. The maps are
  `β : ∀ i, R →* B.obj i`, compatible by `hβ`. The induced map is the parameter
  `βA`, identified with each `b_i ∘ β_i` by `hβA`. Specifying the induced map and
  its defining equalities introduces no additional mathematical restriction.
- `E_i` and `E` are rendered directly by the predicates `IsUnit (β i r)` and
  `IsUnit (βA r)`; no duplicate submonoid definition is needed.
- The first conjunct quantifies over every unit `a` of the ring colimit and gives
  an object `i` and a unit `b` with `Units.map (colimit.ι B i).hom.toMonoidHom b = a`.
- The second conjunct takes two stage units with the same image, and gives a
  common target and arrows making their `Units.map` images equal.
- The third conjunct is the prescribed-starting-stage assertion: for every `i,r`,
  `IsUnit (βA r) ↔ ∃ j, ∃ (_f : i ⟶ j), IsUnit (β j r)`.
- The exact quotient `P_i` is `divisorialChartPushout (β i).mrangeRestrict`, and
  `Q` is `divisorialChartPushout βA.mrangeRestrict`. Their existing congruence
  identifies `(e,1)` with `(1,a)` when `β(e)=a`. Multiplying by `(r,u)` gives
  precisely `(r*e,u) ~ (r,a*u)`; conversely the node's relations with `r=u=1`
  include these generators. Thus both generated congruences agree, including
  for noncancellative monoids. `mrangeRestrict` only changes the codomain to the
  actual range; the defining equality reads `(β.mrangeRestrict e).1 = a.1`.
- `ringUnitPushoutClass β r a` is the existing congruence's `mk' (r,a)`.
  `ringUnitPushoutMap` uses `Con.lift` on the actual pair map
  `(MonoidHom.id R).prodMap (Units.map f.toMonoidHom)`. Its named well-definedness
  theorem says its kernel contains the generated source congruence.
  `ringUnitPushoutDiagram` uses exactly these maps, with the named identity and
  composition clauses. These definitions involve no arbitrary choice of maps.
- `ringUnitPushoutColimit` is exactly `CommMonCat.FilteredColimits.colimit` of
  that diagram. Reading Mathlib's definitions shows that its underlying type is
  the quotient `(D ⋙ forget CommMonCat).ColimitType` (via the definitionally
  identical composite through `MonCat`). This is the explicit set colimit.
  Its commutative-monoid structure is Mathlib's filtered-colimit construction.
  `ringUnitPushoutColimitι` is its explicit cocone stage map. Each such map is a
  bundled monoid homomorphism, so it also sends the unit to the colimit unit.
- The fourth conjunct quantifies over every common stage and both arrows and
  states exactly that multiplication of stage classes is multiplication there.
- The existential `F : ringUnitPushoutColimit B β hβ ≃* Q` is an isomorphism of
  commutative monoids, not a bijection of unrelated sets. Its first clause
  fixes the canonical map on every `[r,u]_i`, using `Units.map b_i u`.
- Its second clause gives `F.symm [r,a] = [[r,b]_i]` for EVERY lift `b` of `a`.
  Consequently it includes independence of the unit representative and stage.
  Since `F.symm` is a function on the actual generated-congruence quotient `Q`,
  it is also independent of all displayed relations and their congruence closure.
- Its last two clauses are the required preservation of the image of `R`
  (pairs `(r,1)`, at every stage) and of every stage unit group (pairs `(1,a)`).
  The `R` classes are stage independent because the diagram maps fix the first
  coordinate and send `1` to `1`, and the index category has common targets.

Dependency declarations read and used:

- `def-weil-size-convention` is a metatheoretic convention with no declaration;
  the explicit universe `u` implements it here.
- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.colimit`, `colimit.ι`,
  `Cocone`, `IsColimit` and `CategoryTheory.IsFiltered`, from Mathlib's
  `CategoryTheory.Limits.HasLimits`, `Limits.Cones`, `Limits.IsLimit`, and
  `CategoryTheory.Filtered.Basic`. These are available through the public imports.
- `def-trf-log-regular-pair`: `AlgebraicGeometry.divisorialChartCongruence` and
  `AlgebraicGeometry.divisorialChartPushout`, from
  `Sheaf.AlgebraicGeometry.LogRegularPair`, read with their complete signatures
  and docstrings. They allow any commutative ring and any commutative monoid;
  the geometric hypotheses of the larger definition are not imposed here.
- Proof dependency `lem-pc-filtered-colimit-commrings-elementwise` has no Lean
  record because its exact Mathlib match is
  `Limits.Concrete.isColimit_exists_rep`, `isColimit_rep_eq_iff_exists` in
  `Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`, together with
  `CommRingCat.FilteredColimits.forget_preservesFilteredColimits` in
  `Mathlib.Algebra.Category.Ring.FilteredColimits`.
- Proof dependency `lem-weil-pbc-filtered-colimit-sets-elementwise` likewise
  matches `Limits.Types.jointly_surjective`,
  `Types.FilteredColimit.isColimit_eq_iff`, and `isColimit_eq_iff'`, from
  `Mathlib.CategoryTheory.Limits.Types.Colimits` and `Types.Filtered`.
  Both proof-dependency interfaces were read, and their modules are imported.
- The existing set-colimit monoid and maps are from
  `Mathlib.Algebra.Category.MonCat.FilteredColimits`; its `M`, `colimit`,
  `colimitCommMonoid`, `colimitCocone` and preservation interfaces were read.

Edge cases checked mathematically before writing:

- The empty category is excluded exactly by the stated nonemptiness axiom;
  one-object constant diagrams and categories with parallel arrows are included.
- Zero rings are allowed throughout. Their unit group is the trivial group,
  and becoming a unit is still witnessed by a finite inverse equation.
- `R` can be trivial, infinitely generated, or noncancellative; no integrality,
  finite presentation, finite generation, or group-completion assumption appears.
- A nonunit can become a unit only at a later stage; the third clause requires
  a refinement from ANY prescribed object, not merely existence of some object.
- Products and equalities allow arbitrary common targets and parallel arrows;
  the proof explicitly uses eventual equalization rather than unique arrows.
- Equality in a quotient is generated-congruence equality, not a claim that a
  single elementary relation witnesses every equality. The inverse is a function
  on that entire quotient.

Searches (2026-10-24):

1. `msearch.py ... leanfinder "Filtered colimits of commutative rings commute
   with quotient monoids R times units identifying (re,u) and (r,beta(e)u)"`
   returned eight generic ring-colimit declarations, including
   `CommRingCat.FilteredColimits.colimitCommRing`, `colimit`, `colimitCoconeIsColimit`
   and the unfiltered colimit quotient multiplication lemma. No matching theorem.
2. `msearch.py ... loogle "Units.map, ConGen, colimit"` reported zero hits and
   unknown identifier `ConGen`; the follow-up query `Units.map` returned the
   actual unit-map declaration and its identity/composition lemmas, twelve hits.
   None states the comparison. This supplied the exact units interface.
3. `msearch.py ... grep "logification|[Uu]nitPushout|[Ll]ogPushout"` returned zero
   Mathlib hits. Source searches by the same patterns and by "unit pushout"
   found the associated-log modules. Reading them led to the existing
   `divisorialChartPushout` in `LogRegularPair.lean`, which is reused here.
4. `rg` of `lean/WeilConjectures` for the item id found no declaration. Searches
   of both `lean/WeilConjectures` and `lean/Sheaf`, Mathlib, and
   `dag/lean_names_upstream.json` for `ringUnitPushout|filteredRing_logPushout`
   found none of the delivery's names. The DAG search for the existing quotient
   found its owning `def-trf-log-regular-pair` and its consumers.
5. `tools/blueprint_refs.py search "fixed-monoid unit pushouts"` returned no
   blueprint statement duplicating this consequence. Stacks source
   `literature/stacks-project/categories.tex`, section-directed-colimits, was
   opened: nonempty filtered categories, eventual equality, and simultaneous
   finite representatives are precisely the input used by the node's proof.

No statement correction or STATEMENT-DISPUTED issue was needed.

## Second reading by Q57

A second pass by this worker read the node alongside the entire file; no second
agent was started, as the dispatch brief forbids that. The maintainer's independent
review remains separate. The pass checked every hypothesis and conjunct against
those listed above. It caught the existing quotient implementation, eliminating
the initially contemplated new definition node, and confirmed that its smaller
set of generators generates the same congruence. It also checked that neither
`βA` nor the unit-pushout maps are arbitrary: `hβA` specifies the induced chart
map, the maps are explicit `Con.lift`s, and the equivalence is prescribed on all
pairs. The inverse clause quantifies over all unit lifts and is already defined
on quotient classes, so neither representative nor relation independence is lost.
The compiler's first pass identified universe metavariables in Mathlib's
`max v u` colimit API and ambiguity of `colimit B` in expected type position.
These were repaired by explicit `.{u,u}` arguments and explicit `CommRingCat.{u}`
annotations, without restricting universes or adding hypotheses.

Validation: `scompile.py Q57 lem-trf-filtered-ring-log-pushout` compiled the
module both as sandbox and at its library module name, with no errors or warnings.
`deliver2.py Q57 lem-trf-filtered-ring-log-pushout --no-push` then printed
`OK (dry run)`: server preflight and per-file compilation both passed.
