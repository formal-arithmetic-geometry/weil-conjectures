## Worker report

The node is already stated by the upstream framework declaration
`CategoryTheory.Adjunction.HasProjectionFormula` in
`WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`; no new module is
needed. The same module supplies the canonical construction
`CategoryTheory.Adjunction.projectionFormulaMap`. The node copy records the existing
class with branch `slopmaster2`. A live `scompile.py` probe checked both declarations.

The ambient hypothesis “$\mathcal C,\mathcal D$ are monoidal categories” is rendered by
Mathlib instances `[Category.{v₁} C] [MonoidalCategory C]` and
`[Category.{v₂} D] [MonoidalCategory D]` in the upstream module. The functors and
adjunction hypothesis are rendered by implicit `P : C ⥤ D`, `S : D ⥤ C`, and
`adj : P ⊣ S` in `namespace CategoryTheory.Adjunction`. The strong monoidal
hypothesis on `S` is the typeclass `[S.Monoidal]`, whose tensorator is
`Functor.LaxMonoidal.μ S`. The dependency’s hom-set bijections are the fields of
`adj.homEquiv`; the unit is `adj.unit`.

For each `L : D` and `M : C`, the displayed source and target are rendered by
`adj.projectionFormulaMap L M :
P.obj (S.obj L ⊗ M) ⟶ L ⊗ P.obj M`. Its definition is the inverse image under
`adj.homEquiv` of
`S.obj L ◁ adj.unit.app M ≫ Functor.LaxMonoidal.μ S L (P.obj M)`, exactly the
composite
`SL ⊗ M → SL ⊗ S(PM) → S(L ⊗ PM)` and the stated adjoint direction. The class
`adj.HasProjectionFormula` has the sole field
`isIso (L : D) (M : C) : IsIso (adj.projectionFormulaMap L M)`, which renders the
final clause that every projection formula map is an isomorphism (and hence has a
two-sided inverse). No additional finiteness, nonemptiness, commutativity,
characteristic, or object hypotheses are introduced.

Dependency declarations used:

* `def-sfb-monoidal-category` is the Mathlib declaration
  `CategoryTheory.MonoidalCategory` in
  `Mathlib.CategoryTheory.Monoidal.Category`.
* `def-sfb-strong-monoidal-functor` is the Mathlib declaration
  `CategoryTheory.Functor.CoreMonoidal` in
  `Mathlib.CategoryTheory.Monoidal.Functor`; the upstream `[S.Monoidal]`
  instance is its strong/monoidal form.
* `lem-weil-pbc-adjunction-of-natural-bijection` is the Mathlib declaration
  `CategoryTheory.Adjunction.mkOfHomEquiv` in
  `Mathlib.CategoryTheory.Adjunction.Basic`; the resulting `Adjunction` exposes
  the required natural hom-set equivalences, unit, and counit.

Edge cases checked: identity adjunctions and identity monoidal functors; arbitrary
objects `L` and `M`; empty categories when typeclass instances exist; zero objects
when present; and no extra characteristic or finiteness assumptions. The universal
quantification in `isIso` includes every object, including zero and unit objects.

Searches made:

* `msearch.py Q24 ... leansearch "adjunction with strong monoidal right adjoint
  projection formula maps are all isomorphisms"`: returned only related reflective
  and monoidal-adjunction results, with no exact predicate.
* `msearch.py Q24 ... loogle "CategoryTheory.Adjunction.HasProjectionFormula,
  CategoryTheory.Adjunction.projectionFormulaMap"`: no hit; the names are not in
  the Mathlib index.
* `msearch.py Q24 ... leanfinder "adjunction projection formula maps P (S L tensor M)
  to L tensor P M isomorphisms"`: returned only unrelated tensor adjunctions and
  module adjunctions.
* `msearch.py Q24 ... grep "HasProjectionFormula|projectionFormulaMap"
  CategoryTheory`: no Mathlib hit.
* `rg -n "HasProjectionFormula|projectionFormulaMap"` in the upstream source found
  the exact declarations in
  `lean/WeilConjectures/CategoryTheory/ModuleObjects/ProjectionFormula.lean`;
  the same names are absent from `lean/Sheaf`.
* A live `scompile.py` probe importing
  `WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula` successfully
  checked `@CategoryTheory.Adjunction.HasProjectionFormula` and
  `@CategoryTheory.Adjunction.projectionFormulaMap`.

No statement dispute, node correction, new node, or dependency module is needed.

## Second reading by Q24

I reread the node statement, the source place
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-sfb-transport/def-sfb-adjunction-has-projection-formula.md`,
and the declaration in
`WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`.

* **Ambient objects and structures.** The node introduces monoidal categories
  `\mathcal C` and `\mathcal D`; the existing declaration's implicit parameters
  `{C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]` and
  `{D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]` render exactly these,
  with independent object and morphism universes. Verdict: holds.
* **Adjunction.** The node introduces `P : C ⥤ D`, `S : D ⥤ C`, an adjunction
  `P ⊣ S`, its unit, and the natural hom-set bijections. The declaration receives
  `adj : P ⊣ S`; Mathlib's `Adjunction` contains the unit and hom equivalences,
  so this is the same bundled data and adds no hypothesis. Verdict: holds.
* **Strong monoidal right adjoint.** The node assumes that `S` is strong monoidal
  with tensorator `\mu^S`. The declaration has `[S.Monoidal]`, whose lax tensorator
  is an isomorphism supplied by the strong `CoreMonoidal` structure. Verdict: holds;
  no symmetry, commutativity, finiteness, or characteristic assumption is added.
* **Projection formula map.** The source map is
  `P.obj (S.obj L ⊗ M) ⟶ L ⊗ P.obj M`, adjoint under `adj.homEquiv` to
  `S.obj L ◁ adj.unit.app M ≫ Functor.LaxMonoidal.μ S L (P.obj M)`.
  This is exactly `adj.projectionFormulaMap L M` in the existing module, with the
  same order and domains for every `L : D` and `M : C`. Verdict: holds.
* **Projection-formula condition.** The node requires every such map to be an
  isomorphism (a two-sided inverse). The class field
  `HasProjectionFormula.isIso (L : D) (M : C) : IsIso (adj.projectionFormulaMap L M)`
  has precisely those quantifiers and conclusion. Verdict: holds.

The empty index set is irrelevant because the condition quantifies over objects;
identity adjunctions and identity monoidal functors typecheck, as do zero and unit
objects whenever the ambient categories have them. Independent universes are
retained. An empty category cannot carry the required tensor unit; this is already
excluded by the source monoidal-category hypothesis. No additional nonemptiness
assumption is introduced.

I searched Mathlib and both the source and project trees with `msearch.py` using
LeanSearch, Loogle, LeanFinder, and `rg`/grep for `HasProjectionFormula` and
`projectionFormulaMap`. Mathlib and the slopmaster2 source have no exact match;
the shared framework has the exact declarations in
`lean/WeilConjectures/CategoryTheory/ModuleObjects/ProjectionFormula.lean`.
The required `scompile.py --source WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`
probe succeeded. The worker's record was otherwise exact. I retained the delivery
checker's required `slopmaster2` branch for this imported `WeilConjectures`
declaration and updated the note to identify it as imported framework material.
I removed the trailing `where` delimiter from `lean.statement`, matching the
preflight signature extraction (the source text before `where`). No mathematical
statement, module, dependency, or source definition required repair.

### Dependency and search details of this reading

I opened all three dependency nodes and their Mathlib signatures: `MonoidalCategory`
(with tensor unit, associator, unitors, pentagon and triangle), `Functor.CoreMonoidal`
(with invertible unit and tensor maps, naturality and coherence), and
`Adjunction.mkOfHomEquiv`/`CoreHomEquiv` (with the natural bijections and the stated
unit/counit). I also read `Functor.Monoidal`, `Monoidal.μIso` and
`CoreMonoidal.toMonoidal`: the source's strong structure is exactly the instance
used by `HasProjectionFormula`, not an extra condition on the adjunction or on P.
The Stacks context at `categories.tex`, Tags 0037, 0FFK and 0FFL, introduces no
additional ambient assumptions. The blueprint definition itself supplies precisely
P, S, their adjunction, its unit and S's strong monoidal structure.

Fresh searches in this reading (recorded in `searches.jsonl`) were:

* LeanFinder: `HasProjectionFormula projectionFormulaMap` — unrelated projection
  notation/data, no general predicate.
* LeanSearch: `Invertibility of the adjunction mate of a monoidal tensorator and
  unit for all pairs of objects` — reflective-monoidal, unit and duality lemmas,
  no exact definition.
* Loogle: `CategoryTheory.frobeniusMorphism` — a cartesian-monoidal specialization.
  I read `Mathlib.CategoryTheory.Monoidal.Closed.Functor`, lines 43–62, and verified
  its cartesian assumptions do not cover the present arbitrary monoidal categories.
* grep/rg: `projectionFormulaMap|frobeniusMorphism|HasProjectionFormula` in Mathlib,
  the slopmaster2 source, `lean/Sheaf`, and the shared framework — the sole exact
  categorical construction and predicate are the existing framework declarations
  being attached. The geometric predicates are different notions.

No new definition node or dependency module is included. Because this is an exact
existing attachment, upstream docstrings are read and reused; no new declaration
or proof (including no new `sorry`) is delivered. The class is actual Prop data
with its all-objects `IsIso` field, and the map has a real `homEquiv.symm`
construction, so neither definition is hollow.

## Earlier second reading (a previous round; superseded)

I reread the current node, all three dependency records, and the complete upstream
module. The adjunction orientation is `P : C ⥤ D`, `S : D ⥤ C`, exactly as in the
node. The map has domain `P.obj (S.obj L ⊗ M)` and codomain `L ⊗ P.obj M`; its
hom-equivalence image is precisely the unit followed by the monoidal tensorator.
The class field quantifies over all `L` and `M` and asks precisely for `IsIso`, so
all hypotheses and both conclusion clauses match. No mismatch was found and no
change beyond the node's `lean` record was made.
