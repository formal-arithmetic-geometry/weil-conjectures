## Worker report

Item: `def-sfb-projection-formula`; group Q18; stage 2; 2026-10-16.

The item is exactly the existing structure
`CategoryTheory.Functor.ProjectionFormula` in
`WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`, lines 79–99 of the
published source. Its module is among the 51 upstream framework modules imported
byte-identically into the side project, as documented in
`coord/pefw-upstream-framework.md`. Consequently the record uses `existing: true`,
`branch: slopmaster2` (the required metadata convention for an existing
`WeilConjectures` declaration), and no new module or definition. The source was also read
through `scompile.py --source WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`;
the published declaration agrees with the shared checkout.

The source definition is
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-sfb-transport/def-sfb-projection-formula.md`.
I read that entire source and the current reviewed N3 split. The handoff's obsolete
split is not used: the node copy is the current shared node, changed only in `lean`.
There is no repair note for this item. No statement correction is needed.

Hypotheses and clauses, individually:

- The two monoidal categories are the source's explicit variables
  `{C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]` and
  `{D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]`. All four universes are
  explicitly declared and independent.
- The functor `S : D ⥤ C` and its strong monoidal structure are the parameters
  `(S : D ⥤ C) [S.Monoidal]`. No symmetry, braiding, additivity, adjunction,
  closedness, or exactness is required.
- The inverse structure maps in the node are precisely
  `Functor.OplaxMonoidal.δ S L L'` and `Functor.OplaxMonoidal.η S`.
  Mathlib calls the inverse unit map `η`, whereas the node calls it epsilon.
  `Functor.Monoidal.μIso` and `εIso` have these maps as their inverses.
- The functor `P : C ⥤ D` is the final explicit parameter `(P : C ⥤ D)`.
- The specified family of isomorphisms is the data field
  `iso (L : D) (M : C) : P.obj (S.obj L ⊗ M) ≅ L ⊗ P.obj M`.
  This stores actual isomorphisms, including their inverses; it is not a mere
  assertion of existence, arbitrary comparison map, or choice from a theorem.
- Naturality in L is `natural_left`: for every `f : L ⟶ L'`,
  `P.map (S.map f ▷ M) ≫ (iso L' M).hom = (iso L M).hom ≫ f ▷ P.obj M`.
- Naturality in M is `natural_right`: for every `g : M ⟶ M'`,
  `P.map (S.obj L ◁ g) ≫ (iso L M').hom = (iso L M).hom ≫ L ◁ P.map g`.
- The unit equation is exactly the field `unit (M : C)`:
  `(iso (𝟙_ D) M).hom ≫ (λ_ (P.obj M)).hom =
  P.map (Functor.OplaxMonoidal.η S ▷ M ≫ (λ_ M).hom)`.
  Composition `≫` is in diagram order, so this is the node's displayed equation.
- The associativity equation is exactly the field `assoc (L L' : D) (M : C)`:
  `(iso (L ⊗ L') M).hom ≫ (α_ L L' (P.obj M)).hom =
  P.map (δ S L L' ▷ M ≫ (α_ (S.obj L) (S.obj L') M).hom) ≫
  (iso L (S.obj L' ⊗ M)).hom ≫ L ◁ (iso L' M).hom`.
  Its factors, their order, and the direction of the associator all match the
  blueprint. There are no further fields or coherence assumptions.

Dependency declaration used: `def-sfb-strong-monoidal-functor` is a Mathlib node
with match `CategoryTheory.Functor.CoreMonoidal` in
`Mathlib.CategoryTheory.Monoidal.Functor`. I read its full signature, docstring,
fields and conversions. The recorded interface gives a unit isomorphism and a
natural tensor isomorphism with associativity and both unit coherences.
`CoreMonoidal.toMonoidal` supplies the equivalent `S.Monoidal` interface used by
the existing projection-formula declaration: its oplax maps are definitionally
`εIso.inv` and `μIso.inv`. Conversely `Monoidal.εIso` and `Monoidal.μIso` recover
these isomorphisms from a monoidal instance. Thus using this existing structure
uses the dependency's notion without a private copy or extra hypothesis.

Edge cases checked by reading the types and equations: all objects and morphisms
are quantified, including L equal to the tensor unit, M equal to the tensor unit,
and identity arrows in either naturality condition. The equations remain typed
with these substitutions; the unit equation explicitly covers the unit case.
There is no zero/nonzero or nonempty-object restriction. A monoidal category
already supplies its tensor unit, so an empty category cannot be a missing case.
The formulation applies without any symmetry, including nonbraided monoidal
categories; independent object and morphism universes for C and D are retained.
No existence theorem for projection formulas is claimed.

Searches performed:

- `msearch.py leanfinder`, query "A projection formula for a functor P relative to
  a strong monoidal functor S is a natural isomorphism P(S L tensor M) to L tensor
  P M compatible with unit and associativity"; followed by "Coherent projection
  formula natural isomorphism P(S L tensor M) isomorphic to L tensor P M".
  Returned tensor/module/localization results, no exact definition.
- `msearch.py loogle`, query
  `CategoryTheory.Functor.ProjectionFormula, CategoryTheory.Functor.LeftLinear`:
  zero hits, unknown identifier `CategoryTheory.Functor.ProjectionFormula`.
- `msearch.py grep`, query
  `ProjectionFormula|projectionFormula|projection_formula|class LeftLinear` in
  `CategoryTheory`: one hit, `Functor.LeftLinear` in
  `Mathlib/CategoryTheory/Monoidal/Action/LinearFunctor.lean:156`.
  I read `OplaxLeftLinear` and `LeftLinear`, including their coherence fields.
  They need specified actions, and are not an exact definition for the given S.
- `msearch.py leansearch`, query "Natural coherent projection formula P(S L tensor
  M) isomorphic to L tensor P M for a strong monoidal functor S": eight results,
  including `Functor.Monoidal.μIso`, `commTensorRight`, `ofBifunctor`, and
  `μNatIso`; none is the requested coherent projection-formula structure.
- `rg` in the older slopmaster2 `WeilConjectures` tree for
  `ProjectionFormula|projectionFormula|projection_formula`, and for the exact
  blueprint id: specialized sheaf and scheme formulas, no exact id or structure.
  A targeted declaration search in its CategoryTheory tree likewise found none.
- `rg` of `lean/Sheaf` for projection-formula names: specialized geometric,
  derived, and coproduct statements, no matching general structure.
- `rg` of the shared `lean/WeilConjectures` framework found the exact structure
  at `CategoryTheory/ModuleObjects/ProjectionFormula.lean:82`. Reading its full
  five fields and docstring established the match. This published framework is
  newer than the older source checkout and is the correct existing declaration.
- `rg` of `dag/lean_names_upstream.json` and the DAG records for ProjectionFormula
  names did not supply a competing binding for this item.

Validation: a scratch probe imports the published existing module and checks the
structure, all five fields, and `CoreMonoidal.toMonoidal` using the required
`scompile.py` wrapper. The delivery dry run also checks the existing declaration
and runs the maintainer's stage-2 preflight. No source module is delivered, no
proof or sorry is added, and no independent DAG node is stated.

The first dry run compiled the existing-declaration probe, then requested the
`slopmaster2` branch label for an existing `WeilConjectures` declaration. That
metadata was corrected. Its only other finding was the second-reading section,
which belongs to the next independent reader and is not written by this worker.

## Second reading by Q18

I independently reopened the current node copy, the blueprint source place, the recorded
`def-sfb-strong-monoidal-functor` dependency, the published framework declaration, and the
Mathlib `CoreMonoidal`/`Monoidal` interfaces. The node's objects and clauses render as follows.

- The monoidal categories are Lean's implicit `{C : Type u₁}` and `{D : Type u₂}` with
  independent `[Category.{v₁} C]`, `[MonoidalCategory C]`, `[Category.{v₂} D]`, and
  `[MonoidalCategory D]`; no universe equality or extra category structure is imposed.
- The strong monoidal functor is `(S : D ⥤ C) [S.Monoidal]`. Its inverse tensor and unit
  structure maps are exactly `Functor.OplaxMonoidal.δ S L L'` and
  `Functor.OplaxMonoidal.η S`, matching the node's `δ` and `ε` orientations. The Mathlib
  `Monoidal` class supplies these as inverses of `μ` and `ε`, and the dependency's
  `CoreMonoidal.toMonoidal` gives this same interface.
- The remaining functor is `(P : C ⥤ D)`, with no adjunction, exactness, symmetry,
  additivity, or closedness hypothesis.
- The family `π` is the actual field
  `iso (L : D) (M : C) : P.obj (S.obj L ⊗ M) ≅ L ⊗ P.obj M`, so both directions of each
  isomorphism are present.
- Naturality in `L` is `natural_left`: for `f : L ⟶ L'`,
  `P.map (S.map f ▷ M) ≫ (iso L' M).hom = (iso L M).hom ≫ f ▷ P.obj M`.
- Naturality in `M` is `natural_right`: for `g : M ⟶ M'`,
  `P.map (S.obj L ◁ g) ≫ (iso L M').hom = (iso L M).hom ≫ L ◁ P.map g`.
- Unit compatibility is `unit (M)`, namely
  `(iso (𝟙_ D) M).hom ≫ (λ_ (P.obj M)).hom =
  P.map (Functor.OplaxMonoidal.η S ▷ M ≫ (λ_ M).hom)`, which is the node's
  `λ_{PM} ∘ π_{1,M} = P(λ_M ∘ (ε ⊗ M))` in Lean's diagram-order composition.
- Associativity compatibility is `assoc (L L' M)`, whose left side is
  `(iso (L ⊗ L') M).hom ≫ (α_ L L' (P.obj M)).hom` and whose right side is
  `P.map (δ S L L' ▷ M ≫ (α_ (S.obj L) (S.obj L') M).hom) ≫
  (iso L (S.obj L' ⊗ M)).hom ≫ L ◁ (iso L' M).hom`. This has exactly the node's
  associator direction and factor order.

No mismatch was found, so no Lean or node repair was necessary. The declaration is an
existing exact match at
`WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula`,
`CategoryTheory.Functor.ProjectionFormula`; the node's `lean` record remains
`existing: true`, branch `slopmaster2`. I checked the full declaration rather than only its
name, including all five fields and its surrounding namespace/universe binders.

Edge cases remain covered: `L` and `M` range over all objects (including tensor units),
`f` and `g` range over all morphisms (including identities), and the unit case is explicit.
No zero-object, nonempty-index, characteristic, finiteness, symmetry, or nonbraided-category
restriction is introduced; empty categories are excluded only when the stated monoidal
category structure itself cannot exist. Independent object and morphism universes are
preserved, and the formulation is valid at every tensor-unit substitution.

For duplicate/notion searches I rechecked `rg` in the current `lean/WeilConjectures` framework,
`lean/Sheaf`, the older slopmaster2 `WeilConjectures` tree, Mathlib's monoidal functor files,
and `dag/lean_names_upstream.json`. The current framework has the exact declaration; the
older source and Mathlib have no projection-formula structure. Mathlib's
`Functor.LeftLinear` is only a candidate for specified monoidal actions and is not this
S-relative definition. I also re-read the recorded dependency node and its
`CoreMonoidal` match; it supplies precisely the strong-monoidal interface used here.
The existing-declaration probe was compiled with the required `scompile.py` wrapper and
all checks (`ProjectionFormula`, its five fields, and `CoreMonoidal.toMonoidal`) succeeded.
